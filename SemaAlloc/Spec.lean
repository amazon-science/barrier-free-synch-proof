abbrev EngineId := Nat   -- hardware execution engine (e.g., DMA, compute, vector)
abbrev ScopeId := Nat    -- unique identifier for a loop or conditional loop in the AST
abbrev DataPathInstrId := Nat    -- unique identifier for a block instruction

-- pointwise function update: f[a ↦ b]
def funUpdate [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

-- structured program AST: blocks contain per-engine instruction lists
inductive Stmt where
  | block : (EngineId → List DataPathInstrId) → Stmt    -- instruction block (per-engine instruction lists)
  | loop : ScopeId → List Stmt → Stmt            -- loop with body
  | cond : ScopeId → ScopeId → List Stmt → List Stmt → Stmt  -- conditional with then/else loop IDs and bodies

opaque DataPathState : Type    -- abstract datapath/memory state modified by instructions
opaque ControlState : Type   -- abstract control state queried by loop/cond guards

structure ProgramBase where
  engines : List EngineId                            -- list of engine IDs in the system
  instrOp : DataPathInstrId → DataPathState → DataPathState      -- datapath effect of executing an instruction
  guard : EngineId → ScopeId → ControlState → Bool              -- per-engine loop/cond guard
  controlOp : EngineId → ScopeId → ControlState → ControlState  -- per-engine control state update on loop entry

-- lifecycle phase of an in-flight instruction
inductive Phase where
  | issued     -- dispatched but not yet committed
  | committed   -- datapath effect applied, waiting to retire

-- what kind of loop a stack frame belongs to
inductive FrameKind where
  | top                    -- top level of the program (no enclosing loop)
  | loop : ScopeId → FrameKind  -- loop frame
  | cond : ScopeId → FrameKind  -- conditional loop frame

-- a stack frame: body of statements, current statement index, and loop kind
structure Frame where
  body : List Stmt
  stmtIdx : Nat
  kind : FrameKind

-- program counter: call stack of frames + current instruction index within the active block
structure PC where
  stack : List Frame
  instrIdx : Nat

-- Structural helpers

-- Which engine owns `instr` in block `f`? Linear scan over engine list.
-- Used by `instrEngine`. Even though this func chooses the first engine it
-- finds, `UniqueInstrIds` guarantees this is always the *only* engine
def findInBlock (engines : List EngineId) (f : EngineId → List DataPathInstrId) (instr : DataPathInstrId) : Option EngineId :=
  match engines with
  | [] => none
  | e :: es => if instr ∈ f e then some e else findInBlock es f instr

-- Which engine owns `instr` anywhere in the AST? Recurses into loops.
def instrEngine (engines : List EngineId) (body : List Stmt) (instr : DataPathInstrId) : Option EngineId :=
  match body with
  | [] => none
  | h :: t =>
    let here := match h with
      | .block f => findInBlock engines f instr
      | .loop _ body' => instrEngine engines body' instr
      | .cond _ _ body' body'' =>
        match instrEngine engines body' instr with
        | some e => some e
        | none => instrEngine engines body'' instr
    match here with
    | some e => some e
    | none => instrEngine engines t instr

-- Body of the loop with the given ID, or none if not found.
def scopeBodyOf : List Stmt → ScopeId → Option (List Stmt)
  | [], _ => none
  | (Stmt.loop lid body) :: rest, target =>
      if lid = target then some body
      else (scopeBodyOf body target).orElse (fun _ => scopeBodyOf rest target)
  | (Stmt.cond thenId elseId t f) :: rest, target =>
      if thenId = target then some t
      else if elseId = target then some f
      else (scopeBodyOf t target).orElse (fun _ =>
            (scopeBodyOf f target).orElse (fun _ =>
            scopeBodyOf rest target))
  | _ :: rest, target => scopeBodyOf rest target

-- Immediate parent loop of `target` in the loop tree.
-- Returns `none` if `target` is a direct child of the top-level program body.
-- Structure mirrors innermostParentScope: recurse into the body, and when `target`
-- is found as a direct child (lid = target), return the enclosing loop.
-- The helper `go` tracks the current enclosing loop as `container`.
def scopeParent (body : List Stmt) (target : ScopeId) : Option ScopeId :=
  go body target none
where
  go : List Stmt → ScopeId → Option ScopeId → Option ScopeId
  | [], _, _ => none
  | (Stmt.loop lid lb) :: rest, target, container =>
      if lid = target then container
      else match go lb target (some lid) with
        | some p => some p
        | none => go rest target container
  | (Stmt.cond thenId elseId tb eb) :: rest, target, container =>
      if thenId = target then container
      else if elseId = target then container
      else match go tb target (some thenId) with
        | some p => some p
        | none => match go eb target (some elseId) with
          | some p => some p
          | none => go rest target container
  | _ :: rest, target, container => go rest target container

-- Is `instr` contained anywhere in `body`? (deep, through loops)
def instrInBody (engines : List EngineId) (body : List Stmt) (instr : DataPathInstrId) : Bool :=
  match body with
  | [] => false
  | h :: t =>
    let here := match h with
      | .block f => (findInBlock engines f instr).isSome
      | .loop _ body' => instrInBody engines body' instr
      | .cond _ _ body' body'' => instrInBody engines body' instr || instrInBody engines body'' instr
    here || instrInBody engines t instr

-- Tightest loop directly containing `instr`, or none if at top level.
def innermostParentScope (engines : List EngineId) (body : List Stmt) (instr : DataPathInstrId) : Option ScopeId :=
  match body with
  | [] => none
  | h :: t =>
    let here := match h with
      | .block _ => none
      | .loop lid body' =>
        if instrInBody engines body' instr then
          match innermostParentScope engines body' instr with
          | some inner => some inner
          | none => some lid
        else none
      | .cond thenId elseId body' body'' =>
        if instrInBody engines body' instr then
          match innermostParentScope engines body' instr with
          | some inner => some inner
          | none => some thenId
        else if instrInBody engines body'' instr then
          match innermostParentScope engines body'' instr with
          | some inner => some inner
          | none => some elseId
        else none
    match here with
    | some sid => some sid
    | none => innermostParentScope engines t instr

-- Is `instr` a direct child of `loop`? (not nested deeper)
def directInBody (engines : List EngineId) (body : List Stmt) (loop : ScopeId) (instr : DataPathInstrId) : Bool :=
  match body with
  | [] => false
  | h :: t =>
    let here := match h with
      | .block _ => false
      | .loop lid body' =>
        if lid == loop then
          body'.any fun s => match s with
            | .block f => (findInBlock engines f instr).isSome
            | _ => false
        else
          directInBody engines body' loop instr
      | .cond thenId elseId body' body'' =>
        if thenId == loop then
          body'.any fun s => match s with
            | .block f => (findInBlock engines f instr).isSome
            | _ => false
        else if elseId == loop then
          body''.any fun s => match s with
            | .block f => (findInBlock engines f instr).isSome
            | _ => false
        else
          directInBody engines body' loop instr || directInBody engines body'' loop instr
    here || directInBody engines t loop instr

-- Statement index of an instruction or loop within `body` (0-indexed, top-level only).
def findIndex (engines : List EngineId) (body : List Stmt) (elem : DataPathInstrId ⊕ ScopeId) : Option Nat :=
  go body elem 0
where
  go (body : List Stmt) (elem : DataPathInstrId ⊕ ScopeId) (idx : Nat) : Option Nat :=
    match body with
    | [] => none
    | s :: rest =>
      let found := match elem, s with
        | .inl instr, .block f => (findInBlock engines f instr).isSome
        | .inr sid, .loop lid _ => sid == lid
        | .inr sid, .cond thenId elseId _ _ => sid == thenId || sid == elseId
        | .inl instr, .loop _ body' => instrInBody engines body' instr
        | .inl instr, .cond _ _ b1 b2 =>
          instrInBody engines b1 instr || instrInBody engines b2 instr
        | _, _ => false
      if found then some idx else go rest elem (idx + 1)

-- Like scopeBodyOf but returns [] instead of none when not found.
def findLoopBody (body : List Stmt) (sid : ScopeId) : List Stmt :=
    match body with
    | [] => []
    | h :: t =>
      match h with
      | .loop lid body' =>
        if sid == lid then body'
        else match findLoopBody body' sid with
          | [] => findLoopBody t sid
          | result => result
      | .cond thenId elseId b1 b2 =>
        if sid == thenId then b1
        else if sid == elseId then b2
        else match findLoopBody b1 sid with
          | [] => match findLoopBody b2 sid with
            | [] => findLoopBody t sid
            | result => result
          | result => result
      | _ => findLoopBody t sid

-- Does `rep1` appear before `rep2` in the body of `loop`?
def precedesIn (engines : List EngineId) (body : List Stmt) (loop : Option ScopeId)
    (rep1 rep2 : DataPathInstrId ⊕ ScopeId) : Bool :=
  let loopBody := match loop with
    | none => body
    | some sid => findLoopBody body sid
  match findIndex engines loopBody rep1, findIndex engines loopBody rep2 with
  | some i, some j => i < j
  | _, _ => false

-- Tightest loop containing both `i1` and `i2`, or none if only shared at top level.
def innermostSharedScope (engines : List EngineId) (body : List Stmt) (i1 i2 : DataPathInstrId) : Option ScopeId :=
  match body with
  | [] => none
  | h :: t =>
    let here := match h with
      | .block _ => none
      | .loop lid body' =>
        if instrInBody engines body' i1 && instrInBody engines body' i2 then
          match innermostSharedScope engines body' i1 i2 with
          | some inner => some inner
          | none => some lid
        else none
      | .cond thenId elseId body' body'' =>
        if instrInBody engines body' i1 && instrInBody engines body' i2 then
          match innermostSharedScope engines body' i1 i2 with
          | some inner => some inner
          | none => some thenId
        else if instrInBody engines body'' i1 && instrInBody engines body'' i2 then
          match innermostSharedScope engines body'' i1 i2 with
          | some inner => some inner
          | none => some elseId
        else none
    match here with
    | some sid => some sid
    | none => innermostSharedScope engines t i1 i2

-- Do i1 and i2 commit on the same engine?
def sameEngine (engines : List EngineId) (body : List Stmt) (i1 i2 : DataPathInstrId) : Prop :=
  match instrEngine engines body i1, instrEngine engines body i2 with
  | some e1, some e2 => e1 = e2
  | _, _ => False

-- Producer's statement appears before consumer's in the shared loop body.
def forwardDep (engines : List EngineId) (body : List Stmt) (producer consumer : DataPathInstrId) : Prop :=
  let loop := innermostSharedScope engines body producer consumer
  let loopBody := match loop with
    | none => body
    | some sid => (scopeBodyOf body sid).getD []
  ∃ si sj : Nat, si < sj ∧
    (∃ s, loopBody[si]? = some s ∧ instrInBody engines [s] producer = true) ∧
    (∃ s, loopBody[sj]? = some s ∧ instrInBody engines [s] consumer = true)

-- Consumer's statement appears before producer's in the shared loop body.
def backwardDep (engines : List EngineId) (body : List Stmt) (producer consumer : DataPathInstrId) : Prop :=
  let loop := innermostSharedScope engines body producer consumer
  let loopBody := match loop with
    | none => body
    | some sid => (scopeBodyOf body sid).getD []
  ∃ si sj : Nat, si < sj ∧
    (∃ s, loopBody[si]? = some s ∧ instrInBody engines [s] consumer = true) ∧
    (∃ s, loopBody[sj]? = some s ∧ instrInBody engines [s] producer = true)

-- The shared loop is the producer's immediate parent (producer is "deeper").
def producerIsParent (engines : List EngineId) (body : List Stmt) (producer consumer : DataPathInstrId) : Prop :=
  innermostSharedScope engines body producer consumer = innermostParentScope engines body producer

-- The shared loop is the consumer's immediate parent (consumer is "deeper").
def consumerIsParent (engines : List EngineId) (body : List Stmt) (producer consumer : DataPathInstrId) : Prop :=
  innermostSharedScope engines body producer consumer = innermostParentScope engines body consumer

-- Neither producer nor consumer is deeper than the other in the loop tree.
def siblings (engines : List EngineId) (body : List Stmt) (producer consumer : DataPathInstrId) : Prop :=
  ¬ producerIsParent engines body producer consumer ∧
  ¬ consumerIsParent engines body producer consumer

-- A dependency edge: consumer waits for producer's (totalEntries - offset)-th retirement.
inductive Dep where
  | none                                   -- no dependency
  | dep (producer : DataPathInstrId) (offset : Nat) -- wait for producer, skipping `offset` iterations

-- Complete specification program: AST + dependency graph.
structure Program extends ProgramBase where
  body : List Stmt             -- top-level statement list (the program AST)
  depGraph : DataPathInstrId → Dep     -- dependency for each instruction

theorem findInBlock_mem_engines {engines : List EngineId} {f : EngineId → List DataPathInstrId} {instr : DataPathInstrId} {e : EngineId}
    (h : findInBlock engines f instr = some e) : e ∈ engines := by
  induction engines with
  | nil => simp [findInBlock] at h
  | cons a as ih =>
    simp only [findInBlock] at h
    split at h
    · obtain rfl := Option.some.inj h; exact List.Mem.head _
    · exact List.Mem.tail _ (ih h)

theorem instrEngine_mem_engines {engines : List EngineId} :
    ∀ {body : List Stmt} {instr : DataPathInstrId} {e : EngineId},
    instrEngine engines body instr = some e → e ∈ engines
  | [], _, _, h => by simp [instrEngine] at h
  | .block f :: rest, instr, e, h => by
    simp only [instrEngine] at h
    cases hFB : findInBlock engines f instr with
    | some e' => simp [hFB] at h; subst h; exact findInBlock_mem_engines hFB
    | none => simp [hFB] at h; exact instrEngine_mem_engines h
  | .loop _ body' :: rest, instr, e, h => by
    simp only [instrEngine] at h
    cases hIE : instrEngine engines body' instr with
    | some e' => simp [hIE] at h; subst h; exact instrEngine_mem_engines hIE
    | none => simp [hIE] at h; exact instrEngine_mem_engines h
  | .cond _ _ body' body'' :: rest, instr, e, h => by
    simp only [instrEngine] at h
    cases hIE1 : instrEngine engines body' instr with
    | some e' => simp [hIE1] at h; subst h; exact instrEngine_mem_engines hIE1
    | none =>
      simp [hIE1] at h
      cases hIE2 : instrEngine engines body'' instr with
      | some e' => simp [hIE2] at h; subst h; exact instrEngine_mem_engines hIE2
      | none => simp [hIE2] at h; exact instrEngine_mem_engines h

-- Runtime state of the specification machine.
structure SpecState where
  controlState : EngineId → ControlState     -- per-engine control state (for loop/cond guards)
  dataPathState : DataPathState                  -- shared datapath/memory state
  pc : EngineId → PC                         -- per-engine program counter (call stack + instrIdx)
  inflight : EngineId → List (DataPathInstrId × Phase) -- per-engine in-flight instruction queue (FIFO)
  rc : DataPathInstrId → Nat                -- how many times each instruction has retired
  -- scopeEntryHistory e innerLoop outerLoop k =
  --   times innerLoop entered during iteration k of outerLoop, as seen by e.
  --   outerLoop = none means "relative to the top level" (used for total entry counts).
  --   Updated at loopEnter, condTrue, condFalse.
  scopeEntryHistory : EngineId → ScopeId → Option ScopeId → Nat → Nat

-- Retirement count abstraction. Currently ss.rc; will become
-- totalRetires from retireHistory when we migrate to per-iteration tracking.
abbrev rc (ss : SpecState) (i : DataPathInstrId) : Nat := ss.rc i

-- The spec state after a retire step. Abstracts the exact fields modified.
-- When rc → retireHistory, only this definition changes.
@[reducible] def specRetireUpdate (ss : SpecState) (e : EngineId) (instr : DataPathInstrId)
    (rest : List (DataPathInstrId × Phase)) : SpecState :=
  { ss with inflight := funUpdate ss.inflight e rest,
            rc := funUpdate ss.rc instr (ss.rc instr + 1) }

-- Total entries of loop sid on engine e. Stored at (none, 1) in scopeEntryHistory.
def totalEntries (s : SpecState) (e : EngineId) (sid : ScopeId) : Nat :=
  s.scopeEntryHistory e sid none 1

-- Total entries for an optional loop. For none (top level), always 1.
def totalEntriesOpt (s : SpecState) (e : EngineId) (loop : Option ScopeId) : Nat :=
  match loop with
  | some sid => totalEntries s e sid
  | none => 1

-- Cumulative executions: sum of history entries k = 1..n (1-indexed, inclusive)
def cumExecs (s : SpecState) (e : EngineId) (producerLoop : ScopeId)
    (outerLoop : Option ScopeId) (n : Nat) : Nat :=
  (List.range n).foldl (fun acc k => acc + s.scopeEntryHistory e producerLoop outerLoop (k + 1)) 0

-- Extract enclosing loop ids from a stack
def enclosingLoopsFromStack : List Frame → List ScopeId
  | [] => []
  | f :: rest => match f.kind with
    | .loop sid => sid :: enclosingLoopsFromStack rest
    | .cond sid => sid :: enclosingLoopsFromStack rest
    | _ => enclosingLoopsFromStack rest

-- Update scopeEntryHistory when innerLoop enters on engine e. 1-indexed.
-- Increments (none, 1) for total count.
-- Self (innerLoop): writes at totalEntries(innerLoop) + 1 (the new iteration number).
-- Enclosing loops: writes at totalEntries(outer) (the current iteration of outer).
def incrScopeEntryHistory (s : SpecState) (e : EngineId) (innerLoop : ScopeId)
    (enclosingLoops : List ScopeId) : EngineId → ScopeId → Option ScopeId → Nat → Nat :=
  fun e' il ol k =>
    if e' = e ∧ il = innerLoop then
      if (ol = none ∧ k = 1) ∨
         (ol = some innerLoop ∧ k = totalEntries s e innerLoop + 1) ∨
         (enclosingLoops.any (fun outer => ol = some outer ∧ k = totalEntries s e outer))
      then s.scopeEntryHistory e' il ol k + 1
      else s.scopeEntryHistory e' il ol k
    else s.scopeEntryHistory e' il ol k

-- Loopd entries: times sid was entered during the current iteration of its parent loop.
-- This is the paper's T̂(e, sid). Resets to 0 when the parent loop is re-entered.
-- When sid is at the top level (scopeParent = none), equals totalEntries.
def tripEntries (s : SpecState) (e : EngineId) (body : List Stmt) (sid : ScopeId) : Nat :=
  match scopeParent body sid with
  | some parent => s.scopeEntryHistory e sid (some parent) (totalEntries s e parent)
  | none => totalEntries s e sid


-- Dependency satisfaction check.
-- Disjunction: vacuous pre-check OR main cumulative check.
-- The vacuous pre-check catches the "bleeding" case where the shared loop hasn't
-- been entered enough times in the current parent iteration for the offset to apply.
def depSatisfied (prog : Program) (dep : Dep) (consumer : DataPathInstrId)
    (s : SpecState) (e : EngineId) : Bool :=
  match dep with
  | .none => true
  | .dep producer offset =>
    let sharedLoop := innermostSharedScope prog.engines prog.body producer consumer
    let producerLoop := innermostParentScope prog.engines prog.body producer
    let vacuous := match sharedLoop with
      | some sid => tripEntries s e prog.body sid ≤ offset
      | none => 1 ≤ offset  -- the implicit top-level loop runs once
    vacuous || match producerLoop with
      | none => s.rc producer ≥ totalEntriesOpt s e sharedLoop - offset
      | some plid =>
        s.rc producer ≥ cumExecs s e plid sharedLoop (totalEntriesOpt s e sharedLoop - offset)

-- Spec transition relation: one step on one engine.
inductive SpecStep (prog : Program) :
    EngineId → SpecState → SpecState → Prop where

  -- issue: dispatch next instruction if dependencies are satisfied.
  | issue (e : EngineId) (s : SpecState) (hEngines : e ∈ prog.engines)
      (frame : Frame) (rest : List Frame)
      (f : EngineId → List DataPathInstrId) (instr : DataPathInstrId)
      (hStack : (s.pc e).stack = frame :: rest)
      (hStmt : frame.body[frame.stmtIdx]? = some (Stmt.block f))
      (hInstr : (f e)[(s.pc e).instrIdx]? = some instr)
      (hDeps : depSatisfied prog (prog.depGraph instr) instr s e = true)
      : SpecStep prog e s
          { s with
            pc := funUpdate s.pc e
              { (s.pc e) with instrIdx := (s.pc e).instrIdx + 1 }
            inflight := funUpdate s.inflight e
              (s.inflight e ++ [(instr, Phase.issued)]) }

  -- commit: apply datapath effect of an issued instruction (out-of-order within engine).
  | commit (e : EngineId) (s : SpecState) (hEngines : e ∈ prog.engines)
      (idx : Nat) (instr : DataPathInstrId)
      (hIdx : (s.inflight e)[idx]? = some (instr, Phase.issued))
      : SpecStep prog e s
          { s with
            dataPathState := prog.instrOp instr s.dataPathState
            inflight := funUpdate s.inflight e
              ((s.inflight e).set idx (instr, Phase.committed)) }

  -- retire: pop head of inflight queue (must be committed), increment rc.
  | retire (e : EngineId) (s : SpecState) (hEngines : e ∈ prog.engines)
      (instr : DataPathInstrId) (rest : List (DataPathInstrId × Phase))
      (hHead : s.inflight e = (instr, Phase.committed) :: rest)
      : SpecStep prog e s (specRetireUpdate s e instr rest)

  -- condTrue: guard true, push then-branch frame, update history.
  | condTrue (e : EngineId) (s : SpecState) (hEngines : e ∈ prog.engines)
      (frame : Frame) (rest : List Frame)
      (thenId elseId : ScopeId) (thenBody elseBody : List Stmt)
      (hStack : (s.pc e).stack = frame :: rest)
      (hStmt : frame.body[frame.stmtIdx]? = some (Stmt.cond thenId elseId thenBody elseBody))
      (hGuard : prog.guard e thenId (s.controlState e) = true)
      : SpecStep prog e s
          { s with
            pc := funUpdate s.pc e
              { stack := ⟨thenBody, 0, .cond thenId⟩ :: frame :: rest, instrIdx := 0 }
            controlState := funUpdate s.controlState e
              (prog.controlOp e thenId (s.controlState e))
            scopeEntryHistory := incrScopeEntryHistory s e thenId
              (enclosingLoopsFromStack (frame :: rest)) }

  -- condFalse: guard false, push else-branch frame, update history.
  | condFalse (e : EngineId) (s : SpecState) (hEngines : e ∈ prog.engines)
      (frame : Frame) (rest : List Frame)
      (thenId elseId : ScopeId) (thenBody elseBody : List Stmt)
      (hStack : (s.pc e).stack = frame :: rest)
      (hStmt : frame.body[frame.stmtIdx]? = some (Stmt.cond thenId elseId thenBody elseBody))
      (hGuard : prog.guard e thenId (s.controlState e) = false)
      : SpecStep prog e s
          { s with
            pc := funUpdate s.pc e
              { stack := ⟨elseBody, 0, .cond elseId⟩ :: frame :: rest, instrIdx := 0 }
            controlState := funUpdate s.controlState e
              (prog.controlOp e elseId (s.controlState e))
            scopeEntryHistory := incrScopeEntryHistory s e elseId
              (enclosingLoopsFromStack (frame :: rest)) }

  -- loopEnter: guard true, push frame, update history.
  -- History update here creates a phase mismatch with impl's stmtRegOp (prepended regOp).
  -- Handled the same way as the old loopIterIncrement ↔ stmtRegOp pattern.
  | loopEnter (e : EngineId) (s : SpecState) (hEngines : e ∈ prog.engines)
      (frame : Frame) (rest : List Frame)
      (lid : ScopeId) (loopBody : List Stmt)
      (hStack : (s.pc e).stack = frame :: rest)
      (hStmt : frame.body[frame.stmtIdx]? = some (Stmt.loop lid loopBody))
      (hGuard : prog.guard e lid (s.controlState e) = true)
      : SpecStep prog e s
          { s with
            pc := funUpdate s.pc e
              { stack := ⟨loopBody, 0, .loop lid⟩ :: frame :: rest, instrIdx := 0 }
            controlState := funUpdate s.controlState e
              (prog.controlOp e lid (s.controlState e))
            scopeEntryHistory := incrScopeEntryHistory s e lid
              (enclosingLoopsFromStack (frame :: rest)) }

  -- loopSkip: guard false, advance past loop. Handles both "never enter" and "exit after iterations."
  | loopSkip (e : EngineId) (s : SpecState) (hEngines : e ∈ prog.engines)
      (frame : Frame) (rest : List Frame)
      (lid : ScopeId) (loopBody : List Stmt)
      (hStack : (s.pc e).stack = frame :: rest)
      (hStmt : frame.body[frame.stmtIdx]? = some (Stmt.loop lid loopBody))
      (hGuard : prog.guard e lid (s.controlState e) = false)
      : SpecStep prog e s
          { s with
            pc := funUpdate s.pc e
              { stack := ⟨frame.body, frame.stmtIdx + 1, frame.kind⟩ :: rest, instrIdx := 0 } }

  -- loopBack: unconditional, pop frame. Parent stmtIdx still at loop stmt.
  -- Next step: loopEnter (guard true) or loopSkip (guard false).
  -- No controlOp here — controlOp only fires on loop entry (loopEnter).
  | loopBack (e : EngineId) (s : SpecState) (hEngines : e ∈ prog.engines)
      (frame parent : Frame) (rest : List Frame)
      (lid : ScopeId)
      (hStack : (s.pc e).stack = frame :: parent :: rest)
      (hKind : frame.kind = .loop lid)
      (hEnd : frame.stmtIdx = frame.body.length)
      : SpecStep prog e s
          { s with
            pc := funUpdate s.pc e
              { stack := parent :: rest, instrIdx := 0 } }

  -- condDone: finished all statements in cond branch, pop frame and advance parent.
  | condDone (e : EngineId) (s : SpecState) (hEngines : e ∈ prog.engines)
      (frame parent : Frame) (rest : List Frame)
      (sid : ScopeId)
      (hStack : (s.pc e).stack = frame :: parent :: rest)
      (hKind : frame.kind = .cond sid)
      (hEnd : frame.stmtIdx = frame.body.length)
      : SpecStep prog e s
          { s with
            pc := funUpdate s.pc e
              { stack := ⟨parent.body, parent.stmtIdx + 1, parent.kind⟩ :: rest, instrIdx := 0 } }

  -- blockDone: all instructions in block issued, advance to next statement.
  | blockDone (e : EngineId) (s : SpecState) (hEngines : e ∈ prog.engines)
      (frame : Frame) (rest : List Frame)
      (f : EngineId → List DataPathInstrId)
      (hStack : (s.pc e).stack = frame :: rest)
      (hStmt : frame.body[frame.stmtIdx]? = some (Stmt.block f))
      (hDone : (s.pc e).instrIdx = (f e).length)
      : SpecStep prog e s
          { s with
            pc := funUpdate s.pc e
              { stack := ⟨frame.body, frame.stmtIdx + 1, frame.kind⟩ :: rest, instrIdx := 0 } }

theorem SpecStep.mem_engines {prog : Program} {e : EngineId} {ss ss' : SpecState}
    (h : SpecStep prog e ss ss') : e ∈ prog.engines := by
  cases h <;> assumption

-- Reflexive transitive closure of SpecStep (multi-step execution).
inductive SpecStar (spec : Program) : SpecState → SpecState → Prop where
  | refl : SpecStar spec s s
  | step : (∃ e, SpecStep spec e s s') → SpecStar spec s' s'' → SpecStar spec s s''

theorem SpecStar.trans {spec : Program} {s₁ s₂ s₃ : SpecState}
    (h₁ : SpecStar spec s₁ s₂) (h₂ : SpecStar spec s₂ s₃) : SpecStar spec s₁ s₃ := by
  induction h₁ with | refl => exact h₂ | step hStep _ ih => exact .step hStep (ih h₂)
