import SemaAlloc.Spec

abbrev RegId := Nat    -- register identifier in the impl's register file
abbrev SemaId := Nat   -- semaphore identifier in the impl's semaphore bank

-- ALU operation applied to (dst, src) register pair.
inductive RegOpKind where
  | id                             -- dst := src
  | const : Nat → RegOpKind    -- dst := n (ignore src)
  | subConst : Nat → RegOpKind -- dst := src - k (Nat subtraction, floors at 0)
  | addConst : Nat → RegOpKind -- dst := src + k
  | mulConst : Nat → RegOpKind -- dst := src * k
  | isGT : Nat → RegOpKind    -- dst := if src > n then 1 else 0
  | addSrc : RegOpKind         -- dst := dst + src (two-register addition)
  | subSrc : RegOpKind         -- dst := dst - src (two-register subtraction, floors at 0)
  | mulSrc : RegOpKind         -- dst := dst * src (two-register multiply)

abbrev RegOp := RegId × RegId × RegOpKind

def RegOpKind.usesDst : RegOpKind → Bool
  | .addSrc | .subSrc | .mulSrc => true
  | _ => false

-- applyRegOpKind takes srcVal and optionally dstVal (for two-register operations).
-- Immediate and unary transforms ignore dstVal.
def applyRegOpKind (t : RegOpKind) (srcVal : Nat) (dstVal : Nat := 0) : Nat :=
  match t with
  | .id => srcVal
  | .const n => n
  | .subConst k => srcVal - k
  | .addConst k => srcVal + k
  | .mulConst k => srcVal * k
  | .isGT n => if srcVal > n then 1 else 0
  | .addSrc => dstVal + srcVal
  | .subSrc => dstVal - srcVal
  | .mulSrc => dstVal * srcVal

-- Impl AST mirrors spec but adds regOp statements for register computations.
inductive ImplStmt : Type where
  | block : (EngineId → List DataPathInstrId) → ImplStmt    -- same as spec block
  | loop : ScopeId → List ImplStmt → ImplStmt        -- same as spec loop
  | cond : ScopeId → ScopeId → List ImplStmt → List ImplStmt → ImplStmt  -- same as spec cond
  | regOp : (EngineId → List RegOp) → ImplStmt  -- register computation block (prepended at loop entry)

-- Complete implementation program.
structure ImplProgram extends ProgramBase where
  body : List ImplStmt                                               -- impl AST (spec body + prepended regOps)
  regOps : EngineId → DataPathInstrId → List RegOp -- per-instruction regOps evaluated before issue
  waitReg : EngineId → DataPathInstrId → RegId                              -- register holding the wait value for issue guard
  waitOf : DataPathInstrId → SemaId                                        -- semaphore to wait on before issuing
  updateOf : DataPathInstrId → SemaId                                      -- semaphore to update on retirement

-- Mirrors spec FrameKind for impl stack frames.
inductive ImplFrameKind where
  | top
  | loop : ScopeId → ImplFrameKind
  | cond : ScopeId → ImplFrameKind

-- A stack frame in the impl: body, current statement, and loop kind.
structure ImplFrame where
  body : List ImplStmt
  stmtIdx : Nat
  kind : ImplFrameKind

-- Impl program counter: stack + three indices for nested progress tracking.
@[ext] structure ImplPC where
  stack : List ImplFrame
  instrIdx : Nat       -- instruction index within current block
  regOpIdx : Nat       -- progress within per-instruction regOps (before issue)
  stmtRegOpIdx : Nat   -- progress within a stmtRegOp block (loop-entry ops)

-- Runtime state of the implementation machine.
@[ext] structure ImplState where
  controlState : EngineId → ControlState     -- per-engine control state (shared with spec)
  dataPathState : DataPathState                  -- shared datapath/memory state (shared with spec)
  pc : EngineId → ImplPC                     -- per-engine program counter
  inflight : EngineId → List (DataPathInstrId × Phase) -- per-engine in-flight queue (same as spec)
  registers : EngineId → RegId → Nat         -- per-engine register file
  semaphores : SemaId → Nat                  -- global semaphore bank (impl-only)

-- Impl transition relation: one step on one engine.
inductive ImplStep (impl : ImplProgram) : EngineId → ImplState → ImplState → Prop where

  -- regOpStep: commit one per-instruction regOp (computing wait value before issue).
  | regOpStep (e : EngineId) (s : ImplState)
      (hEngines : e ∈ impl.engines)
      (frame : ImplFrame) (rest : List ImplFrame)
      (f : EngineId → List DataPathInstrId) (instr : DataPathInstrId)
      (dst src : RegId) (t : RegOpKind)
      (hStack : (s.pc e).stack = frame :: rest)
      (hStmt : frame.body[frame.stmtIdx]? = some (.block f))
      (hInstr : (f e)[(s.pc e).instrIdx]? = some instr)
      (hRegOp : (impl.regOps e instr)[(s.pc e).regOpIdx]? = some (dst, src, t))
      : ImplStep impl e s
          { s with
            registers := funUpdate s.registers e
              (funUpdate (s.registers e) dst (applyRegOpKind t (s.registers e src) (s.registers e dst)))
            pc := funUpdate s.pc e
              { (s.pc e) with regOpIdx := (s.pc e).regOpIdx + 1 } }

  -- issue: all regOps done, semaphore ≥ wait value, dispatch instruction.
  | issue (e : EngineId) (s : ImplState)
      (hEngines : e ∈ impl.engines)
      (frame : ImplFrame) (rest : List ImplFrame)
      (f : EngineId → List DataPathInstrId) (instr : DataPathInstrId)
      (hStack : (s.pc e).stack = frame :: rest)
      (hStmt : frame.body[frame.stmtIdx]? = some (.block f))
      (hInstr : (f e)[(s.pc e).instrIdx]? = some instr)
      (hRegOpsDone : (s.pc e).regOpIdx = (impl.regOps e instr).length)
      (hWait : s.semaphores (impl.waitOf instr) ≥ s.registers e (impl.waitReg e instr))
      : ImplStep impl e s
          { s with
            pc := funUpdate s.pc e
              { (s.pc e) with instrIdx := (s.pc e).instrIdx + 1, regOpIdx := 0 }
            inflight := funUpdate s.inflight e
              (s.inflight e ++ [(instr, Phase.issued)]) }

  -- commit: apply datapath effect of an issued instruction (same as spec).
  | commit (e : EngineId) (s : ImplState)
      (hEngines : e ∈ impl.engines)
      (idx : Nat) (instr : DataPathInstrId)
      (hIdx : (s.inflight e)[idx]? = some (instr, Phase.issued))
      : ImplStep impl e s
          { s with
            dataPathState := impl.instrOp instr s.dataPathState
            inflight := funUpdate s.inflight e
              ((s.inflight e).set idx (instr, Phase.committed)) }

  -- retire: pop head of inflight queue, increment update semaphore.
  | retire (e : EngineId) (s : ImplState)
      (hEngines : e ∈ impl.engines)
      (instr : DataPathInstrId) (inflightRest : List (DataPathInstrId × Phase))
      (hHead : s.inflight e = (instr, Phase.committed) :: inflightRest)
      : ImplStep impl e s
          { s with
            inflight := funUpdate s.inflight e inflightRest
            semaphores := funUpdate s.semaphores (impl.updateOf instr)
              (s.semaphores (impl.updateOf instr) + 1) }

  -- blockDone: all instructions in block issued, advance to next statement.
  | blockDone (e : EngineId) (s : ImplState)
      (hEngines : e ∈ impl.engines)
      (frame : ImplFrame) (rest : List ImplFrame)
      (f : EngineId → List DataPathInstrId)
      (hStack : (s.pc e).stack = frame :: rest)
      (hStmt : frame.body[frame.stmtIdx]? = some (.block f))
      (hDone : (s.pc e).instrIdx = (f e).length)
      : ImplStep impl e s
          { s with
            pc := funUpdate s.pc e
              { stack := ⟨frame.body, frame.stmtIdx + 1, frame.kind⟩ :: rest,
                instrIdx := 0, regOpIdx := 0, stmtRegOpIdx := 0 } }

  -- stmtRegOpStep: commit one register op within a stmtRegOp block.
  -- Steps through the ops list one at a time via stmtRegOpIdx.
  | stmtRegOpStep (e : EngineId) (s : ImplState)
      (hEngines : e ∈ impl.engines)
      (frame : ImplFrame) (rest : List ImplFrame)
      (ops : EngineId → List RegOp)
      (dst src : RegId) (t : RegOpKind)
      (hStack : (s.pc e).stack = frame :: rest)
      (hStmt : frame.body[frame.stmtIdx]? = some (.regOp ops))
      (hOp : (ops e)[(s.pc e).stmtRegOpIdx]? = some (dst, src, t))
      : ImplStep impl e s
          { s with
            registers := funUpdate s.registers e
              (funUpdate (s.registers e) dst (applyRegOpKind t (s.registers e src) (s.registers e dst)))
            pc := funUpdate s.pc e
              { (s.pc e) with stmtRegOpIdx := (s.pc e).stmtRegOpIdx + 1 } }

  -- stmtRegOpDone: all ops in the block are done, advance to next statement.
  | stmtRegOpDone (e : EngineId) (s : ImplState)
      (hEngines : e ∈ impl.engines)
      (frame : ImplFrame) (rest : List ImplFrame)
      (ops : EngineId → List RegOp)
      (hStack : (s.pc e).stack = frame :: rest)
      (hStmt : frame.body[frame.stmtIdx]? = some (.regOp ops))
      (hDone : (s.pc e).stmtRegOpIdx = (ops e).length)
      : ImplStep impl e s
          { s with
            pc := funUpdate s.pc e
              { stack := ⟨frame.body, frame.stmtIdx + 1, frame.kind⟩ :: rest,
                instrIdx := (s.pc e).instrIdx, regOpIdx := 0, stmtRegOpIdx := 0 } }

  -- loopEnter: guard true, push frame.
  | loopEnter (e : EngineId) (s : ImplState)
      (hEngines : e ∈ impl.engines)
      (frame : ImplFrame) (rest : List ImplFrame)
      (lid : ScopeId) (loopBody : List ImplStmt)
      (hStack : (s.pc e).stack = frame :: rest)
      (hStmt : frame.body[frame.stmtIdx]? = some (.loop lid loopBody))
      (hGuard : impl.guard e lid (s.controlState e) = true)
      : ImplStep impl e s
          { s with
            pc := funUpdate s.pc e
              { stack := ⟨loopBody, 0, .loop lid⟩ :: frame :: rest,
                instrIdx := 0, regOpIdx := 0, stmtRegOpIdx := 0 }
            controlState := funUpdate s.controlState e
              (impl.controlOp e lid (s.controlState e)) }

  -- loopSkip: guard false, advance past loop.
  | loopSkip (e : EngineId) (s : ImplState)
      (hEngines : e ∈ impl.engines)
      (frame : ImplFrame) (rest : List ImplFrame)
      (lid : ScopeId) (loopBody : List ImplStmt)
      (hStack : (s.pc e).stack = frame :: rest)
      (hStmt : frame.body[frame.stmtIdx]? = some (.loop lid loopBody))
      (hGuard : impl.guard e lid (s.controlState e) = false)
      : ImplStep impl e s
          { s with
            pc := funUpdate s.pc e
              { stack := ⟨frame.body, frame.stmtIdx + 1, frame.kind⟩ :: rest,
                instrIdx := 0, regOpIdx := 0, stmtRegOpIdx := 0 } }

  -- loopBack: unconditional, pop frame. Parent stmtIdx still at loop stmt.
  | loopBack (e : EngineId) (s : ImplState)
      (hEngines : e ∈ impl.engines)
      (frame parent : ImplFrame) (rest : List ImplFrame)
      (lid : ScopeId)
      (hStack : (s.pc e).stack = frame :: parent :: rest)
      (hKind : frame.kind = .loop lid)
      (hEnd : frame.stmtIdx = frame.body.length)
      : ImplStep impl e s
          { s with
            pc := funUpdate s.pc e
              { stack := parent :: rest, instrIdx := 0, regOpIdx := 0, stmtRegOpIdx := 0 } }

  | condTrue (e : EngineId) (s : ImplState)
      (hEngines : e ∈ impl.engines)
      (frame : ImplFrame) (rest : List ImplFrame)
      (thenId elseId : ScopeId) (thenBody elseBody : List ImplStmt)
      (hStack : (s.pc e).stack = frame :: rest)
      (hStmt : frame.body[frame.stmtIdx]? = some (.cond thenId elseId thenBody elseBody))
      (hGuard : impl.guard e thenId (s.controlState e) = true)
      : ImplStep impl e s
          { s with
            pc := funUpdate s.pc e
              { stack := ⟨thenBody, 0, .cond thenId⟩ :: frame :: rest,
                instrIdx := 0, regOpIdx := 0, stmtRegOpIdx := 0 }
            controlState := funUpdate s.controlState e
              (impl.controlOp e thenId (s.controlState e)) }

  | condFalse (e : EngineId) (s : ImplState)
      (hEngines : e ∈ impl.engines)
      (frame : ImplFrame) (rest : List ImplFrame)
      (thenId elseId : ScopeId) (thenBody elseBody : List ImplStmt)
      (hStack : (s.pc e).stack = frame :: rest)
      (hStmt : frame.body[frame.stmtIdx]? = some (.cond thenId elseId thenBody elseBody))
      (hGuard : impl.guard e thenId (s.controlState e) = false)
      : ImplStep impl e s
          { s with
            pc := funUpdate s.pc e
              { stack := ⟨elseBody, 0, .cond elseId⟩ :: frame :: rest,
                instrIdx := 0, regOpIdx := 0, stmtRegOpIdx := 0 }
            controlState := funUpdate s.controlState e
              (impl.controlOp e elseId (s.controlState e)) }

  | condDone (e : EngineId) (s : ImplState)
      (hEngines : e ∈ impl.engines)
      (frame parent : ImplFrame) (rest : List ImplFrame)
      (sid : ScopeId)
      (hStack : (s.pc e).stack = frame :: parent :: rest)
      (hKind : frame.kind = .cond sid)
      (hEnd : frame.stmtIdx = frame.body.length)
      : ImplStep impl e s
          { s with
            pc := funUpdate s.pc e
              { stack := ⟨parent.body, parent.stmtIdx + 1, parent.kind⟩ :: rest,
                instrIdx := 0, regOpIdx := 0, stmtRegOpIdx := 0 } }

theorem ImplStep.mem_engines {impl : ImplProgram} {e : EngineId} {is is' : ImplState}
    (h : ImplStep impl e is is') : e ∈ impl.engines := by
  cases h <;> assumption
