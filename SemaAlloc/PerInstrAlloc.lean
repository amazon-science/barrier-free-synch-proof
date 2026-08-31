import SemaAlloc.Impl
import SemaAlloc.Utilities

-- Extract the producer instruction from a dependency, if any.
def depProducer (dep : Dep) : Option DataPathInstrId :=
  match dep with
  | .dep p _ => some p
  | .none => none

-- Per-instruction wait-value computation: waitReg := totalEntries(producer's loop) - offset.
def perInstrExpectedRegOps (spec : Program) (waitReg : RegId) (monotoneReg : EngineId → ScopeId → RegId)
    (e : EngineId) (consumer : DataPathInstrId)
    : List RegOp :=
  match spec.depGraph consumer with
  | .none => [(waitReg, waitReg, .const 0)]
  | .dep producer offset =>
    let parentLoop := innermostParentScope spec.engines spec.body producer
    let sharedLoop := innermostSharedScope spec.engines spec.body producer consumer
    match parentLoop with
    | some plid =>
      if sharedLoop = parentLoop then
        -- producerIsParent: subtract offset from monotoneReg
        [(waitReg, monotoneReg e plid, .id), (waitReg, waitReg, .subConst offset)]
      else
        -- child/sibling: monotoneReg directly, no offset subtraction
        [(waitReg, monotoneReg e plid, .id)]
    | none =>
      -- The implicit top-level loop has one trip; underflow therefore yields 0.
      [(waitReg, waitReg, .const (1 - offset))]

-- Direct child loop IDs at the top level of a statement list.
def directChildScopes : List Stmt → List ScopeId
  | [] => []
  | (Stmt.loop lid _) :: rest => lid :: directChildScopes rest
  | (Stmt.cond thenId elseId _ _) :: rest => thenId :: elseId :: directChildScopes rest
  | _ :: rest => directChildScopes rest

-- Loop-entry register operations:
-- 1. Increment monotoneReg and tripReg for the entering loop
-- 2. Reset tripReg to 0 for all direct child loops (fresh parent iteration)
-- The child resets ensure tripRegInv holds: when a parent loop enters,
-- its children's tripRegs are 0 = tripEntries (reading a fresh H slot).
def scopeEntryOps (monotoneReg tripReg : EngineId → ScopeId → RegId)
    (loopBody : List Stmt) (e : EngineId) (lid : ScopeId)
    : List RegOp :=
  [(monotoneReg e lid, monotoneReg e lid, .addConst 1),
   (tripReg e lid, tripReg e lid, .addConst 1)]
  ++ (directChildScopes loopBody).map (fun child =>
    (tripReg e child, tripReg e child, .const 0))

-- Spec and impl bodies correspond 1-to-1. Loops/conds PREPEND a regOp to the impl body.
inductive BodyMatch (monotoneReg tripReg : EngineId → ScopeId → RegId)
    : List Stmt → List ImplStmt → Prop where
  | nil : BodyMatch monotoneReg tripReg [] []
  | block (specF : EngineId → List DataPathInstrId)
      (specRest : List Stmt) (implRest : List ImplStmt)
      (hRest : BodyMatch monotoneReg tripReg specRest implRest)
      : BodyMatch monotoneReg tripReg
          (Stmt.block specF :: specRest) (ImplStmt.block specF :: implRest)
  | loop (lid : ScopeId) (specBody : List Stmt) (implBody : List ImplStmt)
      (specRest : List Stmt) (implRest : List ImplStmt)
      (hBody : BodyMatch monotoneReg tripReg specBody implBody)
      (hRest : BodyMatch monotoneReg tripReg specRest implRest)
      : BodyMatch monotoneReg tripReg
          (Stmt.loop lid specBody :: specRest)
          (ImplStmt.loop lid ([ImplStmt.regOp (scopeEntryOps monotoneReg tripReg specBody · lid)] ++ implBody) :: implRest)
  | cond (thenId elseId : ScopeId) (specThen specElse : List Stmt) (implThen implElse : List ImplStmt)
      (specRest : List Stmt) (implRest : List ImplStmt)
      (hThen : BodyMatch monotoneReg tripReg specThen implThen)
      (hElse : BodyMatch monotoneReg tripReg specElse implElse)
      (hRest : BodyMatch monotoneReg tripReg specRest implRest)
      : BodyMatch monotoneReg tripReg
          (Stmt.cond thenId elseId specThen specElse :: specRest)
          (ImplStmt.cond thenId elseId
            ([ImplStmt.regOp (scopeEntryOps monotoneReg tripReg specThen · thenId)] ++ implThen)
            ([ImplStmt.regOp (scopeEntryOps monotoneReg tripReg specElse · elseId)] ++ implElse)
            :: implRest)

-- Shared allocation fields used by all allocation strategies.
structure AllocBase (spec : Program) (impl : ImplProgram) where
  monotoneReg : EngineId → ScopeId → RegId         -- monotone register: tracks totalEntries(sid)
  monotoneRegInj : ∀ e l1 l2, monotoneReg e l1 = monotoneReg e l2 → l1 = l2  -- distinct loops get distinct registers
  tripReg : EngineId → ScopeId → RegId      -- trip register: tracks tripEntries(sid), resets on parent entry
  tripRegInj : ∀ e l1 l2, tripReg e l1 = tripReg e l2 → l1 = l2  -- distinct loops get distinct registers
  gateReg : EngineId → RegId                     -- scratch register for IsGT gate computation
  waitReg : EngineId → RegId                     -- register holding computed wait value for issue guard
  noClob : ∀ e lid, waitReg e ≠ monotoneReg e lid  -- waitReg doesn't alias any monotoneReg
  noClob_trip_wait : ∀ e lid, waitReg e ≠ tripReg e lid  -- waitReg doesn't alias any tripReg
  noClob_trip_loop : ∀ e l1 l2, tripReg e l1 ≠ monotoneReg e l2  -- tripRegs don't alias monotoneRegs
  noClob_gate_wait : ∀ e, gateReg e ≠ waitReg e  -- gateReg doesn't alias waitReg
  noClob_gate_loop : ∀ e lid, gateReg e ≠ monotoneReg e lid  -- gateReg doesn't alias any monotoneReg
  noClob_gate_trip : ∀ e lid, gateReg e ≠ tripReg e lid  -- gateReg doesn't alias any tripReg
  waitRegEq : ∀ e i, impl.waitReg e i = waitReg e  -- impl's waitReg is engine-uniform (not instruction-dependent)
  baseEq : spec.toProgramBase = impl.toProgramBase  -- spec and impl share the same ProgramBase
  bodyMatch : BodyMatch monotoneReg tripReg spec.body impl.body  -- AST correspondence

-- Wrap allocation-specific regOps with the vacuous gate.
-- The first op zeros waitReg so the waitRegChain invariant holds from regOpIdx ≥ 1.
-- gatePrefix: waitReg := 0, then IsGT(tripReg[shared], offset) → gateReg
-- gateSuffix: waitReg := waitReg * gateReg (zeros out wait value when vacuous)
def wrapWithGate (spec : Program) (gateReg waitReg : RegId)
    (tripReg : EngineId → ScopeId → RegId) (e : EngineId) (consumer : DataPathInstrId)
    (innerOps : List RegOp) : List RegOp :=
  match spec.depGraph consumer with
  | .none => innerOps
  | .dep producer offset =>
    let shared := innermostSharedScope spec.engines spec.body producer consumer
    match shared with
    | some sid =>
      [(waitReg, waitReg, .const 0), -- technically unecessary, but simplifies proofs slightly. can be CSE-ed
       (gateReg, tripReg e sid, .isGT offset)]
      ++ innerOps
      ++ [(waitReg, gateReg, .mulSrc)]
    | none => innerOps

theorem perInstrExpectedRegOps_nonEmpty (spec : Program) (waitReg : RegId) (monotoneReg : EngineId → ScopeId → RegId)
    (e : EngineId) (consumer : DataPathInstrId)
    : (perInstrExpectedRegOps spec waitReg monotoneReg e consumer).length > 0 := by
  simp only [perInstrExpectedRegOps]
  split
  · simp
  · split
    · split <;> simp
    · simp

-- Per-instruction allocation: one semaphore per instruction.
structure PerInstrAllocR (spec : Program) (impl : ImplProgram) extends AllocBase spec impl where
  sema : DataPathInstrId → SemaId                    -- per-instruction semaphore assignment
  semaInj : ∀ i j, sema i = sema j → i = j  -- distinct instructions get distinct semaphores
  updateEq : ∀ i, impl.updateOf i = sema i  -- update the instruction's own semaphore on retire
  waitOfEq : ∀ i, impl.waitOf i = match depProducer (spec.depGraph i) with
    | some p => sema p | none => impl.waitOf i  -- wait on producer's semaphore (if dep exists)
  regOpsEq : ∀ e i, impl.regOps e i = wrapWithGate spec (gateReg e) (waitReg e) tripReg e i
      (perInstrExpectedRegOps spec (waitReg e) monotoneReg e i)  -- regOps = gate-wrapped per-instruction wait computation

theorem perInstr_innerRegOpsFirstSafe (spec : Program) (impl : ImplProgram) (alloc : PerInstrAllocR spec impl)
    : ∀ e i (src : RegId) (t : RegOpKind),
      (perInstrExpectedRegOps spec (alloc.waitReg e) alloc.monotoneReg e i)[0]? = some (alloc.waitReg e, src, t) →
      t.usesDst = false ∧ (src = alloc.waitReg e → ∃ n, t = .const n) := by
  intro e i src t h
  simp only [perInstrExpectedRegOps] at h
  split at h
  · simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨by simp [h.2.2.symm, RegOpKind.usesDst], fun _ => ⟨0, h.2.2.symm⟩⟩
  · rename_i producer offset hDep
    split at h
    · rename_i plid hPL
      split at h <;> (
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
        exact ⟨by simp [h.2.2.symm, RegOpKind.usesDst], fun hSrc => absurd hSrc.symm (h.2.1.symm ▸ alloc.noClob e plid)⟩)
    · simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨by simp [h.2.2.symm, RegOpKind.usesDst], fun _ => ⟨1 - offset, h.2.2.symm⟩⟩

theorem perInstr_regOpsNonEmpty (spec : Program) (impl : ImplProgram) (alloc : PerInstrAllocR spec impl)
    : ∀ e i, (impl.regOps e i).length > 0 := by
  intro e i
  rw [alloc.regOpsEq]
  unfold wrapWithGate
  split
  · exact perInstrExpectedRegOps_nonEmpty spec (alloc.waitReg e) alloc.monotoneReg e i
  · simp only
    split
    · simp
    · exact perInstrExpectedRegOps_nonEmpty spec (alloc.waitReg e) alloc.monotoneReg e i

theorem perInstr_innerRegOpsDstWaitReg (spec : Program) (impl : ImplProgram) (alloc : PerInstrAllocR spec impl)
    : ∀ e i (idx : Nat) (dst src : RegId) (t : RegOpKind),
      (perInstrExpectedRegOps spec (alloc.waitReg e) alloc.monotoneReg e i)[idx]? = some (dst, src, t) → dst = alloc.waitReg e := by
  intro e i idx dst src t h
  simp only [perInstrExpectedRegOps] at h
  split at h
  · match idx with
    | 0 => simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h; exact h.1.symm
    | n + 1 => simp at h
  · rename_i producer offset hDep
    split at h
    · rename_i plid hPL
      split at h
      · match idx with
        | 0 => simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h; exact h.1.symm
        | 1 => simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h; exact h.1.symm
        | n + 2 => simp at h
      · match idx with
        | 0 => simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h; exact h.1.symm
        | n + 1 => simp at h
    · match idx with
      | 0 => simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h; exact h.1.symm
      | n + 1 => simp at h

-- Inner reg ops don't have gateReg as source (needed for gate decomposition)
theorem perInstr_innerRegOpsSrcNeGate (spec : Program) (impl : ImplProgram) (alloc : PerInstrAllocR spec impl)
    : ∀ e i op, op ∈ perInstrExpectedRegOps spec (alloc.waitReg e) alloc.monotoneReg e i → op.2.1 ≠ alloc.gateReg e := by
  intro e i op hMem
  simp only [perInstrExpectedRegOps] at hMem
  -- Each op's source is either waitReg or monotoneReg, neither equals gateReg
  split at hMem
  · -- none: [(waitReg, waitReg, .const 0)]
    simp at hMem; obtain ⟨_, rfl, _⟩ := hMem; exact Ne.symm (alloc.noClob_gate_wait e)
  · rename_i producer offset
    split at hMem
    · rename_i plid
      split at hMem
      · -- [(waitReg, monotoneReg, .id), (waitReg, waitReg, .subConst)]
        simp [List.mem_cons] at hMem
        rcases hMem with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩
        · exact Ne.symm (alloc.noClob_gate_loop e _)
        · exact Ne.symm (alloc.noClob_gate_wait e)
      · -- [(waitReg, monotoneReg, .id)]
        simp at hMem; obtain ⟨_, rfl, _⟩ := hMem; exact Ne.symm (alloc.noClob_gate_loop e _)
    · -- [(waitReg, waitReg, .const (1 - offset))]
      simp at hMem; obtain ⟨_, rfl, _⟩ := hMem; exact Ne.symm (alloc.noClob_gate_wait e)

-- Every direct child loop ID appears in the full loop ID list.
theorem directChildScopes_mem_scopeIdsOf : ∀ (body : List Stmt) (lid : ScopeId),
    lid ∈ directChildScopes body → lid ∈ scopeIdsOf body
  | [], _, h => by simp [directChildScopes] at h
  | .block _ :: rest, lid, h => by
    simp [directChildScopes] at h; simp [scopeIdsOf]; exact directChildScopes_mem_scopeIdsOf rest lid h
  | .loop lid' lb :: rest, lid, h => by
    simp [directChildScopes] at h; simp [scopeIdsOf]
    rcases h with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (directChildScopes_mem_scopeIdsOf rest lid h))
  | .cond tid eid tb eb :: rest, lid, h => by
    simp [directChildScopes] at h; simp [scopeIdsOf]
    rcases h with rfl | rfl | h
    · left; rfl
    · right; left; rfl
    · right; right; right; right; exact directChildScopes_mem_scopeIdsOf rest lid h

-- scopeParent.go returns the container when lid is a direct child loop at the top level.
theorem directChild_scopeParent_go : ∀ (body : List Stmt) (lid container : ScopeId),
    lid ∈ directChildScopes body → UniqueScopeIds body →
    scopeParent.go body lid (some container) = some container
  | [], _, _, h, _ => by simp [directChildScopes] at h
  | .block _ :: rest, lid, container, h, hU => by
    simp [directChildScopes] at h; simp [scopeParent.go]
    cases hU with | block _ _ hUR => exact directChild_scopeParent_go rest lid container h hUR
  | .loop lid' lb :: rest, lid, container, h, hU => by
    simp [directChildScopes] at h; simp [scopeParent.go]
    cases hU with
    | loop _ _ _ hNotBody hNotRest hDisj hUBody hURest =>
      rcases h with rfl | h
      · simp
      · have hNeLid : lid ≠ lid' := fun h' => by
          subst h'; exact hNotRest (directChildScopes_mem_scopeIdsOf rest lid h)
        intro _
        have hNotInLb : lid ∉ scopeIdsOf lb := fun h' =>
          hDisj lid h' (directChildScopes_mem_scopeIdsOf rest lid h)
        rw [scopeParent_go_none_of_not_mem lid (some lid') hNotInLb hUBody]; simp
        exact directChild_scopeParent_go rest lid container h hURest
  | .cond tid eid tb eb :: rest, lid, container, h, hU => by
    simp [directChildScopes] at h; simp [scopeParent.go]
    cases hU with
    | cond _ _ _ _ _ hNe hTnTb hTnEb hTnR hEnTb hEnEb hEnR hTbDisj hEbDisj hUTb hUEb hUR =>
      rcases h with rfl | rfl | h
      · simp
      · have : lid ≠ tid := fun h' => by subst h'; exact absurd rfl hNe
        simp
      · have hNeTid : lid ≠ tid := fun h' => by
          subst h'; exact hTnR (directChildScopes_mem_scopeIdsOf rest lid h)
        have hNeEid : lid ≠ eid := fun h' => by
          subst h'; exact hEnR (directChildScopes_mem_scopeIdsOf rest lid h)
        intro _ _
        have hLidInRest := directChildScopes_mem_scopeIdsOf rest lid h
        have hNotInTb : lid ∉ scopeIdsOf tb := fun h' => (hTbDisj lid h').2 hLidInRest
        have hNotInEb : lid ∉ scopeIdsOf eb := fun h' => hEbDisj lid h' hLidInRest
        rw [scopeParent_go_none_of_not_mem lid (some tid) hNotInTb hUTb]; simp
        rw [scopeParent_go_none_of_not_mem lid (some eid) hNotInEb hUEb]; simp
        exact directChild_scopeParent_go rest lid container h hUR

private theorem uniqueScopeIds_of_getElem_loop {body : List Stmt} {idx : Nat} {lid : ScopeId} {lb : List Stmt}
    (hIdx : body[idx]? = some (Stmt.loop lid lb)) (hUniq : UniqueScopeIds body) : UniqueScopeIds lb := by
  have := uniqueScopeIds_of_getElem hIdx hUniq; cases this with | loop _ _ _ _ _ _ hU _ => exact hU

private theorem uniqueScopeIds_of_getElem_condTrue {body : List Stmt} {idx : Nat}
    {tid eid : ScopeId} {tb eb : List Stmt}
    (hIdx : body[idx]? = some (Stmt.cond tid eid tb eb)) (hUniq : UniqueScopeIds body) : UniqueScopeIds tb := by
  have := uniqueScopeIds_of_getElem hIdx hUniq; cases this with | cond _ _ _ _ _ _ _ _ _ _ _ _ _ _ hU _ _ => exact hU

private theorem uniqueScopeIds_of_getElem_condFalse {body : List Stmt} {idx : Nat}
    {tid eid : ScopeId} {tb eb : List Stmt}
    (hIdx : body[idx]? = some (Stmt.cond tid eid tb eb)) (hUniq : UniqueScopeIds body) : UniqueScopeIds eb := by
  have := uniqueScopeIds_of_getElem hIdx hUniq; cases this with | cond _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hU _ => exact hU

-- If lid is a direct child loop in the body of loop sid (found via getElem),
-- then scopeParent returns sid.
theorem scopeParent_of_directChild_loop {body : List Stmt} {idx : Nat}
    {sid : ScopeId} {loopBody : List Stmt} {lid : ScopeId}
    (hIdx : body[idx]? = some (Stmt.loop sid loopBody))
    (hMem : lid ∈ directChildScopes loopBody)
    (hUniq : UniqueScopeIds body)
    : scopeParent body lid = some sid := by
  unfold scopeParent
  have hLidInSub := directChildScopes_mem_scopeIdsOf loopBody lid hMem
  have hUniqSub := uniqueScopeIds_of_getElem_loop hIdx hUniq
  have hInner := directChild_scopeParent_go loopBody lid sid hMem hUniqSub
  exact scopeParent_go_lift_loop hIdx hUniq hInner hLidInSub

theorem scopeParent_of_directChild_condTrue {body : List Stmt} {idx : Nat}
    {thenId elseId : ScopeId} {tb eb : List Stmt} {lid : ScopeId}
    (hIdx : body[idx]? = some (Stmt.cond thenId elseId tb eb))
    (hMem : lid ∈ directChildScopes tb)
    (hUniq : UniqueScopeIds body)
    : scopeParent body lid = some thenId := by
  unfold scopeParent
  have hLidInSub := directChildScopes_mem_scopeIdsOf tb lid hMem
  have hUniqSub := uniqueScopeIds_of_getElem_condTrue hIdx hUniq
  have hInner := directChild_scopeParent_go tb lid thenId hMem hUniqSub
  exact scopeParent_go_lift_cond_then hIdx hUniq hInner hLidInSub

theorem scopeParent_of_directChild_condFalse {body : List Stmt} {idx : Nat}
    {thenId elseId : ScopeId} {tb eb : List Stmt} {lid : ScopeId}
    (hIdx : body[idx]? = some (Stmt.cond thenId elseId tb eb))
    (hMem : lid ∈ directChildScopes eb)
    (hUniq : UniqueScopeIds body)
    : scopeParent body lid = some elseId := by
  unfold scopeParent
  have hLidInSub := directChildScopes_mem_scopeIdsOf eb lid hMem
  have hUniqSub := uniqueScopeIds_of_getElem_condFalse hIdx hUniq
  have hInner := directChild_scopeParent_go eb lid elseId hMem hUniqSub
  exact scopeParent_go_lift_cond_else hIdx hUniq hInner hLidInSub
