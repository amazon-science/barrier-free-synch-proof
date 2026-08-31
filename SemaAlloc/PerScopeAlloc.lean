import SemaAlloc.PerInstrAlloc
import SemaAlloc.SpecInv

/-! # Per-Loop Allocation

A loop body is the set of `block` instructions that are direct children of the
same loop. All instructions in a loop body execute the same number of times.

PerScopeAllocR assigns one semaphore per (loop, engine) instead of one per instruction.
The semaphore value = sum of retire counts over the loop's instructions on that engine.
Individual retire counts are decoded via the N*r-(N-K) formula.
-/

/-! ## scopeInstrs: the core definition

Collects all instructions belonging to a (loop, engine) pair by deep recursion
that mirrors innermostParentScope's structure.

- `loop = none`: collect from direct-child blocks at the top-level
- `loop = some sid`: recurse into the AST looking for sid, then collect at that level
-/
-- All instructions in the loop body of (loop, engine): the direct-child blocks of the loop.
def scopeInstrs (engines : List EngineId) (eng : EngineId)
    : List Stmt → Option ScopeId → List DataPathInstrId
  | [], _ => []
  -- loop = none: collecting direct-child block instructions
  | .block f :: rest, none => f eng ++ scopeInstrs engines eng rest none
  | .loop _ _ :: rest, none => scopeInstrs engines eng rest none
  | .cond _ _ _ _ :: rest, none => scopeInstrs engines eng rest none
  -- loop = some sid: searching for the loop
  | .block _ :: rest, some sid => scopeInstrs engines eng rest (some sid)
  | .loop lid body' :: rest, some sid =>
    if lid = sid then scopeInstrs engines eng body' none
    else scopeInstrs engines eng body' (some sid) ++
         scopeInstrs engines eng rest (some sid)
  | .cond thenId elseId tb eb :: rest, some sid =>
    if thenId = sid then scopeInstrs engines eng tb none
    else if elseId = sid then scopeInstrs engines eng eb none
    else scopeInstrs engines eng tb (some sid) ++
         scopeInstrs engines eng eb (some sid) ++
         scopeInstrs engines eng rest (some sid)

-- Simp lemmas for scopeInstrs: none (= flatInstrs)
@[simp] theorem scopeInstrs_nil_none : scopeInstrs engines eng [] none = [] := by
  simp [scopeInstrs]
@[simp] theorem scopeInstrs_block_none :
    scopeInstrs engines eng (Stmt.block f :: rest) none = f eng ++ scopeInstrs engines eng rest none := by
  simp [scopeInstrs]
@[simp] theorem scopeInstrs_loop_none :
    scopeInstrs engines eng (Stmt.loop lid body :: rest) none = scopeInstrs engines eng rest none := by
  simp [scopeInstrs]
@[simp] theorem scopeInstrs_cond_none :
    scopeInstrs engines eng (Stmt.cond t e tb eb :: rest) none = scopeInstrs engines eng rest none := by
  simp [scopeInstrs]

-- Simp lemmas for scopeInstrs: some sid
@[simp] theorem scopeInstrs_nil_some : scopeInstrs engines eng [] (some sid) = [] := by
  simp [scopeInstrs]
@[simp] theorem scopeInstrs_block_some :
    scopeInstrs engines eng (Stmt.block f :: rest) (some sid) =
    scopeInstrs engines eng rest (some sid) := by
  simp [scopeInstrs]
@[simp] theorem scopeInstrs_loop_some :
    scopeInstrs engines eng (Stmt.loop lid body :: rest) (some sid) =
    if lid = sid then scopeInstrs engines eng body none
    else scopeInstrs engines eng body (some sid) ++ scopeInstrs engines eng rest (some sid) := by
  simp [scopeInstrs]
@[simp] theorem scopeInstrs_cond_some :
    scopeInstrs engines eng (Stmt.cond thenId elseId tb eb :: rest) (some sid) =
    if thenId = sid then scopeInstrs engines eng tb none
    else if elseId = sid then scopeInstrs engines eng eb none
    else scopeInstrs engines eng tb (some sid) ++
         scopeInstrs engines eng eb (some sid) ++
         scopeInstrs engines eng rest (some sid) := by
  simp [scopeInstrs]

-- Sum of retire counts over all instructions in a loop body.
def scopeRetireSum (rc : DataPathInstrId → Nat) (engines : List EngineId) (eng : EngineId)
    (body : List Stmt) (loop : Option ScopeId) : Nat :=
  (scopeInstrs engines eng body loop).foldl (fun acc i => acc + rc i) 0

-- Per-loop wait-value computation: N*r - (N-K) where N = |loop body|, K = producer's 1-indexed position.
-- Equivalent to N*(r-1) + K for r ≥ 1; uses N*r - (N-K) form so Nat subtraction gives 0 when r = 0.
def perScopeExpectedRegOps (spec : Program) (waitReg : RegId)
    (monotoneReg : EngineId → ScopeId → RegId) (e : EngineId) (consumer : DataPathInstrId)
    : List RegOp :=
  match spec.depGraph consumer with
  | .none => [(waitReg, waitReg, .const 0)]
  | .dep producer offset =>
    let prodLoop := innermostParentScope spec.engines spec.body producer
    let sharedLoop := innermostSharedScope spec.engines spec.body producer consumer
    let prodEng := (instrEngine spec.engines spec.body producer).getD 0
    let instrs := scopeInstrs spec.engines prodEng spec.body prodLoop
    let N := instrs.length
    let K := instrs.idxOf producer + 1
    match prodLoop with
    | some plid =>
      if sharedLoop = prodLoop then
        [(waitReg, monotoneReg e plid, .id),
         (waitReg, waitReg, .subConst offset),
         (waitReg, waitReg, .mulConst N),
         (waitReg, waitReg, .subConst (N - K))]
      else
        [(waitReg, monotoneReg e plid, .id),
         (waitReg, waitReg, .mulConst N),
         (waitReg, waitReg, .subConst (N - K))]
    | none =>
      -- Decode the producer in the one-trip implicit top-level loop.
      [(waitReg, waitReg, .const ((1 - offset) * N - (N - K)))]

/-- Per-scope allocation (denoted "per-loop" in the paper): one semaphore per (scope, engine) pair.
-- Asserts that spec and impl share the same ProgramBase (engines, instrOp, guard, controlOp),
-- that their ASTs correspond via BodyMatch, that register families
-- (monotoneReg, tripReg, waitReg, gateReg) are pairwise non-aliasing,
-- and that semaphore/regOp assignments match the per-loop scheme (one semaphore
-- per (loop, engine) pair, N*r+K encoding).
-/
structure PerScopeAllocR (spec : Program) (impl : ImplProgram)
    extends AllocBase spec impl where
  -- semaphore for each (scope, engine) pair
  perScopeSema : Option ScopeId → EngineId → SemaId
  -- distinct pairs get distinct semaphores
  perScopeSemaInj : ∀ s1 e1 s2 e2, perScopeSema s1 e1 = perScopeSema s2 e2 → s1 = s2 ∧ e1 = e2
  -- update the (producer's loop, producer's engine) semaphore
  updateEq : ∀ i, impl.updateOf i = perScopeSema
    (innermostParentScope spec.engines spec.body i)
    ((instrEngine spec.engines spec.body i).getD 0)
  -- wait on producer's (loop, engine) semaphore
  waitOfEq : ∀ i, impl.waitOf i = match depProducer (spec.depGraph i) with
    | some p => perScopeSema
        (innermostParentScope spec.engines spec.body p)
        ((instrEngine spec.engines spec.body p).getD 0)
    | none => impl.waitOf i
  -- regOps = gate-wrapped per-loop N*r-K computation
  regOpsEq : ∀ e i, impl.regOps e i = wrapWithGate spec (gateReg e) (waitReg e) tripReg e i
      (perScopeExpectedRegOps spec (waitReg e) monotoneReg e i)

theorem perScopeExpectedRegOps_nonEmpty (spec : Program) (waitReg : RegId)
    (monotoneReg : EngineId → ScopeId → RegId) (e : EngineId) (consumer : DataPathInstrId)
    : (perScopeExpectedRegOps spec waitReg monotoneReg e consumer).length > 0 := by
  simp only [perScopeExpectedRegOps]
  split
  · simp
  · split
    · split <;> simp
    · simp

theorem perScope_innerRegOpsFirstSafe (spec : Program) (impl : ImplProgram) (alloc : PerScopeAllocR spec impl)
    : ∀ e i (src : RegId) (t : RegOpKind),
      (perScopeExpectedRegOps spec (alloc.waitReg e) alloc.monotoneReg e i)[0]? = some (alloc.waitReg e, src, t) →
      t.usesDst = false ∧ (src = alloc.waitReg e → ∃ n, t = .const n) := by
  intro e i src t h
  simp only [perScopeExpectedRegOps] at h
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
      exact ⟨by simp [h.2.2.symm, RegOpKind.usesDst], fun _ => ⟨_, h.2.2.symm⟩⟩

theorem perScope_regOpsNonEmpty (spec : Program) (impl : ImplProgram) (alloc : PerScopeAllocR spec impl)
    : ∀ e i, (impl.regOps e i).length > 0 := by
  intro e i
  rw [alloc.regOpsEq]
  unfold wrapWithGate
  split
  · exact perScopeExpectedRegOps_nonEmpty spec (alloc.waitReg e) alloc.monotoneReg e i
  · simp only
    split
    · simp
    · exact perScopeExpectedRegOps_nonEmpty spec (alloc.waitReg e) alloc.monotoneReg e i

theorem perScope_innerRegOpsDstWaitReg (spec : Program) (impl : ImplProgram) (alloc : PerScopeAllocR spec impl)
    : ∀ e i (idx : Nat) (dst src : RegId) (t : RegOpKind),
      (perScopeExpectedRegOps spec (alloc.waitReg e) alloc.monotoneReg e i)[idx]? = some (dst, src, t) → dst = alloc.waitReg e := by
  intro e i idx dst src t h
  simp only [perScopeExpectedRegOps] at h
  split at h
  · match idx with
    | 0 => simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h; exact h.1.symm
    | n + 1 => simp at h
  · rename_i producer offset
    split at h
    · rename_i plid
      split at h
      · match idx with
        | 0 | 1 | 2 | 3 => simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq, Prod.mk.injEq] at h; exact h.1.symm
        | n + 4 => simp at h
      · match idx with
        | 0 | 1 | 2 => simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq, Prod.mk.injEq] at h; exact h.1.symm
        | n + 3 => simp at h
    · match idx with
      | 0 => simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h; exact h.1.symm
      | n + 1 => simp at h

-- Inner reg ops don't have gateReg as source
theorem perScope_innerRegOpsSrcNeGate (spec : Program) (impl : ImplProgram) (alloc : PerScopeAllocR spec impl)
    : ∀ e i op, op ∈ perScopeExpectedRegOps spec (alloc.waitReg e) alloc.monotoneReg e i → op.2.1 ≠ alloc.gateReg e := by
  intro e i op hMem
  simp only [perScopeExpectedRegOps] at hMem
  split at hMem
  · simp at hMem; obtain ⟨_, rfl, _⟩ := hMem; exact Ne.symm (alloc.noClob_gate_wait e)
  · rename_i producer offset
    split at hMem
    · rename_i plid
      split at hMem <;> (
        simp [List.mem_cons] at hMem
        rcases hMem with ⟨_, rfl, _⟩ | hMem
        · exact Ne.symm (alloc.noClob_gate_loop e _)
        · rcases hMem with ⟨_, rfl, _⟩ | hMem
          · exact Ne.symm (alloc.noClob_gate_wait e)
          · rcases hMem with rfl | rfl <;> exact Ne.symm (alloc.noClob_gate_wait e))
    · simp at hMem; obtain ⟨_, rfl, _⟩ := hMem; exact Ne.symm (alloc.noClob_gate_wait e)

-- Bridge lemmas connecting scopeInstrs to innermostParentScope/instrEngine
-- are in the per-loop simulation modules (which import both PerScopeAlloc and Allocatable)
