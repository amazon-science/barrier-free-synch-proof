import SemaAlloc.PerScopeAlloc
import SemaAlloc.PerScopeInv
import SemaAlloc.PCBound
import SemaAlloc.Allocatable
import SemaAlloc.MatchStates
import Batteries

/-! # Per-Loop Lemmas -/

def perScopeSemaInv (spec : Program) (alloc : PerScopeAllocR spec impl) (ss : SpecState) (is : ImplState) : Prop :=
  ∀ loop eng, eng ∈ spec.engines → is.semaphores (alloc.perScopeSema loop eng) =
    scopeRetireSum ss.rc spec.engines eng spec.body loop

theorem perScope_semaInv_mono (spec : Program) (impl : ImplProgram) (alloc : PerScopeAllocR spec impl)
    (ss0 ss1 : SpecState) (is0 is1 : ImplState)
    (hRC : ss0.rc = ss1.rc) (hSema : is0.semaphores = is1.semaphores)
    (hInv : perScopeSemaInv spec alloc ss0 is0)
    : perScopeSemaInv spec alloc ss1 is1 := by
  intro loop eng hE
  rw [← hSema, hInv loop eng hE]; simp [scopeRetireSum, hRC]

/-! ## perScopeExpectedWaitVal: symbolic value of foldRegOps(perScopeExpectedRegOps) -/

def perScopeExpectedWaitVal (spec : Program) (ss : SpecState) (e : EngineId) (instr : DataPathInstrId) : Nat :=
  match spec.depGraph instr with
  | .none => 0
  | .dep producer offset =>
    let prodLoop := innermostParentScope spec.engines spec.body producer
    let sharedLoop := innermostSharedScope spec.engines spec.body producer instr
    let prodEng := (instrEngine spec.engines spec.body producer).getD 0
    let instrs := scopeInstrs spec.engines prodEng spec.body prodLoop
    let N := instrs.length
    let K := instrs.idxOf producer + 1
    match prodLoop with
    | some plid =>
      if sharedLoop = prodLoop then
        (totalEntries ss e plid - offset) * N - (N - K)
      else
        totalEntries ss e plid * N - (N - K)
    | none => (1 - offset) * N - (N - K)

theorem foldRegOps_perScopeExpectedRegOps_waitReg
    {spec : Program} {ss : SpecState} {e : EngineId} {instr : DataPathInstrId}
    {ab : AllocBase spec impl}
    (baseRegs : RegId → Nat)
    (_hBase : baseRegs (ab.waitReg e) = 0)
    (hLoopRegs : ∀ plid, baseRegs (ab.monotoneReg e plid) = totalEntries ss e plid)
    : foldRegOps (perScopeExpectedRegOps spec (ab.waitReg e) ab.monotoneReg e instr) baseRegs (ab.waitReg e)
      = perScopeExpectedWaitVal spec ss e instr := by
  unfold perScopeExpectedRegOps perScopeExpectedWaitVal
  match hDep : spec.depGraph instr with
  | .none =>
    simp [foldRegOps, funUpdate, applyRegOpKind]
  | .dep producer offset =>
    simp only
    match hPL : innermostParentScope spec.engines spec.body producer with
    | none =>
      simp [foldRegOps, funUpdate, applyRegOpKind]
    | some plid =>
      simp only
      split
      · simp [foldRegOps, funUpdate, applyRegOpKind, hLoopRegs plid]
      · simp [foldRegOps, funUpdate, applyRegOpKind, hLoopRegs plid]

/-! ## Arithmetic Helpers -/

theorem foldl_add_shift (xs : List α) (f : α → Nat) (a : Nat) :
    xs.foldl (fun acc i => acc + f i) a =
    a + xs.foldl (fun acc i => acc + f i) 0 := by
  induction xs generalizing a with
  | nil => simp
  | cons x rest ih =>
    simp only [List.foldl_cons]
    rw [ih (a + f x), ih (0 + f x)]
    omega

theorem foldl_add_append (xs ys : List α) (f : α → Nat) :
    (xs ++ ys).foldl (fun acc i => acc + f i) 0 =
    xs.foldl (fun acc i => acc + f i) 0 +
    ys.foldl (fun acc i => acc + f i) 0 := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp only [List.cons_append, List.foldl_cons]
    rw [foldl_add_shift _ _ (0 + f x), foldl_add_shift _ _ (0 + f x)]
    rw [ih]; omega

theorem foldl_sum_ge_of_all_ge (instrs : List α) (f : α → Nat) (v : Nat)
    (h : ∀ x, x ∈ instrs → f x ≥ v)
    : instrs.foldl (fun acc i => acc + f i) 0 ≥ instrs.length * v := by
  induction instrs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [foldl_add_shift]
    have hx := h x (List.Mem.head xs)
    have hxs := ih (fun y hy => h y (List.Mem.tail x hy))
    simp only [Nat.succ_mul]; omega

-- Upper bound: if every element satisfies f(x) ≤ m, then sum ≤ n * m
theorem foldl_sum_le_of_all_le (instrs : List α) (f : α → Nat) (m : Nat)
    (h : ∀ x, x ∈ instrs → f x ≤ m)
    : instrs.foldl (fun acc i => acc + f i) 0 ≤ instrs.length * m := by
  induction instrs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [foldl_add_shift]
    have hx := h x (List.Mem.head xs)
    have hxs := ih (fun y hy => h y (List.Mem.tail x hy))
    simp only [Nat.succ_mul]; omega

private theorem idxOf_ge_of_mem_drop (l : List DataPathInstrId) (n : Nat) (x : DataPathInstrId)
    (hNd : l.Nodup) (hx : x ∈ l.drop n) : l.idxOf x ≥ n := by
  induction l generalizing n with
  | nil => simp at hx
  | cons a as ih =>
    cases n with
    | zero => simp
    | succ m =>
      simp [List.drop_succ_cons] at hx
      have hNd' := (List.nodup_cons.mp hNd).2
      have hne : x ≠ a := by
        intro heq; subst heq
        exact (List.nodup_cons.mp hNd).1 (List.drop_subset _ _ hx)
      have hIH := ih m hNd' hx
      show List.idxOf x (a :: as) ≥ m + 1
      have hbeq : (a == x) = false := by
        rw [beq_eq_false_iff_ne]; exact Ne.symm hne
      simp [List.idxOf_cons, hbeq]
      omega

theorem perScope_lower_bound
    (instrs : List DataPathInstrId) (rc : DataPathInstrId → Nat)
    (hNodup : instrs.Nodup)
    (hMono : ∀ i j, i ∈ instrs → j ∈ instrs →
      instrs.idxOf i < instrs.idxOf j → rc j ≤ rc i)
    (hBound : ∀ i j, i ∈ instrs → j ∈ instrs → rc i ≤ rc j + 1)
    (producer : DataPathInstrId) (hMem : producer ∈ instrs)
    (v : Nat) (hv : instrs.foldl (fun acc i => acc + rc i) 0 ≥
      instrs.length * (v - 1) + (instrs.idxOf producer + 1))
    : rc producer ≥ v := by
  by_contra hlt
  have hlt' : rc producer < v := Nat.lt_of_not_le hlt
  have hp_lt := List.idxOf_lt_length_of_mem hMem
  -- Every x in drop (idxOf producer) has rc x ≤ rc producer
  have hDropBound : ∀ x, x ∈ instrs.drop (instrs.idxOf producer) → rc x ≤ rc producer := by
    intro x hx
    have hxMem : x ∈ instrs := List.drop_subset _ _ hx
    have hIdx := idxOf_ge_of_mem_drop instrs (instrs.idxOf producer) x hNodup hx
    rcases Nat.eq_or_lt_of_le hIdx with heq | hgt
    · -- idxOf x = idxOf producer → x = producer
      have hxLt := List.idxOf_lt_length_of_mem hxMem
      have h1 := List.getElem_idxOf hxLt
      have h2 := List.getElem_idxOf hp_lt
      conv at h1 =>
        lhs
        arg 2
        rw [<- heq]
      have : x = producer := h1.symm.trans h2
      subst this; exact Nat.le_refl _
    · exact hMono producer x hMem hxMem hgt
  -- Every x in take (idxOf producer) has rc x ≤ rc producer + 1
  have hTakeBound : ∀ x, x ∈ instrs.take (instrs.idxOf producer) → rc x ≤ rc producer + 1 := by
    intro x hx
    exact hBound x producer (List.take_subset _ _ hx) hMem
  -- Split foldl over take ++ drop
  have hSplit := List.take_append_drop (instrs.idxOf producer) instrs
  have hSum : (instrs.take (instrs.idxOf producer) ++ instrs.drop (instrs.idxOf producer)).foldl
      (fun acc i => acc + rc i) 0 = instrs.foldl (fun acc i => acc + rc i) 0 := by
    rw [hSplit]
  have hSumSplit := foldl_add_append (instrs.take (instrs.idxOf producer))
      (instrs.drop (instrs.idxOf producer)) rc
  rw [hSplit] at hSumSplit
  -- Upper bounds on each part
  have hTakeLen : (instrs.take (instrs.idxOf producer)).length = instrs.idxOf producer := by
    simp [Nat.min_eq_left (Nat.le_of_lt hp_lt)]
  have hDropLen : (instrs.drop (instrs.idxOf producer)).length = instrs.length - instrs.idxOf producer := by
    simp
  have hTakeSum := foldl_sum_le_of_all_le (instrs.take (instrs.idxOf producer)) rc (rc producer + 1) hTakeBound
  have hDropSum := foldl_sum_le_of_all_le (instrs.drop (instrs.idxOf producer)) rc (rc producer) hDropBound
  rw [hTakeLen] at hTakeSum
  rw [hDropLen] at hDropSum
  have hTotal : instrs.foldl (fun acc i => acc + rc i) 0 ≤
      instrs.idxOf producer * (rc producer + 1) + (instrs.length - instrs.idxOf producer) * rc producer := by
    omega
  have hple : instrs.idxOf producer ≤ instrs.length := Nat.le_of_lt hp_lt
  have hExp : instrs.idxOf producer * (rc producer + 1) =
      instrs.idxOf producer * rc producer + instrs.idxOf producer :=
    Nat.mul_succ _ _
  have hCombine : (instrs.length - instrs.idxOf producer) * rc producer + instrs.idxOf producer * rc producer =
      instrs.length * rc producer := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hple]
  have hBound2 : instrs.foldl (fun acc i => acc + rc i) 0 ≤ instrs.length * rc producer + instrs.idxOf producer := by
    calc instrs.foldl (fun acc i => acc + rc i) 0
        ≤ instrs.idxOf producer * (rc producer + 1) + (instrs.length - instrs.idxOf producer) * rc producer := hTotal
      _ = instrs.idxOf producer * rc producer + instrs.idxOf producer + (instrs.length - instrs.idxOf producer) * rc producer := by rw [hExp]
      _ = (instrs.length - instrs.idxOf producer) * rc producer + instrs.idxOf producer * rc producer + instrs.idxOf producer := by omega
      _ = instrs.length * rc producer + instrs.idxOf producer := by rw [hCombine]
  have hrc_bound : instrs.length * rc producer ≤ instrs.length * (v - 1) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

-- Bridge: PCBound.scopeInstrsNone = scopeInstrs (PerScopeAlloc) for loop = none
private theorem scopeInstrsNone_eq_scopeInstrs_none
    {engines : List EngineId} {eng : EngineId} {body : List Stmt}
    : PCBound.scopeInstrsNone engines eng body = scopeInstrs engines eng body none := by
  induction body with
  | nil => simp [PCBound.scopeInstrsNone]
  | cons s rest ih => cases s <;> simp [PCBound.scopeInstrsNone, ih]

-- idxOf in scopeInstrs = instrsBefore + instrIdx (for loop = none)
-- Uses PCBound's proved theorem via the bridge
theorem scopeInstrs_idxOf_eq_instrsBefore_none
    {engines : List EngineId} {eng : EngineId} {body : List Stmt}
    {stmtIdx instrIdx : Nat} {f : EngineId → List DataPathInstrId} {instr : DataPathInstrId}
    (hStmt : body[stmtIdx]? = some (Stmt.block f))
    (hInstr : (f eng)[instrIdx]? = some instr)
    (hUI : UniqueInstrIds engines body)
    (hEngMem : eng ∈ engines)
    (hNodup : (scopeInstrs engines eng body none).Nodup)
    : (scopeInstrs engines eng body none).idxOf instr =
        instrsBefore engines eng body stmtIdx + instrIdx := by
  rw [← scopeInstrsNone_eq_scopeInstrs_none]
  exact PCBound.scopeInstrsNone_idxOf_eq engines eng body stmtIdx instrIdx f instr hStmt hInstr hUI
    hEngMem (scopeInstrsNone_eq_scopeInstrs_none ▸ hNodup)

theorem innermostParentScope_block :
    innermostParentScope engines (Stmt.block f :: rest) instr =
    innermostParentScope engines rest instr := by
  simp

theorem innermostParentScope_loop :
    innermostParentScope engines (Stmt.loop lid body' :: rest) instr =
    if instrInBody engines body' instr then
      some ((innermostParentScope engines body' instr).getD lid)
    else
      innermostParentScope engines rest instr := by
  simp only [innermostParentScope]
  cases hIB : instrInBody engines body' instr
  simp; cases innermostParentScope engines body' instr <;> simp

theorem innermostParentScope_cond :
    innermostParentScope engines (Stmt.cond thenId elseId tb eb :: rest) instr =
    if instrInBody engines tb instr then
      some ((innermostParentScope engines tb instr).getD thenId)
    else if instrInBody engines eb instr then
      some ((innermostParentScope engines eb instr).getD elseId)
    else
      innermostParentScope engines rest instr := by
  simp only [innermostParentScope]
  cases hIB1 : instrInBody engines tb instr
  · simp
    cases hIB2 : instrInBody engines eb instr
    simp; cases innermostParentScope engines eb instr <;> simp
  · simp; cases innermostParentScope engines tb instr <;> simp

theorem innermostParentScope_none_of_not_in_body : ∀ {engines : List EngineId}
    {body : List Stmt} {instr : DataPathInstrId},
    instrInBody engines body instr = false →
    innermostParentScope engines body instr = none
  | _, [], _, _ => by simp
  | engines, .block f :: rest, instr, h => by
    simp only [instrInBody, Bool.or_eq_false_iff] at h
    rw [innermostParentScope_block]; exact innermostParentScope_none_of_not_in_body h.2
  | engines, .loop lid body' :: rest, instr, h => by
    simp only [instrInBody, Bool.or_eq_false_iff] at h
    rw [innermostParentScope_loop, if_neg (by simp [h.1])]
    exact innermostParentScope_none_of_not_in_body h.2
  | engines, .cond t e tb eb :: rest, instr, h => by
    simp only [instrInBody, Bool.or_eq_false_iff] at h
    rw [innermostParentScope_cond, if_neg (by simp [h.1.1]), if_neg (by simp [h.1.2])]
    exact innermostParentScope_none_of_not_in_body h.2

theorem findInBlock_eq_of_mem_single {engines : List EngineId}
    {f : EngineId → List DataPathInstrId} {eng : EngineId} {instr : DataPathInstrId}
    (hE : eng ∈ engines) (hIn : instr ∈ f eng)
    (hSE : ∀ instr e1 e2, e1 ∈ engines → e2 ∈ engines →
      instr ∈ f e1 → instr ∈ f e2 → e1 = e2)
    : findInBlock engines f instr = some eng := by
  induction engines with
  | nil => simp at hE
  | cons e' rest ih =>
    simp [findInBlock]
    rcases List.mem_cons.mp hE with rfl | hRest
    · simp [hIn]
    · by_cases hIn' : instr ∈ f e'
      · have := hSE instr e' eng (List.Mem.head _) (List.mem_cons_of_mem _ hRest) hIn' hIn
        simp [this, hIn]
      · simp [hIn']
        exact ih hRest (fun i e1 e2 h1 h2 => hSE i e1 e2 (List.mem_cons_of_mem _ h1) (List.mem_cons_of_mem _ h2))

theorem mem_of_findInBlock_eq_some : ∀ {engines : List EngineId}
    {f : EngineId → List DataPathInstrId} {instr : DataPathInstrId} {eng : EngineId},
    findInBlock engines f instr = some eng → instr ∈ f eng
  | [], _, _, _, h => by simp [findInBlock] at h
  | e :: rest, f, instr, eng, h => by
    simp only [findInBlock] at h
    by_cases hIn : instr ∈ f e
    · simp [hIn] at h; rw [← h]; exact hIn
    · simp [hIn] at h; exact mem_of_findInBlock_eq_some h

-- if instrInBody = true then instrEngine ≠ none
theorem instrEngine_ne_none_of_instrInBody : ∀ {engines : List EngineId}
    {body : List Stmt} {instr : DataPathInstrId},
    instrInBody engines body instr = true →
    instrEngine engines body instr ≠ none
  | _, [], _, h => by simp [instrInBody] at h
  | engines, .block f :: rest, instr, h => by
    rw [instrEngine_block]; simp [Option.orElse]; simp [instrInBody] at h
    rcases h with h | h <;>
      cases hfb : findInBlock engines f instr with
      | some e => simp
      | none =>
        first
        | simp [hfb] at h
        | (simp; exact instrEngine_ne_none_of_instrInBody h)
  | engines, .loop lid body' :: rest, instr, h => by
    rw [instrEngine_loop]; simp [Option.orElse]; simp [instrInBody] at h
    rcases h with h | h <;>
      cases hIE : instrEngine engines body' instr with
      | some e => simp
      | none =>
        first
        | exact absurd hIE (instrEngine_ne_none_of_instrInBody h)
        | (simp; exact instrEngine_ne_none_of_instrInBody h)
  | engines, .cond t e tb eb :: rest, instr, h => by
    rw [instrEngine_cond]; simp [Option.orElse]; simp [instrInBody] at h
    rcases h with (h | h) | h <;>
      (cases hIE : instrEngine engines tb instr with
       | some e' => simp
       | none =>
         first
         | exact absurd hIE (instrEngine_ne_none_of_instrInBody h)
         | (simp
            cases hIE2 : instrEngine engines eb instr with
            | some e' => simp
            | none =>
              first
              | exact absurd hIE2 (instrEngine_ne_none_of_instrInBody h)
              | (simp; exact instrEngine_ne_none_of_instrInBody h)))

-- membership in scopeInstrs → instrInBody
theorem instrInBody_of_scopeInstrs : ∀ {engines : List EngineId} {eng : EngineId}
    {body : List Stmt} {loop : Option ScopeId} {instr : DataPathInstrId},
    eng ∈ engines →
    instr ∈ scopeInstrs engines eng body loop →
    instrInBody engines body instr = true
  | _, _, [], _, _, _, h => by cases ‹Option ScopeId› <;> simp at h
  | _, _, .block _ :: _, none, _, hE, h => by
    simp at h; simp [instrInBody]
    rcases h with h | h
    · exact Or.inl (findInBlock_isSome_of_mem hE h)
    · exact Or.inr (instrInBody_of_scopeInstrs hE h)
  | _, _, .block _ :: _, some _, _, hE, h
  | _, _, .loop _ _ :: _, none, _, hE, h
  | _, _, .cond _ _ _ _ :: _, none, _, hE, h => by
    simp at h; simp [instrInBody]; exact Or.inr (instrInBody_of_scopeInstrs hE h)
  | _, _, .loop _ _ :: _, some _, _, hE, h => by
    simp at h; simp [instrInBody]
    split at h
    · exact Or.inl (instrInBody_of_scopeInstrs hE h)
    · rcases List.mem_append.mp h with h | h <;>
        [exact Or.inl (instrInBody_of_scopeInstrs hE h);
         exact Or.inr (instrInBody_of_scopeInstrs hE h)]
  | _, _, .cond _ _ _ _ :: _, some _, _, hE, h => by
    simp at h; simp [instrInBody]
    split at h
    · exact Or.inl (Or.inl (instrInBody_of_scopeInstrs hE h))
    · split at h
      · exact Or.inl (Or.inr (instrInBody_of_scopeInstrs hE h))
      · rcases List.mem_append.mp h with h | h
        · exact Or.inl (Or.inl (instrInBody_of_scopeInstrs hE h))
        · rcases List.mem_append.mp h with h | h <;>
            [exact Or.inl (Or.inr (instrInBody_of_scopeInstrs hE h));
             exact Or.inr (instrInBody_of_scopeInstrs hE h)]

/-! ## Bridge: scopeInstrs ↔ innermostParentScope/instrEngine -/

-- Forward: membership in scopeInstrs → loop and engine match
theorem scopeInstrs_implies_loop_engine :
    ∀ {engines : List EngineId} {eng : EngineId} {body : List Stmt}
    {loop : Option ScopeId} {instr : DataPathInstrId},
    UniqueInstrIds engines body → eng ∈ engines →
    instr ∈ scopeInstrs engines eng body loop →
    innermostParentScope engines body instr = loop ∧
    instrEngine engines body instr = some eng
  | _, _, [], none, _, _, _, h => by simp at h
  | _, _, [], some _, _, _, _, h => by simp at h
  -- block, none
  | engines, eng, .block f :: rest, none, instr, hUI, hE, h => by
    cases hUI with | block =>
    rename_i hND hSE hUIR hDisj
    simp at h
    rw [innermostParentScope_block, instrEngine_block]
    rcases h with hIn | hIn
    · have hNotRest := hDisj instr (findInBlock_isSome_of_mem hE hIn)
      exact ⟨innermostParentScope_none_of_not_in_body hNotRest,
             by simp [findInBlock_eq_of_mem_single hE hIn hSE, Option.orElse]⟩
    · have ⟨hS, hEng⟩ := scopeInstrs_implies_loop_engine hUIR hE hIn
      have hInRest := instrInBody_of_scopeInstrs hE hIn
      have hNotBlock : findInBlock engines f instr = none := by
        by_contra hc
        cases hfb : findInBlock engines f instr with
        | none => exact hc hfb
        | some e' => exact absurd hInRest (by simp [hDisj instr (by simp [hfb])])
      exact ⟨hS, by simp [hNotBlock, Option.orElse, hEng]⟩
  -- block, some: blocks don't contain loops, so instr must be in rest
  | engines, eng, .block f :: rest, some sid, instr, hUI, hE, h => by
    cases hUI with | block =>
    rename_i hND hSE hUIR hDisj
    simp at h
    rw [innermostParentScope_block, instrEngine_block]
    have ⟨hS, hEng⟩ := scopeInstrs_implies_loop_engine hUIR hE h
    have hInRest := instrInBody_of_scopeInstrs hE h
    have hNotBlock : findInBlock engines f instr = none := by
      by_contra hc
      cases hfb : findInBlock engines f instr with
      | none => exact hc hfb
      | some e' => exact absurd hInRest (by simp [hDisj instr (by simp [hfb])])
    exact ⟨hS, by simp [hNotBlock, Option.orElse, hEng]⟩
  -- loop, none: loops define loops, so instr must be in rest (not body')
  | engines, eng, .loop lid body' :: rest, none, instr, hUI, hE, h => by
    cases hUI with | loop =>
    rename_i hUIB hUIR hDisj
    simp at h
    rw [innermostParentScope_loop, instrEngine_loop]
    have ⟨hS, hEng⟩ := scopeInstrs_implies_loop_engine hUIR hE h
    have hInRest := instrInBody_of_scopeInstrs hE h
    have hNotBody : instrInBody engines body' instr = false := by
      by_contra hc; simp at hc; exact absurd hInRest (by simp [hDisj instr hc])
    exact ⟨by rw [if_neg (by simp [hNotBody])]; exact hS,
           by simp [instrEngine_none_of_not_in_body hNotBody, Option.orElse, hEng]⟩
  -- loop, some: either lid = sid (switch to none inside body') or recurse
  | engines, eng, .loop lid body' :: rest, some sid, instr, hUI, hE, h => by
    cases hUI with | loop =>
    rename_i hUIB hUIR hDisj
    simp at h
    rw [innermostParentScope_loop, instrEngine_loop]
    by_cases hLid : lid = sid
    · -- this loop IS the target loop
      subst hLid; simp at h
      have ⟨hS, hEng⟩ := scopeInstrs_implies_loop_engine hUIB hE h
      have hInBody := instrInBody_of_scopeInstrs hE h
      exact ⟨by rw [if_pos hInBody, hS]; simp,
             by simp [hEng, Option.orElse]⟩
    · -- target loop is deeper; instr in body' or rest
      simp [hLid] at h
      rcases h with hBody | hRest
      · have ⟨hS, hEng⟩ := scopeInstrs_implies_loop_engine hUIB hE hBody
        have hInBody := instrInBody_of_scopeInstrs hE hBody
        exact ⟨by rw [if_pos hInBody, hS]; simp,
               by simp [hEng, Option.orElse]⟩
      · have ⟨hS, hEng⟩ := scopeInstrs_implies_loop_engine hUIR hE hRest
        have hInRest := instrInBody_of_scopeInstrs hE hRest
        have hNotBody : instrInBody engines body' instr = false := by
          by_contra hc; simp at hc; exact absurd hInRest (by simp [hDisj instr hc])
        exact ⟨by rw [if_neg (by simp [hNotBody])]; exact hS,
               by simp [instrEngine_none_of_not_in_body hNotBody, Option.orElse, hEng]⟩
  -- cond, none: conds define loops, so instr must be in rest
  | engines, eng, .cond thenId elseId tb eb :: rest, none, instr, hUI, hE, h => by
    cases hUI with | cond =>
    rename_i hUITb hUIEb hD12 hUIR hD1R hD2R
    simp at h
    rw [innermostParentScope_cond, instrEngine_cond]
    have ⟨hS, hEng⟩ := scopeInstrs_implies_loop_engine hUIR hE h
    have hInRest := instrInBody_of_scopeInstrs hE h
    have hNotTb : instrInBody engines tb instr = false := by
      by_contra hc; simp at hc; exact absurd hInRest (by simp [hD1R instr hc])
    have hNotEb : instrInBody engines eb instr = false := by
      by_contra hc; simp at hc; exact absurd hInRest (by simp [hD2R instr hc])
    exact ⟨by rw [if_neg (by simp [hNotTb]), if_neg (by simp [hNotEb])]; exact hS,
           by simp [instrEngine_none_of_not_in_body hNotTb,
                    instrEngine_none_of_not_in_body hNotEb, Option.orElse, hEng]⟩
  -- cond, some: thenId=sid, elseId=sid, or deeper in tb/eb/rest
  -- cond, some (forward)
  | engines, eng, .cond thenId elseId tb eb :: rest, some sid, instr, hUI, hE, h => by
    cases hUI with | cond =>
    rename_i hUITb hUIEb hD12 hUIR hD1R hD2R
    simp at h
    rw [innermostParentScope_cond, instrEngine_cond]
    by_cases hTid : thenId = sid
    · subst hTid; simp at h
      have ⟨hS, hEng⟩ := scopeInstrs_implies_loop_engine hUITb hE h
      have hInTb := instrInBody_of_scopeInstrs hE h
      exact ⟨by rw [if_pos hInTb, hS]; simp,
             by simp [hEng, Option.orElse]⟩
    · simp [hTid] at h
      by_cases hEid : elseId = sid
      · subst hEid; simp at h
        have ⟨hS, hEng⟩ := scopeInstrs_implies_loop_engine hUIEb hE h
        have hInEb := instrInBody_of_scopeInstrs hE h
        have hNotTb : instrInBody engines tb instr = false := by
          by_contra hc; simp at hc; exact absurd hInEb (by simp [hD12 instr hc])
        exact ⟨by rw [if_neg (by simp [hNotTb]), if_pos hInEb, hS]; simp,
               by simp [instrEngine_none_of_not_in_body hNotTb, hEng, Option.orElse]⟩
      · simp [hEid] at h
        rcases h with hTb | hEb | hRest
        · have ⟨hS, hEng⟩ := scopeInstrs_implies_loop_engine hUITb hE hTb
          have hInTb := instrInBody_of_scopeInstrs hE hTb
          exact ⟨by rw [if_pos hInTb, hS]; simp,
                 by simp [hEng, Option.orElse]⟩
        · have ⟨hS, hEng⟩ := scopeInstrs_implies_loop_engine hUIEb hE hEb
          have hInEb := instrInBody_of_scopeInstrs hE hEb
          have hNotTb : instrInBody engines tb instr = false := by
            by_contra hc; simp at hc; exact absurd hInEb (by simp [hD12 instr hc])
          exact ⟨by rw [if_neg (by simp [hNotTb]), if_pos hInEb, hS]; simp,
                 by simp [instrEngine_none_of_not_in_body hNotTb, hEng, Option.orElse]⟩
        · have ⟨hS, hEng⟩ := scopeInstrs_implies_loop_engine hUIR hE hRest
          have hInRest := instrInBody_of_scopeInstrs hE hRest
          have hNotTb : instrInBody engines tb instr = false := by
            by_contra hc; simp at hc; exact absurd hInRest (by simp [hD1R instr hc])
          have hNotEb : instrInBody engines eb instr = false := by
            by_contra hc; simp at hc; exact absurd hInRest (by simp [hD2R instr hc])
          exact ⟨by rw [if_neg (by simp [hNotTb]), if_neg (by simp [hNotEb])]; exact hS,
                 by simp [instrEngine_none_of_not_in_body hNotTb,
                          instrEngine_none_of_not_in_body hNotEb, Option.orElse, hEng]⟩

-- Backward: loop and engine match → membership in scopeInstrs
theorem mem_scopeInstrs_of_loop_engine :
    ∀ {engines : List EngineId} {eng : EngineId} {body : List Stmt}
    {loop : Option ScopeId} {instr : DataPathInstrId},
    UniqueInstrIds engines body → UniqueScopeIds body → eng ∈ engines →
    innermostParentScope engines body instr = loop →
    instrEngine engines body instr = some eng →
    instr ∈ scopeInstrs engines eng body loop
  | _, _, [], _, _, _, _, _, _, hEng => by simp [instrEngine] at hEng
  | engines, eng, .block f :: rest, loop, instr, hUI, hUS, hE, hS, hEng => by
    cases hUI with | block =>
    cases hUS with | block =>
    rename_i hND hSE hUIR hDisj hUSR
    rw [innermostParentScope_block] at hS; rw [instrEngine_block] at hEng
    cases hfb : findInBlock engines f instr with
    | some e' =>
      simp [hfb, Option.orElse] at hEng
      have hNotRest := hDisj instr (by simp [hfb])
      rw [innermostParentScope_none_of_not_in_body hNotRest] at hS
      cases loop with
      | none => simp; left; rw [← hEng]; exact mem_of_findInBlock_eq_some hfb
      | some _ => simp at hS
    | none =>
      simp [hfb, Option.orElse] at hEng
      cases loop with
      | none => simp; right; exact mem_scopeInstrs_of_loop_engine hUIR hUSR hE hS hEng
      | some sid => simp; exact mem_scopeInstrs_of_loop_engine hUIR hUSR hE hS hEng
  | engines, eng, .loop lid body' :: rest, loop, instr, hUI, hUS, hE, hS, hEng => by
    cases hUI with | loop =>
    cases hUS with | loop =>
    rename_i hUIB hUIR hDisj hUSB _ hUSR hNotRest _
    rw [innermostParentScope_loop] at hS; rw [instrEngine_loop] at hEng
    by_cases hInB : instrInBody engines body' instr = true
    · -- instr in loop body
      simp [hInB] at hS
      cases hIE : instrEngine engines body' instr with
      | none => exact absurd hIE (instrEngine_ne_none_of_instrInBody hInB)
      | some e' =>
        simp [hIE, Option.orElse] at hEng
        cases loop with
        | none => simp at hS
        | some sid =>
          simp; by_cases hLid : lid = sid
          · subst hLid; simp
            cases hIPS : innermostParentScope engines body' instr with
            | none => simp [hIPS] at hS; subst hEng
                      exact mem_scopeInstrs_of_loop_engine hUIB hUSB hE hIPS hIE
            | some inner => simp [hIPS] at hS; exfalso
                            rw [hS] at hIPS; rename_i hNotBody _; exact hNotBody (innermostParentScope_mem_scopeIdsOf hIPS)
          · simp [hLid]
            cases hIPS : innermostParentScope engines body' instr with
            | none => simp [hIPS] at hS; exact absurd hS hLid
            | some inner => simp [hIPS] at hS; subst hS; subst hEng; left
                            exact mem_scopeInstrs_of_loop_engine hUIB hUSB hE hIPS hIE
    · -- instr not in loop body
      have hf : instrInBody engines body' instr = false := by
        revert hInB; cases instrInBody engines body' instr <;> simp
      simp [hf] at hS; simp [instrEngine_none_of_not_in_body hf, Option.orElse] at hEng
      cases loop with
      | none => simp; exact mem_scopeInstrs_of_loop_engine hUIR hUSR hE hS hEng
      | some sid =>
        simp; by_cases hLid : lid = sid
        · subst hLid; exfalso; exact hNotRest (innermostParentScope_mem_scopeIdsOf hS)
        · simp [hLid]; right; exact mem_scopeInstrs_of_loop_engine hUIR hUSR hE hS hEng
  | engines, eng, .cond thenId elseId tb eb :: rest, loop, instr, hUI, hUS, hE, hS, hEng => by
    cases hUI with | cond =>
    cases hUS with | cond =>
    rename_i hUITb hUIEb hD12 hUIR hD1R hD2R hNe hUSTb _ _ hUSEb hTnEb hEnEb hUSR hTnR hEnR _ _
    rw [innermostParentScope_cond] at hS; rw [instrEngine_cond] at hEng
    by_cases hInTb : instrInBody engines tb instr = true
    · -- instr in tb
      simp [hInTb] at hS
      cases hIE : instrEngine engines tb instr with
      | none => exact absurd hIE (instrEngine_ne_none_of_instrInBody hInTb)
      | some e' =>
        simp [hIE, Option.orElse] at hEng
        cases loop with
        | none => simp at hS
        | some sid =>
          simp; by_cases hTid : thenId = sid
          · subst hTid; simp
            cases hIPS : innermostParentScope engines tb instr with
            | none => simp [hIPS] at hS; subst hEng
                      exact mem_scopeInstrs_of_loop_engine hUITb hUSTb hE hIPS hIE
            | some inner => simp [hIPS] at hS; exfalso
                            rw [hS] at hIPS
                            have : thenId ∈ scopeIdsOf tb := innermostParentScope_mem_scopeIdsOf hIPS
                            exact absurd this (by assumption)
          · by_cases hEid : elseId = sid
            · subst hEid; simp
              cases hIPS : innermostParentScope engines tb instr with
              | none => simp [hIPS] at hS; exact absurd hS hTid
              | some inner => simp [hIPS] at hS; subst hS; exfalso
                              exact absurd (innermostParentScope_mem_scopeIdsOf hIPS) (by assumption)
            · simp [hTid, hEid]
              cases hIPS : innermostParentScope engines tb instr with
              | none => simp [hIPS] at hS; exact absurd hS hTid
              | some inner => simp [hIPS] at hS; subst hS; subst hEng;
                              left; exact mem_scopeInstrs_of_loop_engine hUITb hUSTb hE hIPS hIE
    · -- instr not in tb
      have hTf : instrInBody engines tb instr = false := by
        revert hInTb; cases instrInBody engines tb instr <;> simp
      simp [hTf] at hS; simp [instrEngine_none_of_not_in_body hTf, Option.orElse] at hEng
      by_cases hInEb : instrInBody engines eb instr = true
      · -- instr in eb
        simp [hInEb] at hS
        cases hIE : instrEngine engines eb instr with
        | none => exact absurd hIE (instrEngine_ne_none_of_instrInBody hInEb)
        | some e' =>
          simp [hIE] at hEng
          cases loop with
          | none => simp at hS
          | some sid =>
            simp; by_cases hEid : elseId = sid
            · subst hEid; simp [hNe]
              cases hIPS : innermostParentScope engines eb instr with
              | none => simp [hIPS] at hS; subst hEng
                        exact mem_scopeInstrs_of_loop_engine hUIEb hUSEb hE hIPS hIE
              | some inner => simp [hIPS] at hS; exfalso
                              subst hS; exact hEnEb (innermostParentScope_mem_scopeIdsOf hIPS)
            · by_cases hTid : thenId = sid
              · subst hTid; simp
                cases hIPS : innermostParentScope engines eb instr with
                | none => simp [hIPS] at hS; exact absurd hS hEid
                | some inner => simp [hIPS] at hS; exfalso
                                rw [hS] at hIPS
                                have : thenId ∈ scopeIdsOf eb := innermostParentScope_mem_scopeIdsOf hIPS
                                exact absurd this hTnEb
              · simp [hTid, hEid]
                cases hIPS : innermostParentScope engines eb instr with
                | none => simp [hIPS] at hS; exact absurd hS hEid
                | some inner => simp [hIPS] at hS; right; left; subst hS; subst hEng
                                exact mem_scopeInstrs_of_loop_engine hUIEb hUSEb hE hIPS hIE
      · -- instr in rest
        have hEf : instrInBody engines eb instr = false := by
          revert hInEb; cases instrInBody engines eb instr <;> simp
        simp [hEf] at hS; simp [instrEngine_none_of_not_in_body hEf] at hEng
        cases loop with
        | none => simp; exact mem_scopeInstrs_of_loop_engine hUIR hUSR hE hS hEng
        | some sid =>
          simp; by_cases hTid : thenId = sid
          · subst hTid; exfalso; exact hTnR (innermostParentScope_mem_scopeIdsOf hS)
          · simp [hTid]; by_cases hEid : elseId = sid
            · subst hEid; exfalso; exact hEnR (innermostParentScope_mem_scopeIdsOf hS)
            · simp [hEid]; right; right; exact mem_scopeInstrs_of_loop_engine hUIR hUSR hE hS hEng

/-! ## scopeInstrs Nodup -/

theorem scopeInstrs_nodup :
    ∀ {engines : List EngineId} {eng : EngineId} {body : List Stmt}
    {loop : Option ScopeId},
    UniqueInstrIds engines body → eng ∈ engines →
    (scopeInstrs engines eng body loop).Nodup
  | _, _, [], none, _, _ => by simp
  | _, _, [], some _, _, _ => by simp
  | engines, eng, .block f :: rest, none, hUI, hE => by
    cases hUI with | block =>
    rename_i hND hSE hDisj hUIR
    simp
    apply List.nodup_append.mpr
    refine ⟨hND eng, scopeInstrs_nodup hDisj hE, ?_⟩
    -- disjointness: x ∈ f eng → x ∉ scopeInstrs rest none
    intro a ha b hb hab; subst hab
    have hFIB := findInBlock_isSome_of_mem hE ha
    have hNotRest := hUIR a hFIB
    -- a ∈ scopeInstrs rest none → instrInBody rest a = true (contradiction)
    exact absurd (instrInBody_of_scopeInstrs hE hb) (by simp [hNotRest])
  | engines, eng, .block _ :: rest, some sid, hUI, hE => by
    cases hUI with | block =>
    rename_i hND hSE hUIR hDisj
    simp
    exact scopeInstrs_nodup hUIR hE
  | engines, eng, .loop lid body' :: rest, none, hUI, hE => by
    cases hUI with | loop =>
    rename_i hUIB hUIR hDisj
    simp
    exact scopeInstrs_nodup hUIR hE
  | engines, eng, .loop lid body' :: rest, some sid, hUI, hE => by
    cases hUI with | loop =>
    rename_i hUIB hUIR hDisj
    simp
    by_cases hLid : lid = sid
    · simp [hLid]; exact scopeInstrs_nodup hUIB hE
    · simp [hLid]
      apply List.nodup_append.mpr
      refine ⟨scopeInstrs_nodup hUIB hE, scopeInstrs_nodup hUIR hE, ?_⟩
      intro a ha b hb hab; subst hab
      exact absurd (instrInBody_of_scopeInstrs hE hb) (by simp [hDisj a (instrInBody_of_scopeInstrs hE ha)])
  | engines, eng, .cond thenId elseId tb eb :: rest, none, hUI, hE => by
    cases hUI with | cond =>
    rename_i hUITb hUIEb hD12 hUIR hD1R hD2R
    simp
    exact scopeInstrs_nodup hUIR hE
  | engines, eng, .cond thenId elseId tb eb :: rest, some sid, hUI, hE => by
    cases hUI with | cond =>
    rename_i hUITb hUIEb hD12 hUIR hD1R hD2R
    simp
    by_cases hTid : thenId = sid
    · simp [hTid]; exact scopeInstrs_nodup hUITb hE
    · simp [hTid]
      by_cases hEid : elseId = sid
      · simp [hEid]; exact scopeInstrs_nodup hUIEb hE
      · simp [hEid]
        -- tb ++ (eb ++ rest): nodup_append twice
        apply List.nodup_append.mpr
        refine ⟨scopeInstrs_nodup hUITb hE, ?_, ?_⟩
        · -- Nodup (eb ++ rest)
          apply List.nodup_append.mpr
          refine ⟨scopeInstrs_nodup hUIEb hE, scopeInstrs_nodup hUIR hE, ?_⟩
          intro a ha b hb hab; subst hab
          exact absurd (instrInBody_of_scopeInstrs hE hb) (by simp [hD2R a (instrInBody_of_scopeInstrs hE ha)])
        · -- tb disjoint from eb ++ rest
          intro a ha b hb hab; subst hab
          rcases List.mem_append.mp hb with hEb | hRest
          · exact absurd (instrInBody_of_scopeInstrs hE hEb) (by simp [hD12 a (instrInBody_of_scopeInstrs hE ha)])
          · exact absurd (instrInBody_of_scopeInstrs hE hRest) (by simp [hD1R a (instrInBody_of_scopeInstrs hE ha)])

/-! ## foldl + funUpdate helpers for retire -/

-- Core lemma: funUpdate adds count(instr) to the sum
-- Adapted from per-loop progress branch
theorem foldl_funUpdate_add_count (l : List DataPathInstrId) (rc : DataPathInstrId → Nat) (instr : DataPathInstrId)
    : l.foldl (fun acc i => acc + funUpdate rc instr (rc instr + 1) i) 0 =
      l.foldl (fun acc i => acc + rc i) 0 + l.count instr := by
  induction l with
  | nil => simp [List.count]
  | cons a rest ih =>
    simp only [List.foldl_cons, Nat.zero_add, List.count_cons]
    rw [foldl_add_shift (f := fun i => funUpdate rc instr (rc instr + 1) i)]
    rw [foldl_add_shift (f := rc)]
    rw [ih]; simp only [funUpdate]
    by_cases ha : a = instr
    · subst ha; simp; omega
    · simp [ha]; omega

-- Nodup version: funUpdate adds 1 if member, 0 if not
theorem scopeRetireSum_funUpdate (rc : DataPathInstrId → Nat) (engines : List EngineId)
    (eng : EngineId) (body : List Stmt) (loop : Option ScopeId)
    (instr : DataPathInstrId) (hNodup : (scopeInstrs engines eng body loop).Nodup)
    : scopeRetireSum (funUpdate rc instr (rc instr + 1)) engines eng body loop =
      scopeRetireSum rc engines eng body loop + if instr ∈ scopeInstrs engines eng body loop then 1 else 0 := by
  simp only [scopeRetireSum]
  rw [foldl_funUpdate_add_count]
  congr 1
  split
  · -- count = 1 for Nodup + member
    rename_i hMem
    have : ∀ (l : List DataPathInstrId), l.Nodup → instr ∈ l → l.count instr = 1 := by
      intro l hND hM
      induction l with
      | nil => simp at hM
      | cons x xs ih =>
        simp only [List.count_cons]
        rcases List.mem_cons.mp hM with rfl | hm
        · simp [List.count_eq_zero_of_not_mem (List.nodup_cons.mp hND).1]
        · have hne : x ≠ instr := fun h => (List.nodup_cons.mp hND).1 (h ▸ hm)
          simp [hne, ih (List.nodup_cons.mp hND).2 hm]
    exact this _ hNodup hMem
  · exact List.count_eq_zero_of_not_mem ‹_›

-- If x ∉ list, funUpdate doesn't change the sum

/-! ## Per-Loop Retire / Issue / Backward Sim Skeleton -/

-- perScopeSemaInv preserved on retire
theorem perScope_retire_semaInv (spec : Program) (impl : ImplProgram) (alloc : PerScopeAllocR spec impl)
    (e : EngineId) (instr : DataPathInstrId) (rest : List (DataPathInstrId × Phase))
    (ss0 : SpecState) (is0 : ImplState)
    (hUI : UniqueInstrIds spec.engines spec.body) (hUS : UniqueScopeIds spec.body)
    (hSema : perScopeSemaInv spec alloc ss0 is0)
    (hInBody : instrInBody spec.engines spec.body instr = true)
    (_ : ss0.inflight e = (instr, Phase.committed) :: rest)
    : perScopeSemaInv spec alloc
        { ss0 with inflight := funUpdate ss0.inflight e rest,
                   rc := funUpdate ss0.rc instr (ss0.rc instr + 1) }
        { is0 with inflight := funUpdate is0.inflight e rest,
                   semaphores := funUpdate is0.semaphores (impl.updateOf instr) (is0.semaphores (impl.updateOf instr) + 1) } := by
  intro loop eng hEngMem
  simp only [perScopeSemaInv] at hSema
  simp only [scopeRetireSum]
  -- The semaphore for (loop, eng) either matches updateOf instr or not
  rw [alloc.updateEq] at *
  by_cases hMatch : alloc.perScopeSema loop eng = alloc.perScopeSema
      (innermostParentScope spec.engines spec.body instr)
      ((instrEngine spec.engines spec.body instr).getD 0)
  · -- Matching: this semaphore tracks instr's loop/engine
    obtain ⟨hLoopEq, hEngEq⟩ := alloc.perScopeSemaInj _ _ _ _ hMatch
    subst hLoopEq; subst hEngEq
    simp [funUpdate]
    rw [hSema _ _ hEngMem]
    -- scopeRetireSum with funUpdate rc: instr is in this scopeInstrs list
    -- RHS = scopeRetireSum (funUpdate rc instr (rc instr + 1))
    -- Use scopeRetireSum_funUpdate to equate with scopeRetireSum rc + 1
    rw [show List.foldl (fun acc i => acc + if i = instr then ss0.rc instr + 1 else ss0.rc i) 0
          (scopeInstrs spec.engines ((instrEngine spec.engines spec.body instr).getD 0) spec.body
            (innermostParentScope spec.engines spec.body instr)) =
        scopeRetireSum (funUpdate ss0.rc instr (ss0.rc instr + 1)) spec.engines
          ((instrEngine spec.engines spec.body instr).getD 0) spec.body
          (innermostParentScope spec.engines spec.body instr) from by
      simp only [scopeRetireSum, funUpdate_apply]]
    rw [scopeRetireSum_funUpdate _ _ _ _ _ _ (scopeInstrs_nodup hUI hEngMem)]
    simp [show instr ∈ scopeInstrs spec.engines ((instrEngine spec.engines spec.body instr).getD 0) spec.body
        (innermostParentScope spec.engines spec.body instr) from by
      have hIENe := instrEngine_ne_none_of_instrInBody hInBody
      obtain ⟨eng, hIE⟩ := Option.ne_none_iff_exists'.mp hIENe
      rw [hIE]; simp
      exact mem_scopeInstrs_of_loop_engine hUI hUS (instrEngine_mem_engines hIE) rfl hIE]
  · -- Non-matching: different semaphore, sum unchanged
    -- instr is NOT in this scopeInstrs list (bridge contradiction)
    have hNotMem : instr ∉ scopeInstrs spec.engines eng spec.body loop := by
      intro hMem
      have ⟨hS, hE⟩ := scopeInstrs_implies_loop_engine hUI hEngMem hMem
      exact hMatch (by rw [hS]; simp [hE])
    -- Step 1: reduce funUpdate on semaphores (LHS)
    simp only [funUpdate, ]
    rw [if_neg hMatch, hSema _ _ hEngMem]
    -- Both sides are foldl over same list. Since instr ∉ list, the if is always false.
    simp only [scopeRetireSum]
    have : ∀ (xs : List DataPathInstrId) (a : Nat), instr ∉ xs →
        xs.foldl (fun acc i => acc + ss0.rc i) a =
        xs.foldl (fun acc i => acc + if i = instr then ss0.rc instr + 1 else ss0.rc i) a := by
      intro xs a hNM
      induction xs generalizing a with
      | nil => rfl
      | cons y ys ih =>
        simp only [List.foldl_cons]
        have hNe : y ≠ instr := by intro h; exact hNM (h ▸ List.Mem.head _)
        rw [if_neg hNe]
        exact ih _ (fun h => hNM (List.Mem.tail _ h))
    exact this _ 0 hNotMem
