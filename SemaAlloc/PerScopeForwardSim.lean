import SemaAlloc.PerScopeInvStep
import SemaAlloc.ForwardSim

/-! # Forward Simulation for Per-Loop Allocation

Follows the same pattern as perScope_backward_sim_step/perScope_backward_sim_star:
custom step and star theorems that thread PerScopeInv alongside MatchStates.
-/

/-! ## Helper lemmas -/

private theorem idxOf_lt_of_mem_take (l : List DataPathInstrId) (n : Nat) (x : DataPathInstrId)
    (hNd : l.Nodup) (hx : x ∈ l.take n) : l.idxOf x < n := by
  induction l generalizing n with
  | nil => simp at hx
  | cons a as ih =>
    cases n with
    | zero => simp at hx
    | succ m =>
      simp [List.take_succ_cons] at hx
      rcases hx with rfl | hx
      · simp
      · have hNd' := (List.nodup_cons.mp hNd).2
        have hne : x ≠ a := by
          intro heq; subst heq
          exact (List.nodup_cons.mp hNd).1 (List.take_subset _ _ hx)
        have hIH := ih m hNd' hx
        have hbeq : (a == x) = false := by
          rw [beq_eq_false_iff_ne]; exact Ne.symm hne
        simp [List.idxOf_cons, hbeq]; omega

/-! ## perScope_upper_bound: forward direction of the N*r+K bound -/

theorem perScope_upper_bound
    (instrs : List DataPathInstrId) (rc : DataPathInstrId → Nat)
    (hNodup : instrs.Nodup)
    (hMono : ∀ i j, i ∈ instrs → j ∈ instrs →
      instrs.idxOf i < instrs.idxOf j → rc j ≤ rc i)
    (hBound : ∀ i j, i ∈ instrs → j ∈ instrs → rc i ≤ rc j + 1)
    (producer : DataPathInstrId) (hMem : producer ∈ instrs)
    (v : Nat) (hv : rc producer ≥ v) (hvpos : v ≥ 1)
    : instrs.foldl (fun acc i => acc + rc i) 0 ≥
      instrs.length * (v - 1) + (instrs.idxOf producer + 1) := by
  have hp_lt := List.idxOf_lt_length_of_mem hMem
  have hple : instrs.idxOf producer ≤ instrs.length := Nat.le_of_lt hp_lt
  have hTakeBound : ∀ x, x ∈ instrs.take (instrs.idxOf producer) → rc x ≥ v := by
    intro x hx
    have hxMem : x ∈ instrs := List.take_subset _ _ hx
    have hIdx := idxOf_lt_of_mem_take instrs _ x hNodup hx
    have := hMono x producer hxMem hMem hIdx
    omega
  have hDropBound : ∀ x, x ∈ instrs.drop (instrs.idxOf producer) → rc x ≥ v - 1 := by
    intro x hx
    have hxMem : x ∈ instrs := List.drop_subset _ _ hx
    have := hBound producer x hMem hxMem
    omega
  have hSumSplit := foldl_add_append (instrs.take (instrs.idxOf producer))
      (instrs.drop (instrs.idxOf producer)) rc
  rw [List.take_append_drop] at hSumSplit
  have hTakeLen : (instrs.take (instrs.idxOf producer)).length = instrs.idxOf producer := by
    simp [Nat.min_eq_left hple]
  have hDropLen : (instrs.drop (instrs.idxOf producer)).length = instrs.length - instrs.idxOf producer := by
    simp
  have hTakeSum := foldl_sum_ge_of_all_ge (instrs.take (instrs.idxOf producer)) rc v hTakeBound
  rw [hTakeLen] at hTakeSum
  have hDropSum := foldl_sum_ge_of_all_ge (instrs.drop (instrs.idxOf producer)) rc (v - 1) hDropBound
  rw [hDropLen] at hDropSum
  have hDropNe : instrs.drop (instrs.idxOf producer) ≠ [] := by
    intro h; simp at h; omega
  obtain ⟨hd, tl, hDropEq⟩ := List.exists_cons_of_ne_nil hDropNe
  have hHdProd : hd = producer := by
    have h1 : (instrs.drop (instrs.idxOf producer))[0]? = some hd := by
      rw [hDropEq]; simp
    simp [List.getElem?_drop] at h1
    have h2 : instrs[instrs.idxOf producer]? = some producer := by
      simp [List.getElem?_eq_getElem hp_lt, List.getElem_idxOf hp_lt]
    rw [h2] at h1; exact (Option.some.inj h1).symm
  subst hHdProd
  have hDropSumSplit : (instrs.drop (instrs.idxOf hd)).foldl (fun acc i => acc + rc i) 0 =
      rc hd + tl.foldl (fun acc i => acc + rc i) 0 := by
    rw [hDropEq, List.foldl_cons, foldl_add_shift]; omega
  have hTlBound : ∀ x, x ∈ tl → rc x ≥ v - 1 :=
    fun x hx => hDropBound x (hDropEq ▸ List.Mem.tail _ hx)
  have hTlLen : tl.length = instrs.length - instrs.idxOf hd - 1 := by
    have := hDropLen; rw [hDropEq, List.length_cons] at this; omega
  have hTlSum := foldl_sum_ge_of_all_ge tl rc (v - 1) hTlBound
  rw [hTlLen] at hTlSum
  rw [hSumSplit, hDropSumSplit]
  have hCombine : instrs.idxOf hd * (v - 1) + (instrs.length - instrs.idxOf hd - 1) * (v - 1) =
      (instrs.length - 1) * (v - 1) := by
    rw [← Nat.add_mul]; congr 1; omega
  have hFinal : (instrs.length - 1) * (v - 1) + instrs.idxOf hd + v =
      instrs.length * (v - 1) + (instrs.idxOf hd + 1) := by
    cases hN : instrs.length with
    | zero => omega
    | succ n =>
      simp only [Nat.succ_sub_one]
      rw [Nat.succ_mul]; omega
  have hvm : v = (v - 1) + 1 := by omega
  have hTakeSum' : List.foldl (fun acc i => acc + rc i) 0 (instrs.take (instrs.idxOf hd)) ≥
      instrs.idxOf hd * (v - 1) + instrs.idxOf hd := by
    rw [hvm] at hTakeSum; omega
  omega

/-! ## perScope_forward_issue_sema_ge: the key forward-direction bound -/

theorem perScope_forward_issue_sema_ge (spec : Program) (impl : ImplProgram) (alloc : PerScopeAllocR spec impl)
    (e : EngineId) (instr : DataPathInstrId) (ss : SpecState) (is : ImplState)
    (hSema : perScopeSemaInv spec alloc ss is)
    (hDeps : depSatisfied spec (spec.depGraph instr) instr ss e = true)
    (hWfAt : AllocatableAt spec ss e instr)
    (hWf : Allocatable spec)
    (_hSpecInv : SpecInv spec ss)
    (hLoopRegs : ∀ plid, is.registers e (alloc.monotoneReg e plid) = totalEntries ss e plid)
    (hTripRegs : ∀ lid, is.registers e (alloc.tripReg e lid) = tripEntries ss e spec.body lid)
    (hInv5 : ∀ eng, eng ∈ spec.engines → ∀ loop, RCMono spec ss eng loop)
    (hInv6 : ∀ eng, eng ∈ spec.engines → ∀ loop, RCBound spec ss eng loop)
    (hUI : UniqueInstrIds spec.engines spec.body)
    (hUS : UniqueScopeIds spec.body)
    : is.semaphores (impl.waitOf instr) ≥
        foldRegOps (impl.regOps e instr)
          (fun r => if r = alloc.waitReg e then 0 else is.registers e r)
          (alloc.waitReg e) := by
  rw [alloc.regOpsEq]
  let baseRegs := fun r => if r = alloc.waitReg e then 0 else is.registers e r
  have hInnerDst : ∀ op ∈ perScopeExpectedRegOps spec (alloc.waitReg e) alloc.monotoneReg e instr,
      op.1 = alloc.waitReg e := by
    intro ⟨d, s, tr⟩ hMem
    obtain ⟨idx, hGet⟩ := List.mem_iff_getElem?.mp hMem
    exact perScope_innerRegOpsDstWaitReg spec impl alloc e instr idx d s tr hGet
  have hDecomp := foldRegOps_wrapWithGate_waitReg (spec := spec) (consumer := instr) (e := e)
    (alloc.noClob_gate_wait e) hInnerDst
    (perScope_innerRegOpsSrcNeGate spec impl alloc e instr)
    (fun sid => Ne.symm (alloc.noClob_trip_wait e sid))
    (perScope_innerRegOpsFirstSafe spec impl alloc e instr)
    (perScopeExpectedRegOps_nonEmpty spec (alloc.waitReg e) alloc.monotoneReg e instr)
    (regs := baseRegs)
  have hBaseLoop : ∀ plid, baseRegs (alloc.monotoneReg e plid) = totalEntries ss e plid := by
    intro plid; simp only [baseRegs]; rw [if_neg (Ne.symm (alloc.noClob e plid))]; exact hLoopRegs plid
  have hInnerEq := foldRegOps_perScopeExpectedRegOps_waitReg (ab := alloc.toAllocBase)
    (spec := spec) (ss := ss) (e := e) (instr := instr) baseRegs
    (by simp [baseRegs]) hBaseLoop
  -- Helper for perScope_upper_bound result conversion: N*(v-1)+K = v*N - (N-K)
  have hArith : ∀ N K v : Nat, K ≤ N → v ≥ 1 →
      N * (v - 1) + K = v * N - (N - K) := by
    intro N K v hKN hv; rw [Nat.mul_comm]; cases v with | zero => omega | succ n => simp [Nat.succ_mul]; omega
  -- Helper: derive prodEng membership
  have hPEM_of : ∀ p k, spec.depGraph instr = .dep p k →
      (instrEngine spec.engines spec.body p).getD 0 ∈ spec.engines := by
    intro p k hD; have hWfI := hWf instr; unfold Allocatable at hWfI; simp [hD] at hWfI
    have hNe := instrEngine_ne_none_of_instrInBody hWfI.1
    obtain ⟨eng, hIE⟩ := Option.ne_none_iff_exists'.mp hNe
    simp [hIE]; exact instrEngine_mem_engines hIE
  -- Helper: derive producer ∈ scopeInstrs
  have hMP_of : ∀ p k loop, spec.depGraph instr = .dep p k →
      innermostParentScope spec.engines spec.body p = loop →
      p ∈ scopeInstrs spec.engines ((instrEngine spec.engines spec.body p).getD 0) spec.body loop := by
    intro p k loop hD hPS; have hWfI := hWf instr; unfold Allocatable at hWfI; simp [hD] at hWfI
    have hIE := instrEngine_ne_none_of_instrInBody hWfI.1
    obtain ⟨eng, hEng⟩ := Option.ne_none_iff_exists'.mp hIE
    simp [hEng]; exact mem_scopeInstrs_of_loop_engine hUI hUS (instrEngine_mem_engines hEng) hPS hEng
  match hDep : spec.depGraph instr with
  | .none =>
    simp only [hDep] at hDecomp; rw [hDecomp, hInnerEq]
    simp [perScopeExpectedWaitVal, hDep]
  | .dep producer offset =>
    simp only [hDep] at hDecomp
    -- Helper: scopeRetireSum >= v*N - (N-K) from perScope_upper_bound
    have hSumBound : ∀ loop v, v ≥ 1 →
        (instrEngine spec.engines spec.body producer).getD 0 ∈ spec.engines →
        producer ∈ scopeInstrs spec.engines ((instrEngine spec.engines spec.body producer).getD 0) spec.body loop →
        ss.rc producer ≥ v →
        scopeRetireSum ss.rc spec.engines ((instrEngine spec.engines spec.body producer).getD 0) spec.body loop ≥
          v * (scopeInstrs spec.engines ((instrEngine spec.engines spec.body producer).getD 0) spec.body loop).length -
          ((scopeInstrs spec.engines ((instrEngine spec.engines spec.body producer).getD 0) spec.body loop).length -
          (List.idxOf producer (scopeInstrs spec.engines ((instrEngine spec.engines spec.body producer).getD 0) spec.body loop) + 1)) := by
      intro loop v hv hPEM' hMP hRC
      have hSum := perScope_upper_bound _ ss.rc
        (scopeInstrs_nodup hUI hPEM') (hInv5 _ hPEM' loop) (hInv6 _ hPEM' loop)
        producer hMP v hRC hv
      have hKleN := List.idxOf_lt_length_of_mem hMP
      change scopeRetireSum _ _ _ _ _ ≥ _; unfold scopeRetireSum
      rw [← hArith _ _ v (by omega) hv]; exact hSum
    have hPEM := hPEM_of producer offset hDep
    match hSS : innermostSharedScope spec.engines spec.body producer instr with
    | some sid =>
      simp only [hSS] at hDecomp
      have hBaseRes : baseRegs (alloc.tripReg e sid) = tripEntries ss e spec.body sid := by
        simp only [baseRegs]; rw [if_neg (Ne.symm (alloc.noClob_trip_wait e sid))]; exact hTripRegs sid
      rw [hBaseRes] at hDecomp
      by_cases hVac : tripEntries ss e spec.body sid ≤ offset
      · -- gate = 0: fold result is 0
        simp only [show ¬(tripEntries ss e spec.body sid > offset) from by omega, ite_false, Nat.zero_mul] at hDecomp
        rw [hDecomp]; exact Nat.zero_le _
      · -- gate = 1: fold result = perScopeExpectedWaitVal
        simp only [show tripEntries ss e spec.body sid > offset from by omega, ite_true, Nat.one_mul] at hDecomp
        rw [hDecomp, hInnerEq]
        obtain ⟨plid, hPL⟩ := innermostParentScope_of_sharedLoop hSS
        simp only [perScopeExpectedWaitVal, hDep, hPL, hSS]
        have hWS : impl.waitOf instr = alloc.perScopeSema (some plid) ((instrEngine spec.engines spec.body producer).getD 0) := by
          rw [alloc.waitOfEq]; simp [depProducer, hDep, hPL]
        rw [hWS, hSema (some plid) _ hPEM]
        -- Simplify depSatisfied and AllocatableAt with hSS, hPL
        simp only [depSatisfied, hDep, hPL, hSS, Bool.or_eq_true, decide_eq_true_eq] at hDeps
        simp only [AllocatableAt, hDep, hPL, hSS] at hWfAt
        have hMP := hMP_of producer offset (some plid) hDep hPL
        by_cases hEq : some sid = some plid
        · -- shared = parent (sid = plid)
          have hSP : sid = plid := Option.some.inj hEq
          subst hSP
          simp only [ite_true] at hWfAt hDeps ⊢
          rcases hDeps with hVacD | hRC
          · exact absurd hVacD hVac
          · rw [hWfAt] at hRC
            rcases Nat.eq_zero_or_pos (totalEntries ss e sid - offset) with hv0 | hvpos
            · -- v = 0: result is 0 * N - ... which under Nat is 0
              simp [hv0]
            · exact hSumBound (some sid) (totalEntries ss e sid - offset) hvpos hPEM hMP (by omega)
        · -- shared ≠ parent
          simp only [show ¬((some sid : Option ScopeId) = some plid) from hEq, ite_false] at hWfAt hDeps ⊢
          rcases hDeps with hVacD | hRC
          · exact absurd hVacD hVac
          · rw [hWfAt] at hRC
            rcases Nat.eq_zero_or_pos (totalEntries ss e plid) with hv0 | hvpos
            · simp [hv0]
            · exact hSumBound (some plid) (totalEntries ss e plid) hvpos hPEM hMP (by omega)
    | none =>
      simp only [hSS] at hDecomp; rw [hDecomp, hInnerEq]
      simp only [perScopeExpectedWaitVal, hDep]
      match hPL : innermostParentScope spec.engines spec.body producer with
      | none =>
        simp only
        have hWS : impl.waitOf instr = alloc.perScopeSema none ((instrEngine spec.engines spec.body producer).getD 0) := by
          rw [alloc.waitOfEq]; simp [depProducer, hDep, hPL]
        rw [hWS, hSema none _ hPEM]
        have hMP := hMP_of producer offset none hDep hPL
        simp only [depSatisfied, hDep, hPL, hSS, totalEntriesOpt,
          Bool.or_eq_true, decide_eq_true_eq] at hDeps
        by_cases hOffset : offset = 0
        · subst offset
          have hRC : ss.rc producer ≥ 1 := by
            rcases hDeps with hVac | hMain
            · omega
            · exact hMain
          have hSum := perScope_upper_bound _ ss.rc
            (scopeInstrs_nodup hUI hPEM) (hInv5 _ hPEM none) (hInv6 _ hPEM none)
            producer hMP 1 hRC (by omega)
          have hKleN := List.idxOf_lt_length_of_mem hMP
          change scopeRetireSum _ _ _ _ _ ≥ _
          unfold scopeRetireSum
          simp only [Nat.sub_zero, Nat.one_mul]
          omega
        · have hOffsetPos : 1 ≤ offset := by omega
          simp [Nat.sub_eq_zero_of_le hOffsetPos]
      | some plid =>
        simp only [hSS]
        have hWS : impl.waitOf instr = alloc.perScopeSema (some plid) ((instrEngine spec.engines spec.body producer).getD 0) := by
          rw [alloc.waitOfEq]; simp [depProducer, hDep, hPL]
        rw [hWS, hSema (some plid) _ hPEM]
        have hMP := hMP_of producer offset (some plid) hDep hPL
        simp only [depSatisfied, hDep, hPL, hSS, Bool.or_eq_true, decide_eq_true_eq] at hDeps
        simp only [AllocatableAt, hDep, hPL, hSS, show (none : Option ScopeId) = some plid ↔ False from by simp, ite_false] at hWfAt
        rcases hDeps with hVacDeps | hRCDeps
        · -- vacuous: 1 ≤ offset. Allocatable forces offset = 1 → totalEntries = 0 → result = 0.
          have hWfI := hWf instr; unfold Allocatable at hWfI; simp [hDep, hPL] at hWfI
          obtain ⟨_, hWfI2⟩ := hWfI
          rcases hWfI2 with hPI | ⟨_, hOff0⟩ | ⟨_, hOff1⟩
          · rw [hSS] at hPI; simp at hPI
          · omega -- offset = 0 contradicts 1 ≤ offset
          · -- offset = 1
            simp only [hOff1, totalEntriesOpt, show 1 - 1 = 0 from rfl] at hWfAt
            simp [cumExecs] at hWfAt
            -- totalEntries plid = 0
            simp only [show (none : Option ScopeId) ≠ some plid from nofun, ite_false]
            rw [← hWfAt]; simp
        · rw [hWfAt] at hRCDeps
          simp only [show (none : Option ScopeId) ≠ some plid from nofun, ite_false]
          rcases Nat.eq_zero_or_pos (totalEntries ss e plid) with hv0 | hvpos
          · simp only [hv0, Nat.zero_mul, Nat.zero_sub]; exact Nat.zero_le _
          · exact hSumBound (some plid) (totalEntries ss e plid) hvpos hPEM hMP (by omega)

/-! ## perScope_forward_sim_step: single-step forward simulation for per-loop allocation

Uses perScopeSemaInv (not a bundled invariant) as the MatchStates SemaInv.
SpecInv and PerScopeInv are threaded as separate hypotheses.
For issue: uses perScope_case_issue (copy of ForwardSim.case_issue with direct PerScopeInv access).
For retire: inline proof using hSpecInv.inflightInBody directly.
For all other cases: uses generic ForwardSim.case_* with perScope_semaInv_mono.
-/

theorem perScope_forward_sim_step (spec : Program) (impl : ImplProgram) (alloc : PerScopeAllocR spec impl)
    (e : EngineId) (ss ss' : SpecState) (is : ImplState)
    (hSim : MatchStates spec impl alloc.toAllocBase (perScopeSemaInv spec alloc) ss is)
    (hInv : ImplInv impl is) (hNARO : NotAtRegOp is)
    (hWf : Allocatable spec) (hSpecInv : SpecInv spec ss)
    (hUniq : UniqueScopeIds spec.body) (hUniqueInstr : UniqueInstrIds spec.engines spec.body)
    (hEngines : e ∈ spec.engines)
    (hPerScopeInv : PerScopeInv spec impl alloc ss is)
    (hStep : SpecStep spec e ss ss')
    : ∃ is', ImplPlusAny impl is is'
        ∧ MatchStates spec impl alloc.toAllocBase (perScopeSemaInv spec alloc) ss' is'
        ∧ NotAtRegOp is' := by
  have hImplE : e ∈ impl.engines := congrArg ProgramBase.engines alloc.baseEq ▸ hEngines
  cases hStep with
  | commit hE idx instr hIdx =>
    exact ForwardSim.case_commit spec impl alloc.toAllocBase
      (perScopeSemaInv spec alloc) (perScope_semaInv_mono spec impl alloc)
      e ss is hSim hNARO hImplE idx instr hIdx
  | retire hE instr inflightRest hHead =>
    have hSpecHead : ss.inflight e = (instr, Phase.committed) :: inflightRest := hHead
    have hInBody : instrInBody spec.engines spec.body instr = true :=
      hSpecInv.inflightInBody e instr Phase.committed (by rw [hSpecHead]; exact List.Mem.head _)
    have hSemaPost := perScope_retire_semaInv spec impl alloc e instr inflightRest ss is
      hUniqueInstr hUniq hSim.semaInv hInBody hSpecHead
    obtain ⟨hDataPath, hInflight, hControl, hSema, hLoopRegInv, hTripRegInv, hRegOpFold, hPC, hWaitChain, hGateChain⟩ := hSim
    have hImplHead : is.inflight e = (instr, Phase.committed) :: inflightRest := by rw [hInflight]; exact hSpecHead
    refine ⟨_, ImplPlusAny.step (ImplStep.retire e is hImplE instr inflightRest hImplHead) ImplStarAny.refl, ?_, ?_⟩
    · exact { dataPathEq := hDataPath
              inflightEq := by intro e'; simp only [funUpdate]; split <;> simp [hInflight]
              controlEq := hControl
              semaInv := hSemaPost
              monotoneRegInv := by
                intro e' lid hNALS; simp [totalEntries]
                exact hLoopRegInv e' lid (fun h => hNALS h)
              tripRegInv := by
                intro e' lid hNALS_all; simp [tripEntries]
                exact hTripRegInv e' lid hNALS_all
              regOpFold := by
                intro e' fr r ops hStack hStmt
                have ⟨h1, h2⟩ := hRegOpFold e' fr r ops hStack hStmt
                exact ⟨fun lid => by simp [totalEntries]; exact h1 lid,
                       fun lid => by simp [tripEntries, totalEntries]; exact h2 lid⟩
              pcCorr := hPC
              waitRegChain := hWaitChain
              gateRegChain := hGateChain }
    · exact hNARO
  | blockDone hE frame rest f hStack hStmt hDone =>
    exact ForwardSim.case_blockDone spec impl alloc.toAllocBase
      (perScopeSemaInv spec alloc) (perScope_semaInv_mono spec impl alloc)
      e ss is hSim hNARO hImplE frame rest f hStack hStmt hDone
  | loopEnter hE frame rest lid loopBody hStack hStmt hGuard =>
    have hPIO : ∀ parent, scopeParent spec.body lid = some parent →
        parent ∈ enclosingLoopsFromStack (frame :: rest) := by
      intro parent hP
      have hSMP := hSpecInv.wellFormedPC e; rw [hStack] at hSMP
      have hUniqBody := smp_uniqueScopeIds hSMP hUniq frame (List.Mem.head _)
      have hMem : lid ∈ scopeIdsOf frame.body := mem_scopeIdsOf_of_getElem hStmt (by simp [scopeIdsOf])
      cases hk : frame.kind with
      | top =>
        have hBodyEq : frame.body = spec.body := by
          cases hSMP with | base => rfl | loop => simp at hk | cond _ _ _ _ _ _ _ _ taken => cases taken <;> simp at hk
        have hGoEq : scopeParent.go frame.body lid none = none :=
          scopeParent_go_of_direct_loop (container := none) hStmt hUniqBody
        rw [scopeParent] at hP; rw [hBodyEq] at hGoEq; rw [hGoEq] at hP; simp at hP
      | loop plid =>
        have hGoEq : scopeParent.go frame.body lid frame.kind.loopId? = some plid := by
          simp [hk]; exact scopeParent_go_of_direct_loop (container := some plid) hStmt hUniqBody
        have hLift := smp_lift_scopeParent_go hSMP hUniq frame rest rfl hGoEq hMem
        rw [scopeParent] at hP; rw [hLift] at hP; simp at hP; subst hP
        simp [enclosingLoopsFromStack, hk]
      | cond cid =>
        have hGoEq : scopeParent.go frame.body lid frame.kind.loopId? = some cid := by
          simp [hk]; exact scopeParent_go_of_direct_loop (container := some cid) hStmt hUniqBody
        have hLift := smp_lift_scopeParent_go hSMP hUniq frame rest rfl hGoEq hMem
        rw [scopeParent] at hP; rw [hLift] at hP; simp at hP; subst hP
        simp [enclosingLoopsFromStack, hk]
    have hNSP : ∀ parent, scopeParent spec.body lid = some parent → parent ≠ lid :=
      fun _ hP => scopeParent_ne_self hUniq hP
    exact ForwardSim.case_loopEnter spec impl alloc.toAllocBase
      (perScopeSemaInv spec alloc) (perScope_semaInv_mono spec impl alloc)
      e ss is hSim hNARO hImplE hSpecInv hUniq
      frame rest lid loopBody hStack hStmt hGuard hPIO hNSP
  | loopSkip hE frame rest lid loopBody hStack hStmt hGuard =>
    exact ForwardSim.case_loopSkip spec impl alloc.toAllocBase
      (perScopeSemaInv spec alloc) (perScope_semaInv_mono spec impl alloc)
      e ss is hSim hNARO hImplE frame rest lid loopBody hStack hStmt hGuard
  | loopBack hE frame parent rest lid hStack hKind hEnd =>
    exact ForwardSim.case_loopBack spec impl alloc.toAllocBase
      (perScopeSemaInv spec alloc) (perScope_semaInv_mono spec impl alloc)
      e ss is hSim hNARO hImplE frame parent rest lid hStack hKind hEnd
  | condTrue hE frame rest thenId elseId thenBody elseBody hStack hStmt hGuard =>
    have hPIO : ∀ parent, scopeParent spec.body thenId = some parent →
        parent ∈ enclosingLoopsFromStack (frame :: rest) := by
      intro parent hP
      have hSMP := hSpecInv.wellFormedPC e; rw [hStack] at hSMP
      have hUniqBody := smp_uniqueScopeIds hSMP hUniq frame (List.Mem.head _)
      have hMem : thenId ∈ scopeIdsOf frame.body := mem_scopeIdsOf_of_getElem hStmt (by simp [scopeIdsOf])
      cases hk : frame.kind with
      | top =>
        have hBodyEq : frame.body = spec.body := by
          cases hSMP with | base => rfl | loop => simp at hk | cond _ _ _ _ _ _ _ _ taken => cases taken <;> simp at hk
        have hGoEq : scopeParent.go frame.body thenId none = none :=
          scopeParent_go_of_direct_cond_then (container := none) hStmt hUniqBody
        rw [scopeParent] at hP; rw [hBodyEq] at hGoEq; rw [hGoEq] at hP; simp at hP
      | loop plid =>
        have hGoEq : scopeParent.go frame.body thenId frame.kind.loopId? = some plid := by
          simp [hk]; exact scopeParent_go_of_direct_cond_then (container := some plid) hStmt hUniqBody
        have hLift := smp_lift_scopeParent_go hSMP hUniq frame rest rfl hGoEq hMem
        rw [scopeParent] at hP; rw [hLift] at hP; simp at hP; subst hP
        simp [enclosingLoopsFromStack, hk]
      | cond cid =>
        have hGoEq : scopeParent.go frame.body thenId frame.kind.loopId? = some cid := by
          simp [hk]; exact scopeParent_go_of_direct_cond_then (container := some cid) hStmt hUniqBody
        have hLift := smp_lift_scopeParent_go hSMP hUniq frame rest rfl hGoEq hMem
        rw [scopeParent] at hP; rw [hLift] at hP; simp at hP; subst hP
        simp [enclosingLoopsFromStack, hk]
    have hNSP : ∀ parent, scopeParent spec.body thenId = some parent → parent ≠ thenId :=
      fun _ hP => scopeParent_ne_self hUniq hP
    exact ForwardSim.case_condTrue spec impl alloc.toAllocBase
      (perScopeSemaInv spec alloc) (perScope_semaInv_mono spec impl alloc)
      e ss is hSim hNARO hImplE hSpecInv hUniq
      frame rest thenId elseId thenBody elseBody hStack hStmt hGuard hPIO hNSP
  | condFalse hE frame rest thenId elseId thenBody elseBody hStack hStmt hGuard =>
    have hPIO : ∀ parent, scopeParent spec.body elseId = some parent →
        parent ∈ enclosingLoopsFromStack (frame :: rest) := by
      intro parent hP
      have hSMP := hSpecInv.wellFormedPC e; rw [hStack] at hSMP
      have hUniqBody := smp_uniqueScopeIds hSMP hUniq frame (List.Mem.head _)
      have hMem : elseId ∈ scopeIdsOf frame.body := mem_scopeIdsOf_of_getElem hStmt (by simp [scopeIdsOf])
      cases hk : frame.kind with
      | top =>
        have hBodyEq : frame.body = spec.body := by
          cases hSMP with | base => rfl | loop => simp at hk | cond _ _ _ _ _ _ _ _ taken => cases taken <;> simp at hk
        have hGoEq : scopeParent.go frame.body elseId none = none :=
          scopeParent_go_of_direct_cond_else (container := none) hStmt hUniqBody
        rw [scopeParent] at hP; rw [hBodyEq] at hGoEq; rw [hGoEq] at hP; simp at hP
      | loop plid =>
        have hGoEq : scopeParent.go frame.body elseId frame.kind.loopId? = some plid := by
          simp [hk]; exact scopeParent_go_of_direct_cond_else (container := some plid) hStmt hUniqBody
        have hLift := smp_lift_scopeParent_go hSMP hUniq frame rest rfl hGoEq hMem
        rw [scopeParent] at hP; rw [hLift] at hP; simp at hP; subst hP
        simp [enclosingLoopsFromStack, hk]
      | cond cid =>
        have hGoEq : scopeParent.go frame.body elseId frame.kind.loopId? = some cid := by
          simp [hk]; exact scopeParent_go_of_direct_cond_else (container := some cid) hStmt hUniqBody
        have hLift := smp_lift_scopeParent_go hSMP hUniq frame rest rfl hGoEq hMem
        rw [scopeParent] at hP; rw [hLift] at hP; simp at hP; subst hP
        simp [enclosingLoopsFromStack, hk]
    have hNSP : ∀ parent, scopeParent spec.body elseId = some parent → parent ≠ elseId :=
      fun _ hP => scopeParent_ne_self hUniq hP
    exact ForwardSim.case_condFalse spec impl alloc.toAllocBase
      (perScopeSemaInv spec alloc) (perScope_semaInv_mono spec impl alloc)
      e ss is hSim hNARO hImplE hSpecInv hUniq
      frame rest thenId elseId thenBody elseBody hStack hStmt hGuard hPIO hNSP
  | condDone hE frame parent rest sid hStack hKind hEnd =>
    exact ForwardSim.case_condDone spec impl alloc.toAllocBase
      (perScopeSemaInv spec alloc) (perScope_semaInv_mono spec impl alloc)
      e ss is hSim hNARO hImplE frame parent rest sid hStack hKind hEnd
  | issue hE frame rest f instr hStack hStmt hInstr hDeps =>
    exact ForwardSim.case_issue spec impl alloc.toAllocBase
      (perScopeSemaInv spec alloc)
      (perScope_semaInv_mono spec impl alloc)
      (fun e i => perScopeExpectedRegOps spec (alloc.waitReg e) alloc.monotoneReg e i)
      ⟨perScope_innerRegOpsFirstSafe spec impl alloc,
       fun e i => perScopeExpectedRegOps_nonEmpty spec (alloc.waitReg e) alloc.monotoneReg e i,
       perScope_innerRegOpsDstWaitReg spec impl alloc⟩
      alloc.regOpsEq
      e ss is hSim hInv hNARO hWf hSpecInv hUniq hUniqueInstr hEngines
      frame rest f instr hStack hStmt hInstr hDeps
      (fun is' hSI hSR hRR =>
        perScope_forward_issue_sema_ge spec impl alloc e instr ss is' hSI hDeps
          (allocatableAt_of_block_instr spec ss e instr hWf hSpecInv hUniq hUniqueInstr hEngines
            frame rest f hStack hStmt hInstr)
          hWf hSpecInv hSR hRR
          (fun eng hEM loop => hPerScopeInv.rcMono eng loop hEM)
          (fun eng hEM loop => hPerScopeInv.rcBound eng loop hEM) hUniqueInstr hUniq)

/-! ## perScope_forward_sim_star: star closure threading PerScopeInv -/

theorem perScope_forward_sim_star (spec : Program) (impl : ImplProgram) (alloc : PerScopeAllocR spec impl)
    (ss ss' : SpecState) (is : ImplState)
    (hSim : MatchStates spec impl alloc.toAllocBase (perScopeSemaInv spec alloc) ss is)
    (hInv : ImplInv impl is) (hNARO : NotAtRegOp is)
    (hWf : Allocatable spec) (hSpecInv : SpecInv spec ss)
    (hUniq : UniqueScopeIds spec.body) (hUniqueInstr : UniqueInstrIds spec.engines spec.body)
    (hPerScopeInv : PerScopeInv spec impl alloc ss is)
    (hSteps : SpecStar spec ss ss')
    : ∃ is', ImplStarAny impl is is'
        ∧ MatchStates spec impl alloc.toAllocBase (perScopeSemaInv spec alloc) ss' is' := by
  induction hSteps generalizing is with
  | refl => exact ⟨is, ImplStarAny.refl, hSim⟩
  | @step s s_mid s_final hStep hStar ih =>
    obtain ⟨e, hStep⟩ := hStep
    obtain ⟨is₁, hImplStar, hSim₁, hNARO₁⟩ := perScope_forward_sim_step spec impl alloc e s s_mid is
      hSim hInv hNARO hWf hSpecInv hUniq hUniqueInstr hStep.mem_engines hPerScopeInv hStep
    have hSpecInvMid := specInv_step spec e s s_mid hUniq hSpecInv hStep
    have hInv₁ := implInv_starAny impl is is₁ hInv hImplStar.to_star
    have hPerScopeGoal := perScopeInv_spec_step spec impl alloc e s s_mid hStep hPerScopeInv hSpecInv hUniqueInstr hUniq
    have hPerScopeInv₁ : PerScopeInv spec impl alloc s_mid is₁ := {
      semaInv := hSim₁.semaInv
      countBalance := hPerScopeGoal.1
      issueOrder := hPerScopeGoal.2.1
      queueOrdered := hPerScopeGoal.2.2.1
      rcMono := hPerScopeGoal.2.2.2.1
      rcBound := hPerScopeGoal.2.2.2.2.1
      pcComplete := hPerScopeGoal.2.2.2.2.2.1
      instrAtPC_atTm1 := hPerScopeGoal.2.2.2.2.2.2
    }
    obtain ⟨is₂, hImplStar₂, hSim₂⟩ := ih is₁ hSim₁ hInv₁ hNARO₁ hSpecInvMid hPerScopeInv₁
    exact ⟨is₂, (hImplStar.to_star).trans hImplStar₂, hSim₂⟩

/-! ## drain_all_regOps: finish any pending loop-entry register ops

If some engine is mid-regOp (atRegOp holds on its top frame), finish those ops
via impl-only steps to reach a NotAtRegOp state. The spec state is unchanged.
MatchStates and ImplInv are preserved because:
- MatchStates.regOpFold guarantees what the registers will be after completing the ops
- stmtRegOpSteps_to_done executes them
- The resulting stmtIdx=1 state satisfies all MatchStates fields

If already NotAtRegOp, this is zero impl steps. -/
theorem drain_all_regOps (spec : Program) (impl : ImplProgram) (alloc : PerScopeAllocR spec impl)
    (ss : SpecState) (is : ImplState)
    (hSim : MatchStates spec impl alloc.toAllocBase (perScopeSemaInv spec alloc) ss is)
    (hImplInv : ImplInv impl is)
    (hPerScopeInv : PerScopeInv spec impl alloc ss is)
    : ∃ is', ImplStarAny impl is is' ∧
        MatchStates spec impl alloc.toAllocBase (perScopeSemaInv spec alloc) ss is' ∧
        ImplInv impl is' ∧
        NotAtRegOp is' ∧
        PerScopeInv spec impl alloc ss is' := by
  suffices h : ∀ (engines : List EngineId) (is : ImplState),
      (∀ e, e ∈ engines → e ∈ impl.engines) →
      MatchStates spec impl alloc.toAllocBase (perScopeSemaInv spec alloc) ss is →
      ImplInv impl is →
      PerScopeInv spec impl alloc ss is →
      (∀ e frame rest, e ∉ engines → (is.pc e).stack = frame :: rest → ¬ atRegOp frame) →
      ∃ is', ImplStarAny impl is is' ∧
        MatchStates spec impl alloc.toAllocBase (perScopeSemaInv spec alloc) ss is' ∧
        ImplInv impl is' ∧ NotAtRegOp is' ∧ PerScopeInv spec impl alloc ss is' by
    exact h impl.engines is (fun _ hm => hm) hSim hImplInv hPerScopeInv (fun e frame rest hNotMem hStack hAR => by
      have hTop := hImplInv.topKindOnly e hNotMem frame rest hStack
      simp [atRegOp, hTop] at hAR)
  intro engines; induction engines with
  | nil =>
    intro is _ hSim hImplInv hPerScopeInv hNotInList
    exact ⟨is, .refl, hSim, hImplInv, fun e frame rest hStack =>
      hNotInList e frame rest (fun h => nomatch h) hStack, hPerScopeInv⟩
  | cons e es ih =>
    intro is hSub hSim hImplInv hPerScopeInv hNotInList
    by_cases hAR : ∃ frame rest, (is.pc e).stack = frame :: rest ∧ atRegOp frame
    · obtain ⟨frame, rest, hStack, hAtRegOp⟩ := hAR
      obtain ⟨sf, srest, hSpecStack, hFrameCorr, hRestCorr, hCovS, hCovI, hNoRegOp⟩ :=
        pcCorr_stack_cons (hSim.pcCorr e) hStack
      obtain ⟨hKC, ⟨implBody, hBM, hBE⟩, hIC⟩ := hFrameCorr
      have hStmtIdx : frame.stmtIdx = 0 := by
        simp [atRegOp] at hAtRegOp
        cases hk : frame.kind <;> simp [hk] at hAtRegOp <;> exact hAtRegOp
      have hOps : ∃ ops, frame.body[frame.stmtIdx]? = some (.regOp ops) := by
        cases hk : frame.kind with
        | loop lid => rw [hk] at hBE; simp at hBE; rw [hBE, hStmtIdx]; exact ⟨_, rfl⟩
        | cond sid => rw [hk] at hBE; simp at hBE; rw [hBE, hStmtIdx]; exact ⟨_, rfl⟩
        | top => simp [atRegOp, hk] at hAtRegOp
      obtain ⟨ops, hStmt⟩ := hOps
      have hFold := hSim.regOpFold e frame rest ops hStack hStmt
      have hBound : (is.pc e).stmtRegOpIdx ≤ (ops e).length :=
        hImplInv.stmtRegOpBound e frame rest ops hStack hStmt
      obtain ⟨is₁, hStar₁, hStack₁, hInstr₁, hRegOp₁, hSROI₁, hPC₁, hInfl₁, hSema₁,
              hDataPath₁, hControl₁, hRegs₁, hRegsE₁⟩ :=
        @stmtRegOpSteps_from impl e is (hSub e (List.mem_cons_self ..))
          frame rest ops hStack hStmt hBound
      have hRO : atRegOp frame := hAtRegOp
      have hLoopRegsE : ∀ lid, is₁.registers e (alloc.toAllocBase.monotoneReg e lid) = totalEntries ss e lid := by
        intro lid'; rw [hRegsE₁]; exact hFold.1 lid'
      have hTripRegsE : ∀ lid, is₁.registers e (alloc.toAllocBase.tripReg e lid) =
          tripEntries ss e spec.body lid := by
        intro lid'; rw [hRegsE₁]; exact hFold.2 lid'
      have hSim₁ : MatchStates spec impl alloc.toAllocBase (perScopeSemaInv spec alloc) ss is₁ :=
        { dataPathEq := by rw [hDataPath₁, hSim.dataPathEq]
          inflightEq := by intro e'; rw [hInfl₁, hSim.inflightEq]
          controlEq := by intro e'; rw [hControl₁, hSim.controlEq]
          semaInv := perScope_semaInv_mono spec impl alloc ss ss is is₁ rfl hSema₁.symm hSim.semaInv
          monotoneRegInv := by
            intro e' lid' hNALS
            by_cases he : e' = e
            · subst he; exact hLoopRegsE lid'
            · rw [hRegs₁ e' he]; exact hSim.monotoneRegInv e' lid' (fun ⟨fr, r, hS, hK, hI⟩ =>
                hNALS ⟨fr, r, by rw [hPC₁ e' he]; exact hS, hK, hI⟩)
          tripRegInv := by
            intro e' lid' hNALS
            by_cases he : e' = e
            · subst he; exact hTripRegsE lid'
            · rw [hRegs₁ e' he]; exact hSim.tripRegInv e' lid' (fun lid'' ⟨fr, r, hS, hK, hI⟩ =>
                hNALS lid'' ⟨fr, r, by rw [hPC₁ e' he]; exact hS, hK, hI⟩)
          regOpFold := by
            intro e' frame' rest' ops' hStack' hStmt'
            by_cases he : e' = e
            · subst he; rw [hStack₁] at hStack'
              obtain ⟨rfl, rfl⟩ := List.cons.inj hStack'
              exfalso
              cases hk : frame.kind with
              | loop lid =>
                rw [hk] at hBE; simp at hBE; rw [hBE, hStmtIdx] at hStmt'
                simp [List.getElem?_cons_succ] at hStmt'; exact bodyMatch_no_regOp hBM hStmt'
              | cond sid =>
                rw [hk] at hBE; simp at hBE; rw [hBE, hStmtIdx] at hStmt'
                simp [List.getElem?_cons_succ] at hStmt'; exact bodyMatch_no_regOp hBM hStmt'
              | top => simp [atRegOp, hk] at hRO
            · rw [hPC₁ e' he] at hStack' ⊢; rw [hRegs₁ e' he]
              exact hSim.regOpFold e' frame' rest' ops' hStack' hStmt'
          pcCorr := by
            intro e'; by_cases he : e' = e
            · subst he
              have hNewFC : FrameCorr alloc.toAllocBase sf
                  ⟨frame.body, frame.stmtIdx + 1, frame.kind⟩ :=
                ⟨hKC, ⟨implBody, hBM, hBE⟩,
                 fun hRO' => by simp only [atRegOp] at hRO'; cases hk : frame.kind <;> simp [hk] at hRO',
                 fun _ => by
                    have ⟨_, hImfZ⟩ := hIC.1 hRO; rw [hImfZ]
                    cases hk : frame.kind with
                    | top => simp [atRegOp, hk] at hRO
                    | loop lid => simp; omega
                    | cond sid => simp; omega⟩
              constructor
              · rw [hSpecStack, hStack₁]
                exact StackCorr.cons _ _ srest rest hNewFC hRestCorr hCovS hCovI hNoRegOp
              · rw [hInstr₁]; exact (hSim.pcCorr _).instrEq
            · rw [hPC₁ e' he]; exact hSim.pcCorr e'
          waitRegChain := by
            intro e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
            by_cases he : e' = e
            · subst he; rw [hStack₁] at hStack'; obtain ⟨rfl, rfl⟩ := List.cons.inj hStack'
              rw [hRegOp₁] at hROI; omega
            · rw [hPC₁ e' he] at hStack' hInstr' hROI ⊢; rw [hRegs₁ e' he]
              exact hSim.waitRegChain e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
          gateRegChain := by
            intro e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
            by_cases he : e' = e
            · subst he; rw [hStack₁] at hStack'; obtain ⟨rfl, rfl⟩ := List.cons.inj hStack'
              rw [hRegOp₁] at hROI; omega
            · rw [hPC₁ e' he] at hStack' hInstr' hROI ⊢; rw [hRegs₁ e' he]
              exact hSim.gateRegChain e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI }
      have hImplInv₁ : ImplInv impl is₁ := implInv_star impl e is is₁ hImplInv hStar₁
      have hPerScopeInv₁ : PerScopeInv spec impl alloc ss is₁ := {
        semaInv := by intro s eng hE; rw [hSema₁]; exact hPerScopeInv.semaInv s eng hE
        countBalance := hPerScopeInv.countBalance
        issueOrder := hPerScopeInv.issueOrder
        queueOrdered := hPerScopeInv.queueOrdered
        rcMono := hPerScopeInv.rcMono
        rcBound := hPerScopeInv.rcBound
        pcComplete := hPerScopeInv.pcComplete
        instrAtPC_atTm1 := hPerScopeInv.instrAtPC_atTm1
      }
      have hDrainedE : ∀ frame' rest', (is₁.pc e).stack = frame' :: rest' → ¬ atRegOp frame' := by
        intro frame' rest' hStack'; rw [hStack₁] at hStack'
        obtain ⟨rfl, rfl⟩ := List.cons.inj hStack'
        simp [atRegOp]; cases hk : frame.kind <;> simp
      have hNotInList₁ : ∀ e' frame' rest', e' ∉ es → (is₁.pc e').stack = frame' :: rest' → ¬ atRegOp frame' := by
        intro e' frame' rest' hNotEs hStack'
        by_cases he : e' = e
        · subst he; exact hDrainedE frame' rest' hStack'
        · rw [hPC₁ e' he] at hStack'
          exact hNotInList e' frame' rest' (fun hMem => by
            cases List.eq_or_mem_of_mem_cons hMem with
            | inl h => exact absurd h he
            | inr h => exact absurd h hNotEs) hStack'
      obtain ⟨is₂, hStar₂, hSim₂, hImplInv₂, hNARO₂, hPerScopeInv₂⟩ :=
        ih is₁ (fun e' he' => hSub e' (List.mem_cons_of_mem _ he'))
          hSim₁ hImplInv₁ hPerScopeInv₁ hNotInList₁
      exact ⟨is₂, (ImplStar_to_ImplStarAny hStar₁).trans hStar₂,
             hSim₂, hImplInv₂, hNARO₂, hPerScopeInv₂⟩
    · have hAR' : ∀ frame rest, (is.pc e).stack = frame :: rest → ¬ atRegOp frame :=
        fun frame rest hStack hContra => hAR ⟨frame, rest, hStack, hContra⟩
      have hNotInList' : ∀ e' frame' rest', e' ∉ es → (is.pc e').stack = frame' :: rest' → ¬ atRegOp frame' := by
        intro e' frame' rest' hNotEs hStack'
        by_cases he : e' = e
        · subst he; exact hAR' frame' rest' hStack'
        · exact hNotInList e' frame' rest' (fun hMem => by
            cases List.eq_or_mem_of_mem_cons hMem with
            | inl h => exact absurd h he
            | inr h => exact absurd h hNotEs) hStack'
      exact ih is (fun e' he' => hSub e' (List.mem_cons_of_mem _ he'))
        hSim hImplInv hPerScopeInv hNotInList'
