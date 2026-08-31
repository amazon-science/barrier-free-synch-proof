import SemaAlloc.PerScopeLemmas
import SemaAlloc.BackwardSim

-- depSatisfied from perScopeSemaInv + PerScopeInv (Inv5/Inv6) at issue time.
-- Uses gate decomposition via foldRegOps_wrapWithGate_waitReg to convert wrapped ops
-- to inner result, then perScope_lower_bound with RCMono/RCBound.
theorem perScope_issue_depSat (spec : Program) (impl : ImplProgram) (alloc : PerScopeAllocR spec impl)
    (e : EngineId) (instr : DataPathInstrId) (ss : SpecState) (is : ImplState)
    (hUI : UniqueInstrIds spec.engines spec.body) (hUS : UniqueScopeIds spec.body)
    (hSema : perScopeSemaInv spec alloc ss is) (hSpecInv : SpecInv spec ss)
    (hWf : Allocatable spec)
    (hWait : is.semaphores (impl.waitOf instr) ≥ is.registers e (alloc.waitReg e))
    (hRegVal : is.registers e (alloc.waitReg e) =
      foldRegOps (impl.regOps e instr) (fun r => if r = alloc.waitReg e then 0 else is.registers e r) (alloc.waitReg e))
    (hLoopRegs : ∀ plid,
      (fun r => if r = alloc.waitReg e then 0 else is.registers e r) (alloc.monotoneReg e plid) =
      totalEntries ss e plid)
    (hTripRegs : ∀ lid, is.registers e (alloc.tripReg e lid) = tripEntries ss e spec.body lid)
    (hInv5 : ∀ eng, eng ∈ spec.engines → ∀ loop, RCMono spec ss eng loop)
    (hInv6 : ∀ eng, eng ∈ spec.engines → ∀ loop, RCBound spec ss eng loop)
    : depSatisfied spec (spec.depGraph instr) instr ss e = true := by
  rw [alloc.regOpsEq] at hRegVal
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
  have hInnerEq := foldRegOps_perScopeExpectedRegOps_waitReg (ab := alloc.toAllocBase)
    (spec := spec) (ss := ss) (e := e) (instr := instr) baseRegs
    (by simp [baseRegs]) hLoopRegs
  simp only at hDecomp
  unfold depSatisfied
  match hDep : spec.depGraph instr with
  | .none => simp
  | .dep producer offset =>
    simp only [hDep] at hDecomp
    let prodEng := (instrEngine spec.engines spec.body producer).getD 0
    have hPEM : prodEng ∈ spec.engines := by
      have hWfI := hWf instr; unfold Allocatable at hWfI; simp [hDep] at hWfI
      have hNe := instrEngine_ne_none_of_instrInBody hWfI.1
      obtain ⟨eng, hIE⟩ := Option.ne_none_iff_exists'.mp hNe
      simp [prodEng, hIE]; exact instrEngine_mem_engines hIE
    have hMP_of : ∀ loop, innermostParentScope spec.engines spec.body producer = loop →
        producer ∈ scopeInstrs spec.engines prodEng spec.body loop := by
      intro loop hPS
      have hWfI := hWf instr; unfold Allocatable at hWfI; simp [hDep] at hWfI
      have hIE := instrEngine_ne_none_of_instrInBody hWfI.1
      obtain ⟨eng, hEng⟩ := Option.ne_none_iff_exists'.mp hIE
      simp [prodEng, hEng]; exact mem_scopeInstrs_of_loop_engine hUI hUS (instrEngine_mem_engines hEng) hPS hEng
    -- Helper: convert v*N-(N-K) to N*(v-1)+K form for perScope_lower_bound
    have hLowerBound : ∀ loop v, v ≥ 1 →
        producer ∈ scopeInstrs spec.engines prodEng spec.body loop →
        scopeRetireSum ss.rc spec.engines prodEng spec.body loop ≥
          v * (scopeInstrs spec.engines prodEng spec.body loop).length -
          ((scopeInstrs spec.engines prodEng spec.body loop).length -
          ((scopeInstrs spec.engines prodEng spec.body loop).idxOf producer + 1)) →
        ss.rc producer ≥ v := by
      intro loop v hv hMP hSumGe
      have hKleN := List.idxOf_lt_length_of_mem hMP
      have hNodup := scopeInstrs_nodup (loop := loop) hUI hPEM
      have hConv : v * (scopeInstrs spec.engines prodEng spec.body loop).length -
          ((scopeInstrs spec.engines prodEng spec.body loop).length -
          ((scopeInstrs spec.engines prodEng spec.body loop).idxOf producer + 1)) =
          (scopeInstrs spec.engines prodEng spec.body loop).length * (v - 1) +
          ((scopeInstrs spec.engines prodEng spec.body loop).idxOf producer + 1) := by
        cases v with | zero => omega | succ n => simp [Nat.succ_mul, Nat.mul_comm]; omega
      have hSumGe' : (scopeInstrs spec.engines prodEng spec.body loop).foldl (fun acc i => acc + ss.rc i) 0 ≥
          (scopeInstrs spec.engines prodEng spec.body loop).length * (v - 1) +
          ((scopeInstrs spec.engines prodEng spec.body loop).idxOf producer + 1) := by
        change scopeRetireSum _ _ _ _ _ ≥ _ at hSumGe; unfold scopeRetireSum at hSumGe; omega
      exact perScope_lower_bound _ ss.rc hNodup
        (hInv5 _ hPEM loop) (hInv6 _ hPEM loop) producer hMP v hSumGe'
    match hPL : innermostParentScope spec.engines spec.body producer with
    | none =>
      have hSS := innermostSharedScope_eq_none_of_parent_eq_none
        (consumer := instr) hPL
      simp only [hPL, hSS, Bool.or_eq_true, decide_eq_true_eq, totalEntriesOpt]
      by_cases hOffset : offset = 0
      · subst offset
        right
        simp only [hSS] at hDecomp; rw [hDecomp, hInnerEq] at hRegVal
        simp [perScopeExpectedWaitVal, hDep, hPL] at hRegVal
        have hWS : impl.waitOf instr = alloc.perScopeSema none prodEng := by
          rw [alloc.waitOfEq]; simp [depProducer, hDep, hPL]; rfl
        rw [hWS] at hWait; rw [hSema none _ hPEM] at hWait; rw [hRegVal] at hWait
        have hMP := hMP_of none hPL
        exact hLowerBound none 1 (by omega) hMP (by simpa using hWait)
      · left
        omega
    | some plid =>
      simp only [hPL, Bool.or_eq_true, decide_eq_true_eq]
      have hMP := hMP_of (some plid) hPL
      match hSS : innermostSharedScope spec.engines spec.body producer instr with
      | some sid =>
        simp only [hSS] at hDecomp
        have hBaseRes : baseRegs (alloc.tripReg e sid) = tripEntries ss e spec.body sid := by
          simp only [baseRegs]; rw [if_neg (Ne.symm (alloc.noClob_trip_wait e sid))]; exact hTripRegs sid
        rw [hBaseRes] at hDecomp
        by_cases hVac : tripEntries ss e spec.body sid ≤ offset
        · simp [hVac]  -- vacuous case
        · right  -- non-vacuous: gate = 1
          simp only [show tripEntries ss e spec.body sid > offset from by omega, ite_true, Nat.one_mul] at hDecomp
          rw [hDecomp, hInnerEq] at hRegVal
          have hWS : impl.waitOf instr = alloc.perScopeSema (some plid) prodEng := by
            rw [alloc.waitOfEq]; simp [depProducer, hDep, hPL]; rfl
          rw [hWS] at hWait; rw [hSema (some plid) _ hPEM] at hWait; rw [hRegVal] at hWait
          simp only [perScopeExpectedWaitVal, hDep, hPL, hSS] at hWait
          by_cases hEq : some sid = some plid
          · obtain rfl := Option.some.inj hEq
            simp only [ite_true] at hWait
            have hCum := @cumExecs_of_all_ones _ _ sid (some sid) (totalEntries ss e sid) (hSpecInv.selfHistory e sid) (totalEntries ss e sid - offset) (Nat.sub_le _ _)
            simp only [totalEntriesOpt]; rw [hCum]
            rcases Nat.eq_zero_or_pos (totalEntries ss e sid - offset) with hv0 | hvpos
            · omega
            · exact hLowerBound (some sid) (totalEntries ss e sid - offset) hvpos hMP hWait
          · simp only [show ¬((some sid : Option ScopeId) = some plid) from hEq, ite_false] at hWait
            -- Need rc producer >= cumExecs
            have hWfI := hWf instr; unfold Allocatable at hWfI; simp [hDep, hPL] at hWfI
            obtain ⟨_, hWfI2⟩ := hWfI
            have hPlidInSl := innermostParentScope_in_sharedLoop_body hUS hUI hPL hSS (fun h => hEq (congrArg some h))
            have hCumFull := hSpecInv.cumulative e plid sid hPlidInSl
            rcases Nat.eq_zero_or_pos (totalEntries ss e plid) with hv0 | hvpos
            · -- totalEntries = 0
              rcases hWfI2 with hPI | ⟨_, hOff0⟩ | ⟨_, hOff1⟩
              · simp [hSS] at hPI; exact (hEq (congrArg some hPI)).elim
              · rw [hOff0]; simp only [Nat.sub_zero, totalEntriesOpt]; rw [hCumFull]; omega
              · rw [hOff1]; simp only [totalEntriesOpt]
                rw [hv0] at hCumFull
                rcases Nat.eq_zero_or_pos (totalEntries ss e sid) with hv0' | hvpos'
                · simp [cumExecs, hv0']
                · have hSucc := cumExecs_succ ss e plid (some sid) (totalEntries ss e sid - 1)
                  have hTE : totalEntries ss e sid - 1 + 1 = totalEntries ss e sid := by omega
                  rw [hTE] at hSucc; rw [hCumFull] at hSucc; omega
            · -- totalEntries > 0
              have hRCge := hLowerBound (some plid) (totalEntries ss e plid) hvpos hMP hWait
              rcases hWfI2 with hPI | ⟨_, hOff0⟩ | ⟨_, hOff1⟩
              · simp [hSS] at hPI; exact (hEq (congrArg some hPI)).elim
              · rw [hOff0]; simp only [Nat.sub_zero, totalEntriesOpt]; rw [hCumFull]; exact hRCge
              · rw [hOff1]; simp only [totalEntriesOpt]
                rcases Nat.eq_zero_or_pos (totalEntries ss e sid) with hv0' | hvpos'
                · simp [cumExecs, hv0']
                · have hSucc := cumExecs_succ ss e plid (some sid) (totalEntries ss e sid - 1)
                  have hTE : totalEntries ss e sid - 1 + 1 = totalEntries ss e sid := by omega
                  rw [hTE] at hSucc; omega
      | none =>
        simp only [hSS] at hDecomp; rw [hDecomp, hInnerEq] at hRegVal
        simp only [perScopeExpectedWaitVal, hDep, hPL, hSS] at hRegVal
        have hWS : impl.waitOf instr = alloc.perScopeSema (some plid) prodEng := by
          rw [alloc.waitOfEq]; simp [depProducer, hDep, hPL]; rfl
        rw [hWS] at hWait; rw [hSema (some plid) _ hPEM] at hWait; rw [hRegVal] at hWait
        simp only [show (none : Option ScopeId) ≠ some plid from nofun, ite_false] at hWait
        -- hWait: sum >= totalEntries * N - (N-K)
        have hWfI := hWf instr; unfold Allocatable at hWfI; simp [hDep, hPL] at hWfI
        obtain ⟨_, hWfI2⟩ := hWfI
        rcases hWfI2 with hPI | ⟨_, hOff0⟩ | ⟨_, hOff1⟩
        · rw [hSS] at hPI; simp at hPI
        · right; rw [hOff0]; simp only [Nat.sub_zero, totalEntriesOpt]
          have hCumOne : cumExecs ss e plid none 1 = totalEntries ss e plid := by
            simp [cumExecs, List.range_succ, List.range_zero, totalEntries]
          rw [hCumOne]
          rcases Nat.eq_zero_or_pos (totalEntries ss e plid) with hv0 | hvpos
          · omega
          · exact hLowerBound (some plid) (totalEntries ss e plid) hvpos hMP hWait
        · right; rw [hOff1]; simp only [totalEntriesOpt, show 1 - 1 = 0 from rfl]; simp [cumExecs]

-- Single-step backward sim using PerScopeInv directly (avoids universal closures)
set_option hygiene false in
macro "perScope_bsim " name:term : tactic => `(tactic|
  (apply $name spec impl alloc.toAllocBase (perScopeSemaInv spec alloc)
    (perScope_semaInv_mono spec impl alloc) <;> assumption))

-- Returns a disjunction rather than SpecStar because perScope_backward_sim_star must distinguish
-- silent from stepping in order to thread PerScopeInv: a silent step preserves it, whereas a
-- stepping case needs perScopeInv_spec_step.
theorem perScope_backward_sim_step (spec : Program) (impl : ImplProgram) (alloc : PerScopeAllocR spec impl)
    (e : EngineId) (ss : SpecState) (is is' : ImplState)
    (hSim : MatchStates spec impl alloc.toAllocBase (perScopeSemaInv spec alloc) ss is)
    (hStep : ImplStep impl e is is')
    (hWf : Allocatable spec) (hSpecInv : SpecInv spec ss)
    (hUniq : UniqueScopeIds spec.body) (hUniqueInstr : UniqueInstrIds spec.engines spec.body)
    (hEngines : e ∈ spec.engines)
    (hPerScopeInv : PerScopeInv spec impl alloc ss is)
    : (∃ ss', SpecStep spec e ss ss' ∧ MatchStates spec impl alloc.toAllocBase (perScopeSemaInv spec alloc) ss' is')
    ∨ MatchStates spec impl alloc.toAllocBase (perScopeSemaInv spec alloc) ss is' := by
  cases hStep with
  | regOpStep _ frame rest f instr dst src t hStack hStmt hInstr hRegOp =>
    exact BackwardSim.case_regOpStep spec impl alloc.toAllocBase
      (perScopeSemaInv spec alloc) (perScope_semaInv_mono spec impl alloc)
      (fun e i => perScopeExpectedRegOps spec (alloc.waitReg e) alloc.monotoneReg e i)
      ⟨perScope_innerRegOpsFirstSafe spec impl alloc,
       fun e i => perScopeExpectedRegOps_nonEmpty spec (alloc.waitReg e) alloc.monotoneReg e i,
       perScope_innerRegOpsDstWaitReg spec impl alloc⟩
      (fun e i => alloc.regOpsEq e i)
      e ss is hSim frame rest f instr dst src t hStack hStmt hInstr hRegOp
  | issue _ frame imrest f instr hStack hStmt hInstr hRegOpsDone hWait =>
    -- Use case_issue_depSat which takes hDeps directly (no universal closure)
    have hWRE : impl.waitReg e instr = alloc.waitReg e := alloc.waitRegEq e instr
    have hROI : (is.pc e).regOpIdx > 0 := by
      rw [hRegOpsDone]; exact perScope_regOpsNonEmpty spec impl alloc e instr
    have hNotRO : ¬ atRegOp frame := by
      obtain ⟨sf, srest, hSpecStack, hFrameCorr, _⟩ := pcCorr_stack_cons (hSim.pcCorr e) hStack
      intro hAR; simp [atRegOp] at hAR
      cases hk : frame.kind <;> simp [hk] at hAR <;>
        (rw [hAR] at hStmt; obtain ⟨ib, hBM, hBE⟩ := hFrameCorr.bodyCorr
         rw [hk] at hBE; rw [hBE] at hStmt; simp at hStmt)
    have hNotALS : ∀ lid, ¬ atLoopStart is e lid :=
      not_atLoopStart_of_not_atRegOp hStack hNotRO
    have hWRV := hSim.waitRegChain e frame imrest f instr hStack hStmt hInstr (by omega)
    have hRegVal : is.registers e (alloc.waitReg e) =
        foldRegOps (impl.regOps e instr) (fun r => if r = alloc.waitReg e then 0 else is.registers e r) (alloc.waitReg e) := by
      rw [hWRV, hRegOpsDone, List.take_length, alloc.regOpsEq]
    have hLoopRegs : ∀ plid,
        (fun r => if r = alloc.waitReg e then 0 else is.registers e r) (alloc.monotoneReg e plid) =
        totalEntries ss e plid := by
      intro plid; simp [Ne.symm (alloc.noClob e plid)]
      exact hSim.monotoneRegInv e plid (hNotALS plid)
    have hTripRegs : ∀ lid, is.registers e (alloc.tripReg e lid) = tripEntries ss e spec.body lid :=
      fun lid => hSim.tripRegInv e lid hNotALS
    have hWaitAdj : is.semaphores (impl.waitOf instr) ≥ is.registers e (alloc.waitReg e) := by
      rw [← hWRE]; exact hWait
    have hDeps : depSatisfied spec (spec.depGraph instr) instr ss e = true :=
      perScope_issue_depSat spec impl alloc e instr ss is hUniqueInstr hUniq
        hSim.semaInv hSpecInv hWf hWaitAdj hRegVal hLoopRegs hTripRegs
        (fun eng hEM loop => hPerScopeInv.rcMono eng loop hEM)
        (fun eng hEM loop => hPerScopeInv.rcBound eng loop hEM)
    exact BackwardSim.case_issue_depSat spec impl alloc.toAllocBase
      (perScopeSemaInv spec alloc) (perScope_semaInv_mono spec impl alloc)
      e ss is hSim hSpecInv hUniq hUniqueInstr hEngines
      frame imrest f instr hStack hStmt hInstr hRegOpsDone hWait hDeps
  | commit _ idx instr hIdx => perScope_bsim BackwardSim.case_commit
  | retire _ instr inflightRest hHead =>
    -- Use case_retire_semaInv which takes hSemaPost directly
    have hSpecHead : ss.inflight e = (instr, Phase.committed) :: inflightRest := by
      have := hSim.inflightEq e; rw [← this]; exact hHead
    have hInBody : instrInBody spec.engines spec.body instr = true :=
      hSpecInv.inflightInBody e instr Phase.committed (by rw [hSpecHead]; exact List.Mem.head _)
    have hSemaPost := perScope_retire_semaInv spec impl alloc e instr inflightRest ss is
      hUniqueInstr hUniq hSim.semaInv hInBody hSpecHead
    exact BackwardSim.case_retire_semaInv spec impl alloc.toAllocBase
      (perScopeSemaInv spec alloc) e ss is hSim hEngines instr inflightRest hHead hSemaPost
  | blockDone _ frame rest f hStack hStmt hDone => perScope_bsim BackwardSim.case_blockDone
  | stmtRegOpStep _ frame rest ops dst src t hStack hStmt hOp => perScope_bsim BackwardSim.case_stmtRegOpStep
  | stmtRegOpDone _ frame rest ops hStack hStmt hDone =>
    have ⟨hLoop, hTrip⟩ := hSim.regOpFold e frame rest ops hStack hStmt
    have hDrop : List.drop ((is.pc e).stmtRegOpIdx) (ops e) = [] := by
      rw [hDone]; simp
    exact (BackwardSim.case_stmtRegOpDone spec impl alloc.toAllocBase
      (perScopeSemaInv spec alloc) (perScope_semaInv_mono spec impl alloc) e ss is hSim
      frame rest ops hStack hStmt hDone
      (fun lid => by have := hLoop lid; rwa [hDrop] at this)
      (fun lid => by have := hTrip lid; rwa [hDrop] at this)).elim
      (fun ⟨ss', h1, h2⟩ => Or.inl ⟨ss', h1, h2⟩) Or.inr
  | loopEnter _ frame rest lid loopBody hStack hStmt hGuard =>
    exact (BackwardSim.case_loopEnter spec impl alloc.toAllocBase
      (perScopeSemaInv spec alloc) (perScope_semaInv_mono spec impl alloc) e ss is hSim hSpecInv hUniq hEngines
      frame rest lid loopBody hStack hStmt hGuard
      (scopeParent_in_enclosingLoops_loop hSim hSpecInv hUniq hEngines hStack hStmt)
      (fun _ hP => scopeParent_ne_self hUniq hP)).elim
      (fun ⟨ss', h1, h2⟩ => Or.inl ⟨ss', h1, h2⟩) Or.inr
  | loopSkip _ frame rest lid loopBody hStack hStmt hGuard => perScope_bsim BackwardSim.case_loopSkip
  | loopBack _ frame parent rest lid hStack hKind hEnd => perScope_bsim BackwardSim.case_loopBack
  | condTrue _ frame rest thenId elseId thenBody elseBody hStack hStmt hGuard =>
    exact (BackwardSim.case_condTrue spec impl alloc.toAllocBase
      (perScopeSemaInv spec alloc) (perScope_semaInv_mono spec impl alloc) e ss is hSim hSpecInv hUniq hEngines
      frame rest thenId elseId thenBody elseBody hStack hStmt hGuard
      (scopeParent_in_enclosingLoops_cond_then hSim hSpecInv hUniq hEngines hStack hStmt)
      (fun _ hP => scopeParent_ne_self hUniq hP)).elim
      (fun ⟨ss', h1, h2⟩ => Or.inl ⟨ss', h1, h2⟩) Or.inr
  | condFalse _ frame rest thenId elseId thenBody elseBody hStack hStmt hGuard =>
    exact (BackwardSim.case_condFalse spec impl alloc.toAllocBase
      (perScopeSemaInv spec alloc) (perScope_semaInv_mono spec impl alloc) e ss is hSim hSpecInv hUniq hEngines
      frame rest thenId elseId thenBody elseBody hStack hStmt hGuard
      (scopeParent_in_enclosingLoops_cond_else hSim hSpecInv hUniq hEngines hStack hStmt)
      (fun _ hP => scopeParent_ne_self hUniq hP)).elim
      (fun ⟨ss', h1, h2⟩ => Or.inl ⟨ss', h1, h2⟩) Or.inr
  | condDone _ frame parent rest sid hStack hKind hEnd => perScope_bsim BackwardSim.case_condDone

-- Helper: derive hInstrEng from inflightEngineEq for retire case
theorem hInstrEng_of_inflight {spec : Program} {ss : SpecState}
    {eng0 : EngineId} {instr : DataPathInstrId} {phase : Phase} {rest : List (DataPathInstrId × Phase)}
    (hSpecInv : SpecInv spec ss) (hUI : UniqueInstrIds spec.engines spec.body)
    (_hUS : UniqueScopeIds spec.body)
    (hHead : ss.inflight eng0 = (instr, phase) :: rest)
    (eng : EngineId) (hAllE : eng ∈ spec.engines) (loop : Option ScopeId)
    : eng ≠ eng0 → instr ∉ scopeInstrs spec.engines eng spec.body loop := by
  intro hne hMem
  have ⟨_, hIE1⟩ := scopeInstrs_implies_loop_engine hUI hAllE hMem
  have hIE2 := hSpecInv.inflightEngineEq eng0 instr phase (by rw [hHead]; exact List.Mem.head _)
  rw [hIE2] at hIE1; exact hne (Option.some.inj hIE1).symm

-- Helper: derive hInstrEng from instrEngine for issue case
theorem hInstrEng_of_issue {spec : Program} {ss : SpecState}
    {eng0 : EngineId} {frame : Frame} {rest : List Frame}
    {f : EngineId → List DataPathInstrId} {instr : DataPathInstrId}
    (hSpecInv : SpecInv spec ss) (hUI : UniqueInstrIds spec.engines spec.body)
    (_hUS : UniqueScopeIds spec.body) (hEng0Mem : eng0 ∈ spec.engines)
    (hStack : (ss.pc eng0).stack = frame :: rest)
    (hStmt : frame.body[frame.stmtIdx]? = some (Stmt.block f))
    (hInstr : (f eng0)[(ss.pc eng0).instrIdx]? = some instr)
    (eng : EngineId) (hAllE : eng ∈ spec.engines) (loop : Option ScopeId)
    : eng ≠ eng0 → instr ∉ scopeInstrs spec.engines eng spec.body loop := by
  intro hne hMem
  have ⟨_, hIE1⟩ := scopeInstrs_implies_loop_engine hUI hAllE hMem
  -- instrEngine for the issued instruction = some eng0
  have hMemF := List.mem_of_getElem? hInstr
  have hSMP := hStack ▸ hSpecInv.wellFormedPC eng0
  have hUIFrame := smp_uniqueInstrIds hSMP hUI frame (List.Mem.head _)
  have hFIB := findInBlock_isSome_of_mem hEng0Mem hMemF
  have hIESingle : instrEngine spec.engines [Stmt.block f] instr = some eng0 := by
    simp [instrEngine]; cases hfb : findInBlock spec.engines f instr with
    | none => simp [hfb] at hFIB
    | some eng' => simp; exact findInBlock_eq_of_mem hEng0Mem hMemF hfb (by
        have : ∀ (body : List Stmt) (n : Nat),
            UniqueInstrIds spec.engines body → body[n]? = some (Stmt.block f) →
            ∀ instr' e1 e2, e1 ∈ spec.engines → e2 ∈ spec.engines →
            instr' ∈ f e1 → instr' ∈ f e2 → e1 = e2 := by
          intro body n hUI' hIdx
          induction body generalizing n with
          | nil => simp at hIdx
          | cons s rest' ih =>
            cases n with
            | zero => simp at hIdx; cases s <;> simp at hIdx; obtain ⟨rfl⟩ := hIdx; cases hUI' with | block => assumption
            | succ m => simp at hIdx; exact ih m (by cases hUI' with | block => assumption | loop => assumption | cond => assumption) hIdx
        exact this frame.body frame.stmtIdx hUIFrame hStmt)
  have hIE2 := instrEngine_lift_smp hSMP hUI (List.Mem.head _)
    (instrEngine_of_getElem_rest hStmt hIESingle hUIFrame)
  rw [hIE2] at hIE1; exact hne (Option.some.inj hIE1).symm

-- If instr is at PC in a block, it's in scopeInstrs for the loop determined by SMP
-- For base (top-level), instr ∈ scopeInstrs ... none
theorem mem_scopeInstrs_none_of_block_at_top
    {engines : List EngineId} {eng : EngineId} {body : List Stmt}
    {si instrIdx : Nat} {f : EngineId → List DataPathInstrId} {instr : DataPathInstrId}
    (hUI : UniqueInstrIds engines body) (_hE : eng ∈ engines)
    (hStmt : body[si]? = some (Stmt.block f)) (hIn : (f eng)[instrIdx]? = some instr)
    : instr ∈ scopeInstrs engines eng body none := by
  have hMemF := List.mem_of_getElem? hIn
  induction body generalizing si with
  | nil => simp at hStmt
  | cons s rest ih =>
    cases si with
    | zero => cases s <;> simp_all [List.mem_append]
    | succ n =>
      cases s <;> simp at hStmt <;>
      (simp [List.mem_append, *]; cases hUI; first | exact ih (by assumption) hStmt | (right; exact ih (by assumption) hStmt))

-- scopeInstrs body (some sid) = [] when sid is not in the loop tree of body
theorem scopeInstrs_some_eq_nil
    {engines : List EngineId} {eng : EngineId}
    : ∀ {body : List Stmt} {sid : ScopeId},
    sid ∉ scopeIdsOf body →
    scopeInstrs engines eng body (some sid) = []
  | [], _, _ => by simp
  | .block _ :: rest, sid, h => by
    simp []; exact scopeInstrs_some_eq_nil (by simp [scopeIdsOf] at h; exact h)
  | .loop lid' lb' :: rest, sid, h => by
    simp [scopeIdsOf, List.mem_cons, List.mem_append, not_or] at h
    obtain ⟨hne, hnlb, hnrest⟩ := h
    simp only [scopeInstrs_loop_some, if_neg (Ne.symm hne)]
    rw [scopeInstrs_some_eq_nil hnlb, scopeInstrs_some_eq_nil hnrest]; simp
  | .cond tid eid tb eb :: rest, sid, h => by
    simp [scopeIdsOf, List.mem_cons, List.mem_append, not_or] at h
    obtain ⟨hne1, hne2, hntb, hneb, hnrest⟩ := h
    simp only [scopeInstrs_cond_some, if_neg (Ne.symm hne1), if_neg (Ne.symm hne2)]
    rw [scopeInstrs_some_eq_nil hntb, scopeInstrs_some_eq_nil hneb, scopeInstrs_some_eq_nil hnrest]; simp

-- scopeInstrs body (some sid) = scopeInstrs (scopeBodyOf body sid).getD [] none
theorem scopeInstrs_eq_scopeBodyOf
    {engines : List EngineId} {eng : EngineId}
    : ∀ {body : List Stmt} {sid : ScopeId},
    UniqueScopeIds body →
    scopeInstrs engines eng body (some sid) =
      scopeInstrs engines eng ((scopeBodyOf body sid).getD []) none
  | [], _, _ => by simp [scopeBodyOf]
  | .block _ :: rest, sid, hUS => by
    simp [scopeBodyOf]
    cases hUS with | block _ _ hUSR => exact scopeInstrs_eq_scopeBodyOf hUSR
  | .loop lid lb :: rest, sid, hUS => by
    cases hUS with | loop _ _ _ _ _ =>
      rename_i hUSLb hLidNLb hUSR hLidNR hDisjBR
      simp only [scopeInstrs_loop_some, scopeBodyOf]
      by_cases hEq : lid = sid
      · subst hEq; simp
      · simp [hEq]
        by_cases hInLb : sid ∈ scopeIdsOf lb
        · have hNotInRest : sid ∉ scopeIdsOf rest := hDisjBR sid hInLb
          rw [scopeInstrs_some_eq_nil hNotInRest, List.append_nil]
          rw [scopeInstrs_eq_scopeBodyOf hUSLb]
          rw [scopeBodyOf_none_of_not_mem hNotInRest]
          cases scopeBodyOf lb sid <;> simp
        · rw [scopeInstrs_some_eq_nil hInLb, scopeBodyOf_none_of_not_mem hInLb]
          simp
          exact scopeInstrs_eq_scopeBodyOf hUSR
  | .cond tid eid tb eb :: rest, sid, hUS => by
    cases hUS with | cond _ _ _ _ _ _ _ _ _ _ _ _ =>
      rename_i a b c d e f g h i j k l
      simp only [scopeInstrs_cond_some, scopeBodyOf]
      by_cases hTid : tid = sid
      · subst hTid; simp
      · simp [hTid]
        by_cases hEid : eid = sid
        · subst hEid; simp
        · simp [hEid]
          by_cases hInTb : sid ∈ scopeIdsOf tb
          · have hNotInEb : sid ∉ scopeIdsOf eb := (l sid hInTb).1
            have hNotInRest : sid ∉ scopeIdsOf rest := (l sid hInTb).2
            rw [scopeInstrs_some_eq_nil hNotInEb, scopeInstrs_some_eq_nil hNotInRest]
            simp
            rw [scopeInstrs_eq_scopeBodyOf b]
            rw [scopeBodyOf_none_of_not_mem hNotInEb, scopeBodyOf_none_of_not_mem hNotInRest]
            cases scopeBodyOf tb sid <;> simp
          · by_cases hInEb : sid ∈ scopeIdsOf eb
            · have hNotInRest : sid ∉ scopeIdsOf rest := k sid hInEb
              rw [scopeInstrs_some_eq_nil hInTb, scopeInstrs_some_eq_nil hNotInRest]
              simp
              rw [scopeInstrs_eq_scopeBodyOf e, scopeBodyOf_none_of_not_mem hInTb,
                  scopeBodyOf_none_of_not_mem hNotInRest]
              cases scopeBodyOf eb sid <;> simp
            · rw [scopeInstrs_some_eq_nil hInTb, scopeInstrs_some_eq_nil hInEb]
              simp
              rw [scopeBodyOf_none_of_not_mem hInTb, scopeBodyOf_none_of_not_mem hInEb]
              simp
              exact scopeInstrs_eq_scopeBodyOf h

-- Unified theorem: if scopeBodyOf body sid = some sb, then scopeInstrs body (some sid) = scopeInstrs sb none
theorem scopeInstrs_of_scopeBodyOf
    {engines : List EngineId} {eng : EngineId} {body : List Stmt}
    {sid : ScopeId} {sb : List Stmt}
    (hUS : UniqueScopeIds body)
    (hSB : scopeBodyOf body sid = some sb)
    : scopeInstrs engines eng body (some sid) = scopeInstrs engines eng sb none := by
  rw [scopeInstrs_eq_scopeBodyOf hUS, hSB]; simp

-- instrsBefore at stmtIdx+1 when body[stmtIdx] is a loop: same as instrsBefore at stmtIdx
theorem instrsBefore_succ_of_loop {engines : List EngineId} {eng : EngineId}
    {body : List Stmt} {n : Nat} {lid : ScopeId} {lb : List Stmt}
    (h : body[n]? = some (Stmt.loop lid lb))
    : instrsBefore engines eng body (n + 1) = instrsBefore engines eng body n := by
  induction body generalizing n with
  | nil => simp at h
  | cons s rest ih =>
    cases n with
    | zero => cases s <;> simp at h; obtain ⟨rfl, _⟩ := h; simp [instrsBefore]
    | succ m => cases s <;> (simp at h; simp [instrsBefore]; exact ih h)

theorem instrsBefore_succ_of_cond {engines : List EngineId} {eng : EngineId}
    {body : List Stmt} {n : Nat} {tid eid : ScopeId} {tb eb : List Stmt}
    (h : body[n]? = some (Stmt.cond tid eid tb eb))
    : instrsBefore engines eng body (n + 1) = instrsBefore engines eng body n := by
  induction body generalizing n with
  | nil => simp at h
  | cons s rest ih =>
    cases n with
    | zero => cases s <;> simp at h; obtain ⟨_, _, _, _⟩ := h; simp_all [instrsBefore]
    | succ m => cases s <;> (simp at h; simp [instrsBefore]; exact ih h)

theorem instrsBefore_succ_of_block {engines : List EngineId} {eng : EngineId}
    {body : List Stmt} {n : Nat} {f : EngineId → List DataPathInstrId}
    (h : body[n]? = some (Stmt.block f))
    : instrsBefore engines eng body (n + 1) = instrsBefore engines eng body n + (f eng).length := by
  induction body generalizing n with
  | nil => simp at h
  | cons s rest ih =>
    cases n with
    | zero => cases s <;> simp at h; cases h; simp [instrsBefore]
    | succ m =>
      cases s <;> simp at h <;> simp [instrsBefore]
      · have := ih h; omega  -- block head: add (a eng).length to both sides
      · exact ih h  -- loop head
      · exact ih h  -- cond head

-- findActiveFrame returns isTop = true for the loop containing the PC instruction
theorem findActiveFrame_isTop_of_instrAtPC {spec : Program} {ss : SpecState}
    (hSpecInv : SpecInv spec ss) (hUI : UniqueInstrIds spec.engines spec.body)
    (hUS : UniqueScopeIds spec.body)
    {eng : EngineId} {frame : Frame} {rest : List Frame}
    {f : EngineId → List DataPathInstrId} {instr : DataPathInstrId}
    (hAllE : eng ∈ spec.engines)
    (hStack : (ss.pc eng).stack = frame :: rest)
    (hStmt : frame.body[frame.stmtIdx]? = some (Stmt.block f))
    (hInstr : (f eng)[(ss.pc eng).instrIdx]? = some instr)
    {loop : Option ScopeId}
    (hMem : instr ∈ scopeInstrs spec.engines eng spec.body loop)
    : ∃ fr, findActiveFrame (frame :: rest) loop = some (fr, true) := by
  have hSMP := hSpecInv.wellFormedPC eng
  rw [hStack] at hSMP
  -- For each SMP case, the matching loop has isTop = true (by findActiveFrame computation)
  -- Non-matching loops derive contradiction via scopeInstrs uniqueness
  cases hSMP with
  | base si ii =>
    simp at hStmt; cases loop with
    | none => exact ⟨⟨spec.body, si, .top⟩, by simp [findActiveFrame]⟩
    | some sid =>
      exfalso
      have hMemNone := mem_scopeInstrs_none_of_block_at_top hUI hAllE hStmt hInstr
      have ⟨hS1, _⟩ := scopeInstrs_implies_loop_engine hUI hAllE hMemNone
      have ⟨hS2, _⟩ := scopeInstrs_implies_loop_engine hUI hAllE hMem
      rw [hS1] at hS2; exact absurd hS2 (by simp)
  | loop loopBody si ii lid parentFrame rest' hParentStmt hParentSMP =>
    simp at hStmt; cases loop with
    | some sid =>
      by_cases hSid : lid = sid
      · subst hSid; exact ⟨⟨loopBody, si, .loop lid⟩, by simp [findActiveFrame]⟩
      · exfalso
        have hUILB := uniqueInstrIds_of_getElem_loop_smp hParentStmt (smp_uniqueInstrIds hParentSMP hUI parentFrame (List.Mem.head _))
        have hMemLBNone := mem_scopeInstrs_none_of_block_at_top hUILB hAllE hStmt hInstr
        have hUSFrame := smp_uniqueScopeIds hParentSMP hUS parentFrame (List.Mem.head _)
        have hSIpf := @scopeInstrs_of_scopeBodyOf spec.engines eng _ _ _ hUSFrame (scopeBodyOf_of_getElem hParentStmt hUSFrame)
        have hSBAgree := smp_scopeBodyOf_agree hParentSMP hUS parentFrame (List.Mem.head _) lid
          (mem_scopeIdsOf_of_getElem hParentStmt (by simp [scopeIdsOf]))
        have hMemLid : instr ∈ scopeInstrs spec.engines eng spec.body (some lid) := by
          rw [scopeInstrs_eq_scopeBodyOf hUS, hSBAgree, ← scopeInstrs_eq_scopeBodyOf hUSFrame, hSIpf]
          exact hMemLBNone
        have ⟨hS2, _⟩ := scopeInstrs_implies_loop_engine hUI hAllE hMem
        have ⟨hS3, _⟩ := scopeInstrs_implies_loop_engine hUI hAllE hMemLid
        rw [hS2] at hS3; exact hSid (Option.some.inj hS3).symm
    | none =>
      exfalso
      have hUILB := uniqueInstrIds_of_getElem_loop_smp hParentStmt (smp_uniqueInstrIds hParentSMP hUI parentFrame (List.Mem.head _))
      have hMemLBNone := mem_scopeInstrs_none_of_block_at_top hUILB hAllE hStmt hInstr
      have hUSFrame := smp_uniqueScopeIds hParentSMP hUS parentFrame (List.Mem.head _)
      have hSIpf := @scopeInstrs_of_scopeBodyOf spec.engines eng _ _ _ hUSFrame (scopeBodyOf_of_getElem hParentStmt hUSFrame)
      have hSBAgree := smp_scopeBodyOf_agree hParentSMP hUS parentFrame (List.Mem.head _) lid
        (mem_scopeIdsOf_of_getElem hParentStmt (by simp [scopeIdsOf]))
      have hMemLid : instr ∈ scopeInstrs spec.engines eng spec.body (some lid) := by
        rw [scopeInstrs_eq_scopeBodyOf hUS, hSBAgree, ← scopeInstrs_eq_scopeBodyOf hUSFrame, hSIpf]
        exact hMemLBNone
      have ⟨hS2, _⟩ := scopeInstrs_implies_loop_engine hUI hAllE hMem
      have ⟨hS3, _⟩ := scopeInstrs_implies_loop_engine hUI hAllE hMemLid
      rw [hS2] at hS3; exact absurd hS3 (by simp)
  | cond thenBody elseBody si ii tid eid parentFrame rest' taken hParentStmt hParentSMP =>
    simp at hStmt
    have hUSFrame := smp_uniqueScopeIds hParentSMP hUS parentFrame (List.Mem.head _)
    have hUIParent := smp_uniqueInstrIds hParentSMP hUI parentFrame (List.Mem.head _)
    -- The active loop id is (if taken then tid else eid)
    have hScopeId := if taken then tid else eid
    cases taken with
    | true =>
      simp at hStmt
      -- taken = true
      have hUITB := uniqueInstrIds_of_getElem_condTrue_smp hParentStmt hUIParent
      have hMemTBNone := mem_scopeInstrs_none_of_block_at_top hUITB hAllE hStmt hInstr
      have hSIpf := @scopeInstrs_of_scopeBodyOf spec.engines eng _ _ _ hUSFrame (scopeBodyOf_of_getElem_condTrue hParentStmt hUSFrame)
      have hSBAgree := smp_scopeBodyOf_agree hParentSMP hUS parentFrame (List.Mem.head _) tid
        (mem_scopeIdsOf_of_getElem hParentStmt (by simp [scopeIdsOf]))
      have hMemTid : instr ∈ scopeInstrs spec.engines eng spec.body (some tid) := by
        rw [scopeInstrs_eq_scopeBodyOf hUS, hSBAgree, ← scopeInstrs_eq_scopeBodyOf hUSFrame, hSIpf]
        exact hMemTBNone
      cases loop with
      | some sid =>
        by_cases hSid : tid = sid
        · subst hSid; exact ⟨⟨thenBody, si, .cond tid⟩, by simp [findActiveFrame]⟩
        · exfalso
          have ⟨hS2, _⟩ := scopeInstrs_implies_loop_engine hUI hAllE hMem
          have ⟨hS3, _⟩ := scopeInstrs_implies_loop_engine hUI hAllE hMemTid
          rw [hS2] at hS3; exact hSid (Option.some.inj hS3).symm
      | none =>
        exfalso
        have ⟨hS2, _⟩ := scopeInstrs_implies_loop_engine hUI hAllE hMem
        have ⟨hS3, _⟩ := scopeInstrs_implies_loop_engine hUI hAllE hMemTid
        rw [hS2] at hS3; exact absurd hS3 (by simp)
    | false =>
      simp at hStmt
      -- taken = false
      have hUIEB := uniqueInstrIds_of_getElem_condFalse_smp hParentStmt hUIParent
      have hMemEBNone := mem_scopeInstrs_none_of_block_at_top hUIEB hAllE hStmt hInstr
      have hSIpf := @scopeInstrs_of_scopeBodyOf spec.engines eng _ _ _ hUSFrame (scopeBodyOf_of_getElem_condFalse hParentStmt hUSFrame)
      have hSBAgree := smp_scopeBodyOf_agree hParentSMP hUS parentFrame (List.Mem.head _) eid
        (mem_scopeIdsOf_of_getElem hParentStmt (by simp [scopeIdsOf]))
      have hMemEid : instr ∈ scopeInstrs spec.engines eng spec.body (some eid) := by
        rw [scopeInstrs_eq_scopeBodyOf hUS, hSBAgree, ← scopeInstrs_eq_scopeBodyOf hUSFrame, hSIpf]
        exact hMemEBNone
      cases loop with
      | some sid =>
        by_cases hSid : eid = sid
        · subst hSid; exact ⟨⟨elseBody, si, .cond eid⟩, by simp [findActiveFrame]⟩
        · exfalso
          have ⟨hS2, _⟩ := scopeInstrs_implies_loop_engine hUI hAllE hMem
          have ⟨hS3, _⟩ := scopeInstrs_implies_loop_engine hUI hAllE hMemEid
          rw [hS2] at hS3; exact hSid (Option.some.inj hS3).symm
      | none =>
        exfalso
        have ⟨hS2, _⟩ := scopeInstrs_implies_loop_engine hUI hAllE hMem
        have ⟨hS3, _⟩ := scopeInstrs_implies_loop_engine hUI hAllE hMemEid
        rw [hS2] at hS3; exact absurd hS3 (by simp)

-- If findActiveFrame returns isTop = true for loop, then the PC instruction is in that loop
theorem mem_scopeInstrs_of_findActiveFrame_isTop {spec : Program} {ss : SpecState}
    (hSpecInv : SpecInv spec ss) (hUI : UniqueInstrIds spec.engines spec.body)
    (hUS : UniqueScopeIds spec.body)
    {eng : EngineId} {frame : Frame} {rest : List Frame}
    {f : EngineId → List DataPathInstrId} {instr : DataPathInstrId}
    (hAllE : eng ∈ spec.engines)
    (hStack : (ss.pc eng).stack = frame :: rest)
    (hStmt : frame.body[frame.stmtIdx]? = some (Stmt.block f))
    (hInstr : (f eng)[(ss.pc eng).instrIdx]? = some instr)
    {loop : Option ScopeId} {fr : Frame}
    (hfa : findActiveFrame (frame :: rest) loop = some (fr, true))
    : instr ∈ scopeInstrs spec.engines eng spec.body loop := by
  -- findActiveFrame_isTop_eq gives fr = frame
  have hfr := findActiveFrame_isTop_eq hfa; subst hfr
  -- Now use the bridge proof structure: for matching loop, instr ∈ scopeInstrs
  -- This is the same SMP case analysis as findActiveFrame_isTop_of_instrAtPC
  have hSMP := hSpecInv.wellFormedPC eng
  rw [hStack] at hSMP
  cases hSMP with
  | base si ii =>
    simp at hStmt
    cases loop with
    | none => exact mem_scopeInstrs_none_of_block_at_top hUI hAllE hStmt hInstr
    | some sid => simp [findActiveFrame] at hfa
  | loop loopBody si ii lid parentFrame rest' hParentStmt hParentSMP =>
    simp at hStmt
    cases loop with
    | some sid =>
      by_cases hSid : lid = sid
      · subst hSid
        have hUILB := uniqueInstrIds_of_getElem_loop_smp hParentStmt (smp_uniqueInstrIds hParentSMP hUI parentFrame (List.Mem.head _))
        have hMemLBNone := mem_scopeInstrs_none_of_block_at_top hUILB hAllE hStmt hInstr
        have hUSFrame := smp_uniqueScopeIds hParentSMP hUS parentFrame (List.Mem.head _)
        have hSIpf := @scopeInstrs_of_scopeBodyOf spec.engines eng _ _ _ hUSFrame (scopeBodyOf_of_getElem hParentStmt hUSFrame)
        have hSBAgree := smp_scopeBodyOf_agree hParentSMP hUS parentFrame (List.Mem.head _) lid
          (mem_scopeIdsOf_of_getElem hParentStmt (by simp [scopeIdsOf]))
        rw [scopeInstrs_eq_scopeBodyOf hUS, hSBAgree, ← scopeInstrs_eq_scopeBodyOf hUSFrame, hSIpf]
        exact hMemLBNone
      · simp [findActiveFrame, show lid ≠ sid from hSid] at hfa
    | none => simp [findActiveFrame] at hfa
  | cond thenBody elseBody si ii tid eid parentFrame rest' taken hParentStmt hParentSMP =>
    simp at hStmt; cases loop with
    | some sid =>
      have hActiveSid := if taken then tid else eid
      by_cases hSid : (if taken then tid else eid) = sid
      · cases taken with
        | false =>
          simp at hSid hStmt; subst hSid
          have hUIEB := uniqueInstrIds_of_getElem_condFalse_smp hParentStmt (smp_uniqueInstrIds hParentSMP hUI parentFrame (List.Mem.head _))
          have hMemEBNone := mem_scopeInstrs_none_of_block_at_top hUIEB hAllE hStmt hInstr
          have hUSFrame := smp_uniqueScopeIds hParentSMP hUS parentFrame (List.Mem.head _)
          have hSIpf := @scopeInstrs_of_scopeBodyOf spec.engines eng _ _ _ hUSFrame (scopeBodyOf_of_getElem_condFalse hParentStmt hUSFrame)
          have hSBAgree := smp_scopeBodyOf_agree hParentSMP hUS parentFrame (List.Mem.head _) eid
            (mem_scopeIdsOf_of_getElem hParentStmt (by simp [scopeIdsOf]))
          rw [scopeInstrs_eq_scopeBodyOf hUS, hSBAgree, ← scopeInstrs_eq_scopeBodyOf hUSFrame, hSIpf]
          exact hMemEBNone
        | true =>
          simp at hSid hStmt; subst hSid
          have hUITB := uniqueInstrIds_of_getElem_condTrue_smp hParentStmt (smp_uniqueInstrIds hParentSMP hUI parentFrame (List.Mem.head _))
          have hMemTBNone := mem_scopeInstrs_none_of_block_at_top hUITB hAllE hStmt hInstr
          have hUSFrame := smp_uniqueScopeIds hParentSMP hUS parentFrame (List.Mem.head _)
          have hSIpf := @scopeInstrs_of_scopeBodyOf spec.engines eng _ _ _ hUSFrame (scopeBodyOf_of_getElem_condTrue hParentStmt hUSFrame)
          have hSBAgree := smp_scopeBodyOf_agree hParentSMP hUS parentFrame (List.Mem.head _) tid
            (mem_scopeIdsOf_of_getElem hParentStmt (by simp [scopeIdsOf]))
          rw [scopeInstrs_eq_scopeBodyOf hUS, hSBAgree, ← scopeInstrs_eq_scopeBodyOf hUSFrame, hSIpf]
          exact hMemTBNone
      · cases taken <;> simp at hSid <;> simp [findActiveFrame, hSid] at hfa
    | none => simp [findActiveFrame] at hfa

-- Key bridge: scopeKBound = idxOf(instruction at PC) in scopeInstrs
-- This connects the PC-computed kBound to the index in the flat instruction list
theorem scopeKBound_eq_idxOf_instrAtPC {spec : Program} {ss : SpecState}
    (hSpecInv : SpecInv spec ss) (hUI : UniqueInstrIds spec.engines spec.body)
    (hUS : UniqueScopeIds spec.body)
    {eng : EngineId} {frame : Frame} {rest : List Frame}
    {f : EngineId → List DataPathInstrId} {instr : DataPathInstrId}
    (hAllE : eng ∈ spec.engines)
    (hStack : (ss.pc eng).stack = frame :: rest)
    (hStmt : frame.body[frame.stmtIdx]? = some (Stmt.block f))
    (hInstr : (f eng)[(ss.pc eng).instrIdx]? = some instr)
    {loop : Option ScopeId}
    (hMem : instr ∈ scopeInstrs spec.engines eng spec.body loop)
    : scopeKBound spec ss eng loop =
        (scopeInstrs spec.engines eng spec.body loop).idxOf instr := by
  have hSMP := hSpecInv.wellFormedPC eng
  rw [hStack] at hSMP
  simp only [scopeKBound, hStack]
  cases hSMP with
  | base si ii =>
    -- frame.body = spec.body, single .top frame
    simp at hStmt
    -- findActiveFrame [⟨spec.body, si, .top⟩] loop
    cases loop with
    | none =>
      simp [findActiveFrame, hStmt]
      exact (scopeInstrs_idxOf_eq_instrsBefore_none hStmt hInstr hUI hAllE
        (scopeInstrs_nodup hUI hAllE)).symm
    | some sid =>
      -- instr ∈ scopeInstrs ... (some sid) but instr is in top-level block → contradiction
      simp [findActiveFrame]
      have hMemNone := mem_scopeInstrs_none_of_block_at_top hUI hAllE hStmt hInstr
      have ⟨hS1, _⟩ := scopeInstrs_implies_loop_engine hUI hAllE hMemNone
      have ⟨hS2, _⟩ := scopeInstrs_implies_loop_engine hUI hAllE hMem
      rw [hS1] at hS2; exact absurd hS2 (by simp)
  | loop loopBody si ii lid parentFrame rest' hParentStmt hParentSMP =>
    simp at hStmt
    -- child.kind = .loop lid
    cases loop with
    | some sid =>
      by_cases hSid : lid = sid
      · subst hSid
        -- findActiveFrame returns (child, true) since child.kind = .loop lid
        simp [findActiveFrame, hStmt]
        -- scopeInstrs spec.body (some lid) = scopeInstrs loopBody none (via scopeBodyOf bridge)
        have hUISMP := smp_uniqueInstrIds hParentSMP hUI parentFrame (List.Mem.head _)
        have hUILB := uniqueInstrIds_of_getElem_loop_smp hParentStmt hUISMP
        have hUSFrame := smp_uniqueScopeIds hParentSMP hUS parentFrame (List.Mem.head _)
        have hUSLB : UniqueScopeIds loopBody := by
          have h := uniqueScopeIds_of_getElem hParentStmt hUSFrame
          cases h with | loop => assumption
        -- Connect scopeInstrs spec.body (some lid) = scopeInstrs loopBody none
        -- Use scopeInstrs_of_scopeBodyOf on parentFrame.body
        have hSIpf := @scopeInstrs_of_scopeBodyOf spec.engines eng _ _ _ hUSFrame (scopeBodyOf_of_getElem hParentStmt hUSFrame)
        -- And connect scopeInstrs spec.body (some lid) to scopeInstrs parentFrame.body (some lid)
        -- via scopeInstrs_eq_scopeBodyOf + smp_scopeBodyOf_agree
        have hSBAgree := smp_scopeBodyOf_agree hParentSMP hUS parentFrame (List.Mem.head _) lid
          (mem_scopeIdsOf_of_getElem hParentStmt (by simp [scopeIdsOf]))
        rw [scopeInstrs_eq_scopeBodyOf hUS, hSBAgree, ← scopeInstrs_eq_scopeBodyOf hUSFrame, hSIpf]
        exact (scopeInstrs_idxOf_eq_instrsBefore_none hStmt hInstr hUILB hAllE
          (scopeInstrs_nodup hUILB hAllE)).symm
      · -- sid ≠ lid: contradiction — instr's unique loop is lid, not sid
        exfalso
        have hUILB' := uniqueInstrIds_of_getElem_loop_smp hParentStmt (smp_uniqueInstrIds hParentSMP hUI parentFrame (List.Mem.head _))
        have hMemLBNone := mem_scopeInstrs_none_of_block_at_top hUILB' hAllE hStmt hInstr
        have hUSFrame := smp_uniqueScopeIds hParentSMP hUS parentFrame (List.Mem.head _)
        have hSIpf := @scopeInstrs_of_scopeBodyOf spec.engines eng _ _ _ hUSFrame (scopeBodyOf_of_getElem hParentStmt hUSFrame)
        have hSBAgree := smp_scopeBodyOf_agree hParentSMP hUS parentFrame (List.Mem.head _) lid
          (mem_scopeIdsOf_of_getElem hParentStmt (by simp [scopeIdsOf]))
        have hMemLid : instr ∈ scopeInstrs spec.engines eng spec.body (some lid) := by
          rw [scopeInstrs_eq_scopeBodyOf hUS, hSBAgree, ← scopeInstrs_eq_scopeBodyOf hUSFrame, hSIpf]
          exact hMemLBNone
        have ⟨hS2, _⟩ := scopeInstrs_implies_loop_engine hUI hAllE hMem
        have ⟨hS3, _⟩ := scopeInstrs_implies_loop_engine hUI hAllE hMemLid
        rw [hS2] at hS3; exact hSid (Option.some.inj hS3).symm
    | none =>
      -- loop = none: contradiction — loopBody instr has loop some lid, not none
      exfalso
      have hUILB' := uniqueInstrIds_of_getElem_loop_smp hParentStmt (smp_uniqueInstrIds hParentSMP hUI parentFrame (List.Mem.head _))
      have hMemLBNone := mem_scopeInstrs_none_of_block_at_top hUILB' hAllE hStmt hInstr
      have hUSFrame := smp_uniqueScopeIds hParentSMP hUS parentFrame (List.Mem.head _)
      have hSIpf := @scopeInstrs_of_scopeBodyOf spec.engines eng _ _ _ hUSFrame (scopeBodyOf_of_getElem hParentStmt hUSFrame)
      have hSBAgree := smp_scopeBodyOf_agree hParentSMP hUS parentFrame (List.Mem.head _) lid
        (mem_scopeIdsOf_of_getElem hParentStmt (by simp [scopeIdsOf]))
      have hMemLid : instr ∈ scopeInstrs spec.engines eng spec.body (some lid) := by
        rw [scopeInstrs_eq_scopeBodyOf hUS, hSBAgree, ← scopeInstrs_eq_scopeBodyOf hUSFrame, hSIpf]
        exact hMemLBNone
      have ⟨hS2, _⟩ := scopeInstrs_implies_loop_engine hUI hAllE hMem
      have ⟨hS3, _⟩ := scopeInstrs_implies_loop_engine hUI hAllE hMemLid
      rw [hS2] at hS3; exact absurd hS3 (by simp)
  | cond thenBody elseBody si ii tid eid parentFrame rest' taken hParentStmt hParentSMP =>
    simp at hStmt
    have hUIPF := smp_uniqueInstrIds hParentSMP hUI parentFrame (List.Mem.head _)
    have hUSFrame := smp_uniqueScopeIds hParentSMP hUS parentFrame (List.Mem.head _)
    -- Get the active body and loop id based on taken
    cases taken with
    | true =>
      simp at hStmt
      -- taken = true
      have hUIBody := uniqueInstrIds_of_getElem_condTrue_smp hParentStmt hUIPF
      cases loop with
      | some sid =>
        by_cases hSid : tid = sid
        · subst hSid
          simp [findActiveFrame, hStmt]
          have hSIpf := @scopeInstrs_of_scopeBodyOf spec.engines eng _ _ _ hUSFrame (scopeBodyOf_of_getElem_condTrue hParentStmt hUSFrame)
          have hSBAgree := smp_scopeBodyOf_agree hParentSMP hUS parentFrame (List.Mem.head _) tid
            (mem_scopeIdsOf_of_getElem hParentStmt (by simp [scopeIdsOf]))
          rw [scopeInstrs_eq_scopeBodyOf hUS, hSBAgree, ← scopeInstrs_eq_scopeBodyOf hUSFrame, hSIpf]
          exact (scopeInstrs_idxOf_eq_instrsBefore_none hStmt hInstr hUIBody hAllE
            (scopeInstrs_nodup hUIBody hAllE)).symm
        · exfalso
          have hMemTBNone := mem_scopeInstrs_none_of_block_at_top hUIBody hAllE hStmt hInstr
          have hSIpf := @scopeInstrs_of_scopeBodyOf spec.engines eng _ _ _ hUSFrame (scopeBodyOf_of_getElem_condTrue hParentStmt hUSFrame)
          have hSBAgree := smp_scopeBodyOf_agree hParentSMP hUS parentFrame (List.Mem.head _) tid
            (mem_scopeIdsOf_of_getElem hParentStmt (by simp [scopeIdsOf]))
          have hMemTid : instr ∈ scopeInstrs spec.engines eng spec.body (some tid) := by
            rw [scopeInstrs_eq_scopeBodyOf hUS, hSBAgree, ← scopeInstrs_eq_scopeBodyOf hUSFrame, hSIpf]
            exact hMemTBNone
          have ⟨hS2, _⟩ := scopeInstrs_implies_loop_engine hUI hAllE hMem
          have ⟨hS3, _⟩ := scopeInstrs_implies_loop_engine hUI hAllE hMemTid
          rw [hS2] at hS3; exact hSid (Option.some.inj hS3).symm
      | none =>
        exfalso
        have hMemTBNone := mem_scopeInstrs_none_of_block_at_top hUIBody hAllE hStmt hInstr
        have hSIpf := @scopeInstrs_of_scopeBodyOf spec.engines eng _ _ _ hUSFrame (scopeBodyOf_of_getElem_condTrue hParentStmt hUSFrame)
        have hSBAgree := smp_scopeBodyOf_agree hParentSMP hUS parentFrame (List.Mem.head _) tid
          (mem_scopeIdsOf_of_getElem hParentStmt (by simp [scopeIdsOf]))
        have hMemTid : instr ∈ scopeInstrs spec.engines eng spec.body (some tid) := by
          rw [scopeInstrs_eq_scopeBodyOf hUS, hSBAgree, ← scopeInstrs_eq_scopeBodyOf hUSFrame, hSIpf]
          exact hMemTBNone
        have ⟨hS2, _⟩ := scopeInstrs_implies_loop_engine hUI hAllE hMem
        have ⟨hS3, _⟩ := scopeInstrs_implies_loop_engine hUI hAllE hMemTid
        rw [hS2] at hS3; exact absurd hS3 (by simp)
    | false =>
      simp at hStmt
      -- taken = false
      have hUIBody := uniqueInstrIds_of_getElem_condFalse_smp hParentStmt hUIPF
      cases loop with
      | some sid =>
        by_cases hSid : eid = sid
        · subst hSid
          simp [findActiveFrame, hStmt]
          have hSIpf := @scopeInstrs_of_scopeBodyOf spec.engines eng _ _ _ hUSFrame (scopeBodyOf_of_getElem_condFalse hParentStmt hUSFrame)
          have hSBAgree := smp_scopeBodyOf_agree hParentSMP hUS parentFrame (List.Mem.head _) eid
            (mem_scopeIdsOf_of_getElem hParentStmt (by simp [scopeIdsOf]))
          rw [scopeInstrs_eq_scopeBodyOf hUS, hSBAgree, ← scopeInstrs_eq_scopeBodyOf hUSFrame, hSIpf]
          exact (scopeInstrs_idxOf_eq_instrsBefore_none hStmt hInstr hUIBody hAllE
            (scopeInstrs_nodup hUIBody hAllE)).symm
        · exfalso
          have hMemEBNone := mem_scopeInstrs_none_of_block_at_top hUIBody hAllE hStmt hInstr
          have hSIpf := @scopeInstrs_of_scopeBodyOf spec.engines eng _ _ _ hUSFrame (scopeBodyOf_of_getElem_condFalse hParentStmt hUSFrame)
          have hSBAgree := smp_scopeBodyOf_agree hParentSMP hUS parentFrame (List.Mem.head _) eid
            (mem_scopeIdsOf_of_getElem hParentStmt (by simp [scopeIdsOf]))
          have hMemEid : instr ∈ scopeInstrs spec.engines eng spec.body (some eid) := by
            rw [scopeInstrs_eq_scopeBodyOf hUS, hSBAgree, ← scopeInstrs_eq_scopeBodyOf hUSFrame, hSIpf]
            exact hMemEBNone
          have ⟨hS2, _⟩ := scopeInstrs_implies_loop_engine hUI hAllE hMem
          have ⟨hS3, _⟩ := scopeInstrs_implies_loop_engine hUI hAllE hMemEid
          rw [hS2] at hS3; exact hSid (Option.some.inj hS3).symm
      | none =>
        exfalso
        have hMemEBNone := mem_scopeInstrs_none_of_block_at_top hUIBody hAllE hStmt hInstr
        have hSIpf := @scopeInstrs_of_scopeBodyOf spec.engines eng _ _ _ hUSFrame (scopeBodyOf_of_getElem_condFalse hParentStmt hUSFrame)
        have hSBAgree := smp_scopeBodyOf_agree hParentSMP hUS parentFrame (List.Mem.head _) eid
          (mem_scopeIdsOf_of_getElem hParentStmt (by simp [scopeIdsOf]))
        have hMemEid : instr ∈ scopeInstrs spec.engines eng spec.body (some eid) := by
          rw [scopeInstrs_eq_scopeBodyOf hUS, hSBAgree, ← scopeInstrs_eq_scopeBodyOf hUSFrame, hSIpf]
          exact hMemEBNone
        have ⟨hS2, _⟩ := scopeInstrs_implies_loop_engine hUI hAllE hMem
        have ⟨hS3, _⟩ := scopeInstrs_implies_loop_engine hUI hAllE hMemEid
        rw [hS2] at hS3; exact absurd hS3 (by simp)
theorem instrAtPC_at_Tm1 {spec : Program} {ss : SpecState} {is : ImplState}
    {impl : ImplProgram} {alloc : PerScopeAllocR spec impl}
    (hSpecInv : SpecInv spec ss) (hPerScopeInv : PerScopeInv spec impl alloc ss is)
    (hUI : UniqueInstrIds spec.engines spec.body) (hUS : UniqueScopeIds spec.body)
    {e : EngineId} {frame : Frame} {rest : List Frame}
    {f : EngineId → List DataPathInstrId} {instr : DataPathInstrId}
    (hStack : (ss.pc e).stack = frame :: rest)
    (hStmt : frame.body[frame.stmtIdx]? = some (Stmt.block f))
    (hInstr : (f e)[(ss.pc e).instrIdx]? = some instr)
    {eng : EngineId} {loop : Option ScopeId}
    (hAllE : eng ∈ spec.engines)
    (hMem : instr ∈ scopeInstrs spec.engines eng spec.body loop)
    (he : eng = e)
    : ss.rc instr + inflightCount instr (ss.inflight eng) =
        totalEntriesOpt ss eng loop - 1 ∧
      (∀ j, j ∈ scopeInstrs spec.engines eng spec.body loop →
        (scopeInstrs spec.engines eng spec.body loop).idxOf j <
          (scopeInstrs spec.engines eng spec.body loop).idxOf instr →
        ss.rc j + inflightCount j (ss.inflight eng) = totalEntriesOpt ss eng loop) := by
  subst he
  constructor
  · exact hPerScopeInv.instrAtPC_atTm1 eng hAllE frame rest f instr hStack hStmt hInstr loop hMem
  · intro j hj hIdx
    -- instr is at T-1 (from instrAtPC_atTm1 PerScopeInv field)
    have hInstrTm1 := hPerScopeInv.instrAtPC_atTm1 eng hAllE frame rest f instr hStack hStmt hInstr loop hMem
    have ⟨hFwd, hBack⟩ := hPerScopeInv.pcComplete eng loop hAllE
    -- Case split on T >= 1 vs T = 0
    rcases Nat.eq_zero_or_pos (totalEntriesOpt ss eng loop) with hT0 | hT
    · -- T = 0: everything is at 0. Since T-1 = 0 (Nat), and Inv2 upper bound <= T = 0,
      -- all rc + ifCount = 0 = T. So j at T trivially.
      have ⟨hUp, _⟩ := hPerScopeInv.countBalance eng loop hAllE j hj
      rw [hT0] at hUp ⊢; omega
    · -- T >= 1: use pcComplete_kBound_eq_of_at_Tm1 to get idxOf instr >= kBound
      have hInstrGe := pcComplete_kBound_eq_of_at_Tm1 spec ss eng loop (scopeKBound spec ss eng loop) instr hFwd hBack hMem hInstrTm1 hT
      -- If idxOf j < kBound, then j is at T (from inv7 forward)
      by_cases hjlt : (scopeInstrs spec.engines eng spec.body loop).idxOf j < scopeKBound spec ss eng loop
      · exact hFwd j hj hjlt
      · -- idxOf instr = scopeKBound, so idxOf j < kBound, contradicting hjlt
        have hKBEq := scopeKBound_eq_idxOf_instrAtPC hSpecInv hUI hUS hAllE hStack hStmt hInstr hMem
        omega

/-- Inv7 preservation for loop entry (loopEnter, condTrue, condFalse).
    The new state pushes a frame and increments the loop iter history for `sid`. -/
theorem pcComplete_loopEntry_all {spec : Program} {ss ss' : SpecState}
    {eng0 : EngineId} {sid : ScopeId} {loopBody : List Stmt} {kind : FrameKind}
    {frame : Frame} {rest : List Frame}
    (hStack : (ss.pc eng0).stack = frame :: rest)
    (hKind : kind = .loop sid ∨ kind = .cond sid)
    (hNotBlock : ∀ f, frame.body[frame.stmtIdx]? ≠ some (Stmt.block f))
    (hPC_eng0 : ss'.pc eng0 = ⟨⟨loopBody, 0, kind⟩ :: frame :: rest, 0⟩)
    (hPC_ne : ∀ eng, eng ≠ eng0 → ss'.pc eng = ss.pc eng)
    (hRC : ss'.rc = ss.rc)
    (hIF : ss'.inflight = ss.inflight)
    (hTE_self : totalEntriesOpt ss' eng0 (some sid) = totalEntriesOpt ss eng0 (some sid) + 1)
    (hTE_ne_loop : ∀ loop, loop ≠ some sid → totalEntriesOpt ss' eng0 loop = totalEntriesOpt ss eng0 loop)
    (hTE_ne_eng : ∀ eng, eng ≠ eng0 → ∀ loop, totalEntriesOpt ss' eng loop = totalEntriesOpt ss eng loop)
    (hInv7 : ∀ eng loop, eng ∈ spec.engines → PCComplete spec ss eng loop (scopeKBound spec ss eng loop) ∧
      (∀ i, i ∈ scopeInstrs spec.engines eng spec.body loop →
        (scopeInstrs spec.engines eng spec.body loop).idxOf i ≥ scopeKBound spec ss eng loop →
        ss.rc i + inflightCount i (ss.inflight eng) = totalEntriesOpt ss eng loop - 1))
    (hAllAtT : ∀ i, i ∈ scopeInstrs spec.engines eng0 spec.body (some sid) →
        ss.rc i + inflightCount i (ss.inflight eng0) = totalEntriesOpt ss eng0 (some sid))
    (hEng0Mem : eng0 ∈ spec.engines)
    : ∀ eng loop, eng ∈ spec.engines → PCComplete spec ss' eng loop (scopeKBound spec ss' eng loop) ∧
      (∀ i, i ∈ scopeInstrs spec.engines eng spec.body loop →
        (scopeInstrs spec.engines eng spec.body loop).idxOf i ≥ scopeKBound spec ss' eng loop →
        ss'.rc i + inflightCount i (ss'.inflight eng) = totalEntriesOpt ss' eng loop - 1) := by
  intro eng loop hEngMem
  by_cases he : eng = eng0
  · subst he
    by_cases hsc : loop = some sid
    · subst hsc
      have hKB0 := scopeKBound_loopEntry_self (spec := spec) (sid := sid) (loopBody := loopBody) hStack hKind
      have hKBpc : scopeKBound spec ss' eng (some sid) = 0 := by
        have := scopeKBound_eq_of_pc_eq (spec := spec) (ss' := ss')
          (ss := { ss with pc := funUpdate ss.pc eng { stack := ⟨loopBody, 0, kind⟩ :: frame :: rest, instrIdx := 0 } })
          (eng := eng) (loop := some sid) (by simp [funUpdate, hPC_eng0])
        rw [this]; exact hKB0
      rw [hKBpc]
      constructor
      · intro i _ hlt; omega
      · intro i hi _
        rw [hRC, hIF, hTE_self]
        have hAtT := hAllAtT i hi
        omega
    · have hKBeq : scopeKBound spec ss' eng loop = scopeKBound spec ss eng loop := by
        have := scopeKBound_eq_of_pc_eq (spec := spec) (ss' := ss')
          (ss := { ss with pc := funUpdate ss.pc eng { stack := ⟨loopBody, 0, kind⟩ :: frame :: rest, instrIdx := 0 } })
          (eng := eng) (loop := loop) (by simp [funUpdate, hPC_eng0])
        rw [this]
        exact scopeKBound_loopEntry_other (spec := spec) (loopBody := loopBody) hStack hKind hsc hNotBlock
      have ⟨hFwd, hBack⟩ := hInv7 eng loop hEngMem
      exact pcComplete_of_same_kBound hKBeq hRC (congrFun hIF eng) (hTE_ne_loop loop hsc) hFwd hBack
  · have hKBeq : scopeKBound spec ss' eng loop = scopeKBound spec ss eng loop :=
      scopeKBound_eq_of_pc_eq (hPC_ne eng he)
    have ⟨hFwd, hBack⟩ := hInv7 eng loop hEngMem
    exact pcComplete_of_same_kBound hKBeq hRC (congrFun hIF eng) (hTE_ne_eng eng he loop) hFwd hBack

-- Goal type for PerScopeInv preservation through a SpecStep (shared by sub-lemmas)
abbrev PerScopeInvStepGoal (spec : Program) (ss' : SpecState) : Prop :=
  (∀ eng loop, eng ∈ spec.engines → CountBalance spec ss' eng loop) ∧
  (∀ eng loop, eng ∈ spec.engines → IssueOrder spec ss' eng loop) ∧
  (∀ eng loop, eng ∈ spec.engines → QueueOrdered spec ss' eng loop) ∧
  (∀ eng loop, eng ∈ spec.engines → RCMono spec ss' eng loop) ∧
  (∀ eng loop, eng ∈ spec.engines → RCBound spec ss' eng loop) ∧
  (∀ eng loop, eng ∈ spec.engines →
    PCComplete spec ss' eng loop (scopeKBound spec ss' eng loop) ∧
    (∀ i, i ∈ scopeInstrs spec.engines eng spec.body loop →
      (scopeInstrs spec.engines eng spec.body loop).idxOf i ≥ scopeKBound spec ss' eng loop →
      ss'.rc i + inflightCount i (ss'.inflight eng) =
        totalEntriesOpt ss' eng loop - 1)) ∧
  (∀ eng, eng ∈ spec.engines → ∀ frame rest f instr,
    (ss'.pc eng).stack = frame :: rest →
    frame.body[frame.stmtIdx]? = some (Stmt.block f) →
    (f eng)[(ss'.pc eng).instrIdx]? = some instr →
    ∀ loop, instr ∈ scopeInstrs spec.engines eng spec.body loop →
      ss'.rc instr + inflightCount instr (ss'.inflight eng) =
        totalEntriesOpt ss' eng loop - 1)

-- PerScopeInv preservation: issue case (extracted for readability)
theorem perScopeInv_spec_step_issue (spec : Program) (impl : ImplProgram) (alloc : PerScopeAllocR spec impl)
    (eng0 : EngineId) (ss : SpecState)
    (frame : Frame) (rest : List Frame) (f : EngineId → List DataPathInstrId) (instr : DataPathInstrId)
    (hStack : (ss.pc eng0).stack = frame :: rest)
    (hStmt : frame.body[frame.stmtIdx]? = some (Stmt.block f))
    (hInstr : (f eng0)[(ss.pc eng0).instrIdx]? = some instr)
    (hDeps : depSatisfied spec (spec.depGraph instr) instr ss eng0 = true)
    (hPerScopeInv : PerScopeInv spec impl alloc ss (is : ImplState))
    (hSpecInv : SpecInv spec ss)
    (hUniqueInstr : UniqueInstrIds spec.engines spec.body)
    (hUniq : UniqueScopeIds spec.body)
    (hEng0Mem : eng0 ∈ spec.engines)
    : PerScopeInvStepGoal spec
        { ss with
          pc := funUpdate ss.pc eng0
            { (ss.pc eng0) with instrIdx := (ss.pc eng0).instrIdx + 1 }
          inflight := funUpdate ss.inflight eng0
            (ss.inflight eng0 ++ [(instr, Phase.issued)]) } := by
  have hIE_issue := hInstrEng_of_issue hSpecInv hUniqueInstr hUniq hEng0Mem hStack hStmt hInstr
  have hAtTm1_full : ∀ eng loop, instr ∈ scopeInstrs spec.engines eng spec.body loop →
      eng = eng0 →
      (ss.rc instr + inflightCount instr (ss.inflight eng) = totalEntriesOpt ss eng loop - 1) ∧
      (∀ j, j ∈ scopeInstrs spec.engines eng spec.body loop →
        (scopeInstrs spec.engines eng spec.body loop).idxOf j <
          (scopeInstrs spec.engines eng spec.body loop).idxOf instr →
        ss.rc j + inflightCount j (ss.inflight eng) = totalEntriesOpt ss eng loop) := by
    intro eng loop hMem he
    exact instrAtPC_at_Tm1 hSpecInv hPerScopeInv hUniqueInstr hUniq hStack hStmt hInstr (he ▸ hEng0Mem) hMem he
  have hAtTm1 : ∀ eng loop, instr ∈ scopeInstrs spec.engines eng spec.body loop →
      eng = eng0 → ss.rc instr + inflightCount instr (ss.inflight eng) =
        totalEntriesOpt ss eng loop - 1 := fun eng loop hMem he => (hAtTm1_full eng loop hMem he).1
  have hLater : ∀ eng loop, ∀ j, j ∈ scopeInstrs spec.engines eng spec.body loop →
      (scopeInstrs spec.engines eng spec.body loop).idxOf instr <
        (scopeInstrs spec.engines eng spec.body loop).idxOf j →
      eng = eng0 → ss.rc j + inflightCount j (ss.inflight eng) =
        totalEntriesOpt ss eng loop - 1 := by
    intro eng loop j hj hIdx he; subst he
    have ⟨hFwd, hBack⟩ := hPerScopeInv.pcComplete eng loop hEng0Mem
    have hMemI : instr ∈ scopeInstrs spec.engines eng spec.body loop := by
      have h1 := List.idxOf_lt_length_of_mem hj
      by_contra h; have h2 := List.idxOf_eq_length h; omega
    have hInstrTm1 := hAtTm1 eng loop hMemI rfl
    rcases Nat.eq_zero_or_pos (totalEntriesOpt ss eng loop) with hT0 | hT
    · have ⟨hUp, _⟩ := hPerScopeInv.countBalance eng loop hEng0Mem j hj; rw [hT0] at hUp ⊢; omega
    · have hInstrGe := pcComplete_kBound_eq_of_at_Tm1 spec ss eng loop (scopeKBound spec ss eng loop) instr hFwd hBack hMemI hInstrTm1 hT
      exact hBack j hj (by omega)
  have hT : ∀ eng loop, instr ∈ scopeInstrs spec.engines eng spec.body loop →
      eng = eng0 → totalEntriesOpt ss eng loop ≥ 1 := by
    intro eng loop hMem he; subst he; cases loop with
    | none => simp [totalEntriesOpt]
    | some sid =>
      obtain ⟨fr, hfa⟩ := findActiveFrame_isTop_of_instrAtPC hSpecInv hUniqueInstr hUniq hEng0Mem hStack hStmt hInstr hMem
      have hfr := findActiveFrame_isTop_eq hfa; subst hfr
      have hOnStack : sid ∈ loopsOnStack ss eng := by
        simp only [loopsOnStack, hStack]
        by_contra hNotIn
        exact absurd hfa (by rw [findActiveFrame_none_of_not_in_enclosing hNotIn]; simp)
      exact hSpecInv.activeLoopPos eng sid hOnStack
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro eng loop hE
    by_cases hMemInstr : instr ∈ scopeInstrs spec.engines eng spec.body loop
    · exact countBalance_issue spec ss eng0 eng loop instr
        (hPerScopeInv.countBalance eng loop hE) (hPerScopeInv.issueOrder eng loop hE)
        (hAtTm1 eng loop) (hLater eng loop) (fun he => hT eng loop hMemInstr he)
    · intro i hi
      have hNe : i ≠ instr := fun h => hMemInstr (h ▸ hi)
      have hOld := hPerScopeInv.countBalance eng loop hE i hi
      constructor
      · show ss.rc i + inflightCount i ((funUpdate ss.inflight eng0 (ss.inflight eng0 ++ [(instr, Phase.issued)])) eng) ≤ totalEntriesOpt ss eng loop
        simp only [funUpdate_apply]
        by_cases he : eng = eng0
        · subst he; simp only [ite_true, inflightCount_append, inflightCount_singleton]
          simp only [show (instr == i) = false from beq_eq_false_iff_ne.mpr (Ne.symm hNe)]; exact hOld.1
        · simp only [if_neg he]; exact hOld.1
      · show ss.rc i + inflightCount i ((funUpdate ss.inflight eng0 (ss.inflight eng0 ++ [(instr, Phase.issued)])) eng) ≥ totalEntriesOpt ss eng loop - 1
        simp only [funUpdate_apply]
        by_cases he : eng = eng0
        · subst he; simp only [ite_true, inflightCount_append, inflightCount_singleton]
          simp only [show (instr == i) = false from beq_eq_false_iff_ne.mpr (Ne.symm hNe)]; exact hOld.2
        · simp only [if_neg he]; exact hOld.2
  · intro eng loop hE
    by_cases hMemInstr : instr ∈ scopeInstrs spec.engines eng spec.body loop
    · exact issueOrder_issue spec ss eng0 eng loop instr
        (hPerScopeInv.issueOrder eng loop hE) (hPerScopeInv.countBalance eng loop hE)
        (by intro hMem he j hj hIdx; subst he
            have ⟨hFwd, _⟩ := hPerScopeInv.pcComplete eng loop hE
            have hKB := scopeKBound_eq_idxOf_instrAtPC hSpecInv hUniqueInstr hUniq hE hStack hStmt hInstr hMem
            exact hFwd j hj (by omega))
        (hAtTm1 eng loop) (fun he => hT eng loop hMemInstr he)
    · unfold IssueOrder; simp only
      intro i j hi hj hIdx hjT
      have hNe_i : i ≠ instr := fun h => hMemInstr (h ▸ hi)
      have hNe_j : j ≠ instr := fun h => hMemInstr (h ▸ hj)
      simp only [totalEntriesOpt, totalEntries] at hjT ⊢
      simp only [funUpdate_apply] at hjT ⊢
      by_cases he : eng = eng0
      · subst he; simp only [ite_true, inflightCount_append, inflightCount_singleton] at hjT ⊢
        simp only [show (instr == j) = false from beq_eq_false_iff_ne.mpr (Ne.symm hNe_j)] at hjT
        simp only [show (instr == i) = false from beq_eq_false_iff_ne.mpr (Ne.symm hNe_i)]
        exact hPerScopeInv.issueOrder eng loop hE i j hi hj hIdx hjT
      · simp only [if_neg he] at hjT ⊢
        exact hPerScopeInv.issueOrder eng loop hE i j hi hj hIdx hjT
  · intro eng loop hE; exact queueOrdered_issue spec ss eng0 eng loop instr
      (hPerScopeInv.queueOrdered eng loop hE) (by
        intro p ip pp hGetP hMemIP hMemInstr he; subst he
        have hCOB_tail : countOccsBefore instr (ss.inflight eng ++ [(instr, Phase.issued)]) (ss.inflight eng).length = inflightCount instr (ss.inflight eng) := by
          have : ∀ (l : List (DataPathInstrId × Phase)) (suffix : List (DataPathInstrId × Phase)),
              countOccsBefore instr (l ++ suffix) l.length = inflightCount instr l := by
            intro l; induction l with
            | nil => simp [inflightCount]
            | cons hd rest ih =>
              intro suffix; obtain ⟨hd_id, hd_ph⟩ := hd
              simp [countOccsBefore, inflightCount, ih suffix]
          exact this (ss.inflight eng) [(instr, Phase.issued)]
        have hTailTag : entryTag instr ss.rc (ss.inflight eng ++ [(instr, Phase.issued)]) (ss.inflight eng).length = ss.rc instr + inflightCount instr (ss.inflight eng) + 1 := by
          simp [entryTag, hCOB_tail]
        have hInstrTm1 := hAtTm1 eng loop hMemInstr rfl
        have hTge := hT eng loop hMemInstr rfl
        have hTailTag_eq_T : entryTag instr ss.rc (ss.inflight eng ++ [(instr, Phase.issued)]) (ss.inflight eng).length = totalEntriesOpt ss eng loop := by
          rw [hTailTag]; omega
        have hpLt : p < (ss.inflight eng).length := by
          exact List.getElem?_eq_some_iff.mp hGetP |>.1
        have hCOB_bound : countOccsBefore ip (ss.inflight eng) p + 1 ≤ inflightCount ip (ss.inflight eng) := by
          suffices h : countOccsBefore ip (ss.inflight eng) (p + 1) ≤ inflightCount ip (ss.inflight eng) by
            have : countOccsBefore ip (ss.inflight eng) (p + 1) = countOccsBefore ip (ss.inflight eng) p + 1 := by
              have : ∀ (l : List (DataPathInstrId × Phase)) (n : Nat), l[n]? = some (ip, pp) →
                  countOccsBefore ip l (n + 1) = countOccsBefore ip l n + 1 := by
                intro l; induction l with
                | nil => simp
                | cons hd rest ih =>
                  intro n hGet; obtain ⟨hd_id, hd_ph⟩ := hd
                  cases n with
                  | zero =>
                    simp [] at hGet
                    obtain ⟨rfl, _⟩ := hGet
                    simp [countOccsBefore]
                  | succ m =>
                    simp only [countOccsBefore]
                    have hGet' : rest[m]? = some (ip, pp) := by simpa using hGet
                    rw [ih m hGet']; omega
              exact this (ss.inflight eng) p hGetP
            omega
          suffices ∀ (l : List (DataPathInstrId × Phase)) (n : Nat), n ≤ l.length →
              countOccsBefore ip l n ≤ inflightCount ip l by
            exact this (ss.inflight eng) (p + 1) hpLt
          intro l; induction l with
          | nil => intro n hn; simp at hn; subst hn; simp [countOccsBefore, inflightCount]
          | cons hd rest ih =>
            intro n hn; obtain ⟨hd_id, hd_ph⟩ := hd
            cases n with
            | zero => simp [countOccsBefore]
            | succ m =>
              simp only [countOccsBefore, inflightCount]
              have hm : m ≤ rest.length := by simp at hn; omega
              have := ih m hm; omega
        have hTagBound : entryTag ip ss.rc (ss.inflight eng) p ≤ totalEntriesOpt ss eng loop := by
          simp only [entryTag]
          have ⟨hUp, _⟩ := hPerScopeInv.countBalance eng loop hE ip hMemIP
          omega
        rcases Nat.lt_or_eq_of_le hTagBound with hLt | hEq
        · left; rw [hTailTag_eq_T]; exact hLt
        · right
          constructor
          · rw [hTailTag_eq_T]; exact hEq
          · have hIPAtT : ss.rc ip + inflightCount ip (ss.inflight eng) = totalEntriesOpt ss eng loop := by
              have ⟨hUp, _⟩ := hPerScopeInv.countBalance eng loop hE ip hMemIP
              simp only [entryTag] at hEq; omega
            have ⟨hFwd, hBack⟩ := hPerScopeInv.pcComplete eng loop hE
            have hKB := scopeKBound_eq_idxOf_instrAtPC hSpecInv hUniqueInstr hUniq hE hStack hStmt hInstr hMemInstr
            have hIPLt : (scopeInstrs spec.engines eng spec.body loop).idxOf ip < scopeKBound spec ss eng loop := by
              by_contra hge
              have hge := Nat.le_of_not_lt hge
              have := hBack ip hMemIP hge
              omega
            rw [hKB] at hIPLt; exact hIPLt)
  · intro eng loop hE; exact rcMono_issue spec ss eng0 eng loop instr (hPerScopeInv.rcMono eng loop hE)
  · intro eng loop hE; exact rcBound_issue spec ss eng0 eng loop instr (hPerScopeInv.rcBound eng loop hE)
  · intro eng loop hE
    by_cases he : eng = eng0
    · subst he
      have ⟨hOldFwd, hOldBack⟩ := hPerScopeInv.pcComplete eng loop hE
      by_cases hMemLoop : instr ∈ scopeInstrs spec.engines eng spec.body loop
      · have hOldKB := scopeKBound_eq_idxOf_instrAtPC hSpecInv hUniqueInstr hUniq hE hStack hStmt hInstr hMemLoop
        have hND := scopeInstrs_nodup (loop := loop) hUniqueInstr hE
        obtain ⟨fr, hfa⟩ := findActiveFrame_isTop_of_instrAtPC hSpecInv hUniqueInstr hUniq hE hStack hStmt hInstr hMemLoop
        have hfr := findActiveFrame_isTop_eq hfa; subst hfr
        have hNewKB : scopeKBound spec { ss with pc := funUpdate ss.pc eng { stack := (ss.pc eng).stack, instrIdx := (ss.pc eng).instrIdx + 1 }, inflight := funUpdate ss.inflight eng (ss.inflight eng ++ [(instr, Phase.issued)]) } eng loop = (scopeInstrs spec.engines eng spec.body loop).idxOf instr + 1 := by
          simp only [scopeKBound, funUpdate, ite_true, hStack, hfa, hStmt]
          simp only [scopeKBound, hStack, hfa, hStmt] at hOldKB; simp at hOldKB
          have : instrsBefore spec.engines eng fr.body fr.stmtIdx + ((ss.pc eng).instrIdx + 1) =
              (instrsBefore spec.engines eng fr.body fr.stmtIdx + (ss.pc eng).instrIdx) + 1 := by omega
          rw [this, hOldKB]
        simp only [hNewKB]
        constructor
        · intro i hi hlt
          simp only [funUpdate, ite_true, totalEntriesOpt, totalEntries]
          rw [inflightCount_append, inflightCount_singleton]
          by_cases hii : instr = i
          · subst hii; simp
            have hTm1 := hAtTm1 eng loop hMemLoop rfl
            have hTge := hT eng loop hMemLoop rfl
            show ss.rc instr + (inflightCount instr (ss.inflight eng) + 1) = totalEntriesOpt ss eng loop
            omega
          · simp [show (instr == i) = false from beq_eq_false_iff_ne.mpr hii, Nat.add_zero]
            have hIdxLt : (scopeInstrs spec.engines eng spec.body loop).idxOf i < (scopeInstrs spec.engines eng spec.body loop).idxOf instr := by
              have hle := Nat.lt_succ_iff.mp hlt
              rcases Nat.eq_or_lt_of_le hle with heq | hlt'; swap; exact hlt'
              exact absurd (nodup_idxOf_eq_of_mem hND hi hMemLoop heq) (Ne.symm hii)
            rw [← hOldKB] at hIdxLt
            exact hOldFwd i hi hIdxLt
        · intro i hi hge
          simp only [funUpdate, ite_true, totalEntriesOpt, totalEntries]
          have hIdxGt : (scopeInstrs spec.engines eng spec.body loop).idxOf instr < (scopeInstrs spec.engines eng spec.body loop).idxOf i := by omega
          have hNe : i ≠ instr := by intro heq; subst heq; omega
          rw [inflightCount_append, inflightCount_singleton]
          simp [show (instr == i) = false from beq_eq_false_iff_ne.mpr (Ne.symm hNe), Nat.add_zero]
          exact hLater eng loop i hi hIdxGt rfl
      · have hNe : ∀ i, i ∈ scopeInstrs spec.engines eng spec.body loop → i ≠ instr :=
          fun i hi heq => hMemLoop (heq ▸ hi)
        have hKBeq : scopeKBound spec { ss with pc := funUpdate ss.pc eng { stack := (ss.pc eng).stack, instrIdx := (ss.pc eng).instrIdx + 1 }, inflight := funUpdate ss.inflight eng (ss.inflight eng ++ [(instr, Phase.issued)]) } eng loop = scopeKBound spec ss eng loop := by
          simp only [scopeKBound, funUpdate, ite_true, hStack]
          cases hfa : findActiveFrame (frame :: rest) loop with
          | none => rfl
          | some fp =>
            obtain ⟨fr, isTop⟩ := fp; simp; cases isTop
            · rfl
            · exfalso
              have hfr := findActiveFrame_isTop_eq hfa; subst hfr
              exact hMemLoop (mem_scopeInstrs_of_findActiveFrame_isTop hSpecInv hUniqueInstr hUniq hE hStack hStmt hInstr hfa)
        simp only [hKBeq]
        constructor
        · intro i hi hlt
          simp only [funUpdate, ite_true, totalEntriesOpt, totalEntries]
          rw [inflightCount_append, inflightCount_singleton]
          simp only [show (instr == i) = false from beq_eq_false_iff_ne.mpr (Ne.symm (hNe i hi))]
          exact hOldFwd i hi hlt
        · intro i hi hge
          simp only [funUpdate, ite_true, totalEntriesOpt, totalEntries]
          rw [inflightCount_append, inflightCount_singleton]
          simp only [show (instr == i) = false from beq_eq_false_iff_ne.mpr (Ne.symm (hNe i hi))]
          exact hOldBack i hi hge
    · have hIFne : (funUpdate ss.inflight eng0 (ss.inflight eng0 ++ [(instr, Phase.issued)])) eng = ss.inflight eng := by simp [funUpdate, he]
      have ⟨hFwd, hBack⟩ := hPerScopeInv.pcComplete eng loop hE
      constructor <;> intro i hi hlt <;> simp only at hlt ⊢ <;> simp only [funUpdate, if_neg he, totalEntriesOpt, totalEntries] at hlt ⊢
      · exact hFwd i hi (by simp [scopeKBound, funUpdate, he] at hlt; exact hlt)
      · exact hBack i hi (by simp [scopeKBound, funUpdate, he] at hlt; exact hlt)
  · intro eng hE frame' rest' f' instr' hStack' hStmt' hInstr' loop hMem'
    by_cases he : eng = eng0
    · subst he
      simp only [funUpdate, ite_true] at hStack' hInstr'
      rw [hStack] at hStack'; cases hStack'
      rw [hStmt] at hStmt'; cases hStmt'
      have hSMP := hSpecInv.wellFormedPC eng
      rw [hStack] at hSMP
      have hUIFrame := smp_uniqueInstrIds hSMP hUniqueInstr frame (List.Mem.head _)
      have hFNodup : (f eng).Nodup := by
        have : ∀ {body : List Stmt} {n : Nat} {g : EngineId → List DataPathInstrId},
            UniqueInstrIds spec.engines body → body[n]? = some (Stmt.block g) →
            ∀ e, (g e).Nodup := by
          intro body n g hUI' hIdx e
          induction body generalizing n with
          | nil => simp at hIdx
          | cons s rest' ih =>
            cases n with
            | zero =>
              cases s <;> simp at hIdx
              · obtain ⟨rfl⟩ := hIdx; cases hUI'; next hND _ _ _ => exact hND e
            | succ m =>
              simp at hIdx
              exact ih (by cases hUI' with | block => assumption | loop => assumption | cond => assumption) hIdx
        exact this hUIFrame hStmt eng
      have hNe : instr' ≠ instr := by
        intro heq
        have : ∀ (l : List DataPathInstrId) (x : DataPathInstrId) (i : Nat),
            l.Nodup → l[i]? = some x → l[i + 1]? = some x → False := by
          intro l x i hnd hgi hgj
          induction l generalizing i with
          | nil => simp at hgi
          | cons a as ih =>
            cases i with
            | zero =>
              simp at hgi hgj
              exact (List.nodup_cons.mp hnd).1 (hgi ▸ List.mem_of_getElem? hgj)
            | succ n =>
              simp at hgi hgj
              exact ih n (List.nodup_cons.mp hnd).2 hgi hgj
        exact this (f eng) instr' _ hFNodup (by rw [heq]; exact hInstr) hInstr'
      simp only [funUpdate, ite_true]
      rw [inflightCount_append, inflightCount_singleton]
      simp only [show (instr == instr') = false from beq_eq_false_iff_ne.mpr (Ne.symm hNe)]
      change ss.rc instr' + inflightCount instr' (ss.inflight eng) =
        totalEntriesOpt ss eng loop - 1
      rcases Nat.eq_zero_or_pos (totalEntriesOpt ss eng loop) with hT0 | hTpos
      · have ⟨hUp, _⟩ := hPerScopeInv.countBalance eng loop hE instr' hMem'
        rw [hT0] at hUp ⊢; omega
      · have ⟨_, hBack⟩ := hPerScopeInv.pcComplete eng loop hE
        exact hBack instr' hMem' (by
          let ss' : SpecState := { ss with pc := funUpdate ss.pc eng { (ss.pc eng) with instrIdx := (ss.pc eng).instrIdx + 1 }, inflight := funUpdate ss.inflight eng (ss.inflight eng ++ [(instr, Phase.issued)]) }
          have hSpecInv' : SpecInv spec ss' := specInv_step spec eng ss ss' hUniq hSpecInv
            (SpecStep.issue eng ss hE frame rest f instr hStack hStmt hInstr hDeps)
          have hNewStack : (ss'.pc eng).stack = frame :: rest := by simp [ss', funUpdate, hStack]
          have hNewInstr : (f eng)[(ss'.pc eng).instrIdx]? = some instr' := by simp [ss', funUpdate]; exact hInstr'
          have hKBnew := scopeKBound_eq_idxOf_instrAtPC hSpecInv' hUniqueInstr hUniq hE hNewStack hStmt hNewInstr hMem'
          have hStack' : (ss'.pc eng).stack = frame :: rest := by simp [ss', funUpdate, hStack]
          simp only [scopeKBound, hStack', hStack] at hKBnew ⊢
          cases hfa : findActiveFrame (frame :: rest) loop with
          | none => simp [hfa] at hKBnew ⊢; omega
          | some fp =>
            obtain ⟨fr, isTop⟩ := fp
            simp [hfa] at hKBnew ⊢; cases isTop
            · simp at hKBnew ⊢; omega
            · have hfr := findActiveFrame_isTop_eq hfa; subst hfr; simp only [hStmt, ite_true] at hKBnew ⊢; have hPC : (ss'.pc eng).instrIdx = (ss.pc eng).instrIdx + 1 := (by simp [ss', funUpdate]); rw [hPC] at hKBnew; omega)
    · simp only [funUpdate, if_neg he] at hStack' hInstr' ⊢
      exact hPerScopeInv.instrAtPC_atTm1 eng hE frame' rest' f' instr' hStack' hStmt' hInstr' loop hMem'
