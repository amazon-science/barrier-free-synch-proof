import SemaAlloc.PerScopeIssue

private theorem invs2to6_loopEntry (spec : Program) (impl : ImplProgram) (alloc : PerScopeAllocR spec impl)
    (eng0 : EngineId) (ss : SpecState) (is : ImplState)
    (hPerScopeInv : PerScopeInv spec impl alloc ss is)
    (sid : ScopeId) (encLoops : List ScopeId)
    (hAllAtT : ∀ eng loop, loop = some sid → eng = eng0 →
      ∀ i, i ∈ scopeInstrs spec.engines eng spec.body loop →
        ss.rc i + inflightCount i (ss.inflight eng) = totalEntriesOpt ss eng loop)
    : (∀ eng loop, eng ∈ spec.engines → CountBalance spec
        { ss with scopeEntryHistory := incrScopeEntryHistory ss eng0 sid encLoops } eng loop) ∧
      (∀ eng loop, eng ∈ spec.engines → IssueOrder spec
        { ss with scopeEntryHistory := incrScopeEntryHistory ss eng0 sid encLoops } eng loop) ∧
      (∀ eng loop, eng ∈ spec.engines → QueueOrdered spec
        { ss with scopeEntryHistory := incrScopeEntryHistory ss eng0 sid encLoops } eng loop) ∧
      (∀ eng loop, eng ∈ spec.engines → RCMono spec
        { ss with scopeEntryHistory := incrScopeEntryHistory ss eng0 sid encLoops } eng loop) ∧
      (∀ eng loop, eng ∈ spec.engines → RCBound spec
        { ss with scopeEntryHistory := incrScopeEntryHistory ss eng0 sid encLoops } eng loop) :=
  ⟨fun eng loop hE => countBalance_loopEntry spec ss eng0 eng loop sid encLoops (hPerScopeInv.countBalance eng loop hE) (hAllAtT eng loop),
   fun eng loop hE => issueOrder_loopEntry spec ss eng0 eng loop sid encLoops (hPerScopeInv.issueOrder eng loop hE) (hAllAtT eng loop),
   fun eng loop hE => queueOrdered_loopEntry spec ss eng0 eng loop sid encLoops (hPerScopeInv.queueOrdered eng loop hE),
   fun eng loop hE => rcMono_loopEntry spec ss eng0 eng loop sid encLoops (hPerScopeInv.rcMono eng loop hE),
   fun eng loop hE => rcBound_loopEntry spec ss eng0 eng loop sid encLoops (hPerScopeInv.rcBound eng loop hE)⟩

set_option hygiene false in
macro "inv7_loop_entry_args " sid:ident : tactic => `(tactic| (
  · simp [funUpdate]
  · intro eng hne; simp [funUpdate, hne]
  · rfl
  · rfl
  · simp [totalEntriesOpt, totalEntries, incrScopeEntryHistory_totalEntries]
  · intro loop hsc; cases loop with
    | none => simp [totalEntriesOpt]
    | some sid' =>
      have hne : sid' ≠ $sid := fun h => hsc (congrArg some h)
      simp [totalEntriesOpt, totalEntries, incrScopeEntryHistory_ne_sid hne]
  · intro eng hne; intro loop; cases loop with
    | none => simp [totalEntriesOpt]
    | some sid => simp [totalEntriesOpt, totalEntries, incrScopeEntryHistory_ne_engine hne]
  · exact hPerScopeInv.pcComplete
  · exact hAllAtT_loop eng0 (some $sid) rfl rfl
  · exact hE))

-- instrAtPC_atTm1: eng ≠ eng0 branch for loop-entry cases (loopEnter, condTrue, condFalse)
set_option hygiene false in
macro "instrAtPC_atTm1_ne_engine" : tactic => `(tactic| (
  simp only [funUpdate, if_neg he] at hStack1 hInstr1
  have hOld := hPerScopeInv.instrAtPC_atTm1 eng hE' frame1 rest1 f1 instr1 hStack1 hStmt1 hInstr1 loop hMem1
  simp only [totalEntriesOpt, totalEntries] at hOld ⊢
  cases loop with
  | none => exact hOld
  | some sid' => simp only [] at hOld ⊢; rw [incrScopeEntryHistory_ne_engine he]; exact hOld))

-- instrAtPC_atTm1: full eng=eng0 branch for condTrue/condFalse loop-entry cases
set_option hygiene false in
macro "instrAtPC_atTm1_cond_entry " sid:ident loopBody:ident specStep:term : tactic => `(tactic| (
  subst he; simp only [funUpdate, ite_true] at hStack1 hInstr1
  obtain ⟨rfl, rfl⟩ := List.cons.inj hStack1
  have hNotBlock : ∀ f, frame.body[frame.stmtIdx]? ≠ some (Stmt.block f) := by intro f; rw [hStmt]; simp
  by_cases hsc : loop = some $sid
  · subst hsc
    have hAtT := hAllAtT_loop eng (some $sid) rfl rfl instr1 hMem1
    simp only [totalEntriesOpt, totalEntries] at hAtT ⊢
    simp only [incrScopeEntryHistory_totalEntries]; omega
  · have ⟨_, hBack⟩ := hPerScopeInv.pcComplete eng loop hE
    have hOld := hBack instr1 hMem1 (by
      let ss' : SpecState := { ss with
        pc := funUpdate ss.pc eng { stack := ⟨$loopBody, 0, .cond $sid⟩ :: frame :: rest, instrIdx := 0 }
        controlState := funUpdate ss.controlState eng (spec.controlOp eng $sid (ss.controlState eng))
        scopeEntryHistory := incrScopeEntryHistory ss eng $sid (enclosingLoopsFromStack (frame :: rest)) }
      have hSpecInv' : SpecInv spec ss' := specInv_step spec eng ss ss' hUniq hSpecInv ($specStep)
      have hNewStack : (ss'.pc eng).stack = ⟨$loopBody, 0, .cond $sid⟩ :: frame :: rest := by simp [ss', funUpdate]
      have hNewInstr : (f1 eng)[(ss'.pc eng).instrIdx]? = some instr1 := by simp [ss', funUpdate]; exact hInstr1
      have hKBnew := scopeKBound_eq_idxOf_instrAtPC hSpecInv' hUniqueInstr hUniq hE' hNewStack hStmt1 hNewInstr hMem1
      have hKBeq := scopeKBound_loopEntry_other (spec := spec) (loopBody := $loopBody) hStack (Or.inr rfl) hsc hNotBlock
      rw [← hKBeq, ← scopeKBound_eq_of_pc_eq (show ss'.pc eng = ({ ss with pc := funUpdate ss.pc eng { stack := ⟨$loopBody, 0, .cond $sid⟩ :: frame :: rest, instrIdx := 0 } } : SpecState).pc eng from by simp [ss', funUpdate])]
      omega)
    cases loop with
    | none => simp [totalEntriesOpt] at hOld ⊢; exact hOld
    | some sid' =>
      simp [totalEntriesOpt, totalEntries] at hOld ⊢
      have hne : sid' ≠ $sid := fun h => hsc (congrArg some h)
      simp [incrScopeEntryHistory_ne_sid hne]; exact hOld))

-- PerScopeInv preservation through a SpecStep
theorem perScopeInv_spec_step (spec : Program) (impl : ImplProgram) (alloc : PerScopeAllocR spec impl)
    (eng0 : EngineId) (ss ss' : SpecState)
    (hSpecStep : SpecStep spec eng0 ss ss')
    (hPerScopeInv : PerScopeInv spec impl alloc ss (is : ImplState))
    (hSpecInv : SpecInv spec ss)
    (hUniqueInstr : UniqueInstrIds spec.engines spec.body)
    (hUniq : UniqueScopeIds spec.body)
    : PerScopeInvStepGoal spec ss' := by
  cases hSpecStep with
  | retire hE instr rest hHead =>
    have hIE := hInstrEng_of_inflight hSpecInv hUniqueInstr hUniq hHead
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro eng loop hE; exact countBalance_retire spec ss eng0 eng loop instr Phase.committed rest hHead (hPerScopeInv.countBalance eng loop hE) (hIE eng hE loop)
    · intro eng loop hE; exact issueOrder_retire spec ss eng0 eng loop instr Phase.committed rest hHead (hPerScopeInv.issueOrder eng loop hE) (hPerScopeInv.countBalance eng loop hE) (hIE eng hE loop)
    · intro eng loop hE; exact queueOrdered_retire spec ss eng0 eng loop instr Phase.committed rest hHead (hPerScopeInv.queueOrdered eng loop hE) (hIE eng hE loop)
    · intro eng loop hE; by_cases he : eng = eng0
      · subst he; exact rcMono_retire spec ss eng loop instr rest hHead (hPerScopeInv.countBalance eng loop hE) (hPerScopeInv.issueOrder eng loop hE) (hPerScopeInv.queueOrdered eng loop hE) (hPerScopeInv.rcMono eng loop hE) (hPerScopeInv.rcBound eng loop hE)
      · -- eng ≠ eng0: inflight unchanged, instr ∉ scopeInstrs → rc unchanged → Inv5 same
        intro i j hi hj hIdx
        have hni : i ≠ instr := fun h => hIE eng hE loop he (h ▸ hi)
        have hnj : j ≠ instr := fun h => hIE eng hE loop he (h ▸ hj)
        show funUpdate ss.rc instr (ss.rc instr + 1) j ≤
          funUpdate ss.rc instr (ss.rc instr + 1) i
        simp [funUpdate, hni, hnj]
        exact hPerScopeInv.rcMono eng loop hE i j hi hj hIdx
    · intro eng loop hE; by_cases he : eng = eng0
      · subst he; exact rcBound_retire spec ss eng loop instr rest hHead (hPerScopeInv.countBalance eng loop hE) (hPerScopeInv.issueOrder eng loop hE) (hPerScopeInv.queueOrdered eng loop hE) (hPerScopeInv.rcMono eng loop hE) (hPerScopeInv.rcBound eng loop hE)
      · intro i j hi hj
        have hni : i ≠ instr := fun h => hIE eng hE loop he (h ▸ hi)
        have hnj : j ≠ instr := fun h => hIE eng hE loop he (h ▸ hj)
        show funUpdate ss.rc instr (ss.rc instr + 1) i ≤
          funUpdate ss.rc instr (ss.rc instr + 1) j + 1
        simp [funUpdate, hni, hnj]
        exact hPerScopeInv.rcBound eng loop hE i j hi hj
    · -- Inv7: PC unchanged on retire, so scopeKBound unchanged
      intro eng loop hE
      have ⟨hInv7, hInv7Back⟩ := hPerScopeInv.pcComplete eng loop hE
      exact pcComplete_retire spec ss eng0 eng loop (scopeKBound spec ss eng loop) instr Phase.committed rest hHead hInv7 hInv7Back (hIE eng hE loop)
    · -- instrAtPC_atTm1: PC unchanged on retire
      intro eng hE frame' rest' f instr' hStack' hStmt' hInstr' loop hMem
      -- PC is unchanged, so ss'.pc = ss.pc; totalEntriesOpt unchanged
      have hOld := hPerScopeInv.instrAtPC_atTm1 eng hE frame' rest' f instr' hStack' hStmt' hInstr' loop hMem
      -- Show totalEntriesOpt is unchanged
      show funUpdate ss.rc instr (ss.rc instr + 1) instr' +
        inflightCount instr' (funUpdate ss.inflight eng0 rest eng) =
        totalEntriesOpt ss eng loop - 1
      by_cases he : eng = eng0
      · subst he
        simp only [funUpdate, ite_true]
        by_cases hii : instr' = instr
        · subst hii; simp only [ite_true]
          rw [hHead] at hOld; simp [inflightCount_cons] at hOld; omega
        · simp only [if_neg hii]
          rw [hHead] at hOld; simp only [inflightCount_cons, beq_eq_false_iff_ne.mpr (Ne.symm hii), Bool.false_eq_true, ite_false, Nat.zero_add] at hOld
          exact hOld
      · have hni : instr' ≠ instr := fun h => hIE eng hE loop he (h ▸ hMem)
        simp only [funUpdate, if_neg he, if_neg hni]
        exact hOld
  | issue hE frame rest f instr hStack hStmt hInstr hDeps =>
    exact perScopeInv_spec_step_issue spec impl alloc eng0 ss frame rest f instr hStack hStmt hInstr hDeps hPerScopeInv hSpecInv hUniqueInstr hUniq hE
  | commit hE idx instr hIdx =>
    have hIFEq := inflightCount_set_phase _ _ _ _ Phase.committed hIdx
    have hIFNe : ∀ eng, eng ≠ eng0 →
        (funUpdate ss.inflight eng0 ((ss.inflight eng0).set idx (instr, Phase.committed))) eng = ss.inflight eng :=
      fun eng hne => by simp [funUpdate, hne]
    have hTEq : ∀ eng loop, totalEntriesOpt
        { controlState := ss.controlState, dataPathState := spec.instrOp instr ss.dataPathState, pc := ss.pc,
          inflight := funUpdate ss.inflight eng0 ((ss.inflight eng0).set idx (instr, Phase.committed)),
          rc := ss.rc, scopeEntryHistory := ss.scopeEntryHistory }
        eng loop = totalEntriesOpt ss eng loop := by intros; simp [totalEntriesOpt, totalEntries]
    -- For any per-engine property P, if P holds with old inflight, it holds with new
    have transfer : ∀ eng (v : Nat),
        ss.rc instr + inflightCount instr (ss.inflight eng) = v →
        ss.rc instr + inflightCount instr (funUpdate ss.inflight eng0 ((ss.inflight eng0).set idx (instr, Phase.committed)) eng) = v := by
      intro eng v h; by_cases he : eng = eng0 <;> simp_all [funUpdate]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro eng loop hE; unfold CountBalance; intro i hi
      have h := hPerScopeInv.countBalance eng loop hE i hi; simp only [hTEq]
      by_cases he : eng = eng0 <;> simp_all [funUpdate]
    · intro eng loop hE; unfold IssueOrder; simp only [hTEq]; intro i j hi hj hlt hsum
      have h := hPerScopeInv.issueOrder eng loop hE; unfold IssueOrder at h
      have hsum' : ss.rc j + inflightCount j (ss.inflight eng) = totalEntriesOpt ss eng loop := by
        by_cases he : eng = eng0
        · subst he; simp only [funUpdate, ite_true] at hsum; rw [hIFEq] at hsum; exact hsum
        · rw [hIFNe eng he] at hsum; exact hsum
      have goal := h i j hi hj hlt hsum'
      by_cases he : eng = eng0
      · subst he; simp only [funUpdate, ite_true]; rw [hIFEq]; exact goal
      · rw [hIFNe eng he]; exact goal
    · intro eng loop hE; by_cases he : eng = eng0
      · subst he; unfold QueueOrdered; simp only [funUpdate, ite_true]
        have hET := entryTag_set_phase (retireFn := ss.rc) _ _ _ Phase.issued Phase.committed hIdx
        have hGetP := getElem_set_phase_fst _ _ _ Phase.issued Phase.committed hIdx
        intro p q ip iq pp pq hpq hp hq hip hiq
        obtain ⟨pp', hp'⟩ := hGetP p ip pp hp; obtain ⟨pq', hq'⟩ := hGetP q iq pq hq
        simp only [hET]; exact hPerScopeInv.queueOrdered eng loop hE p q ip iq pp' pq' hpq hp' hq' hip hiq
      · unfold QueueOrdered; simp only [hIFNe eng he]; exact hPerScopeInv.queueOrdered eng loop hE
    · intro eng loop hE; exact hPerScopeInv.rcMono eng loop hE
    · intro eng loop hE; exact hPerScopeInv.rcBound eng loop hE
    · intro eng loop hE
      have ⟨hFwd, hBack⟩ := hPerScopeInv.pcComplete eng loop hE
      constructor <;> intro i hi hbd <;> simp only at hbd ⊢ <;> rw [hTEq]
      · have := hFwd i hi hbd; by_cases he : eng = eng0 <;> simp_all [funUpdate]
      · have := hBack i hi hbd; by_cases he : eng = eng0 <;> simp_all [funUpdate]
    · intro eng hE frame' rest' f instr' hStack' hStmt' hInstr' loop hMem
      show ss.rc instr' + inflightCount instr' (funUpdate ss.inflight eng0 ((ss.inflight eng0).set idx (instr, Phase.committed)) eng) = totalEntriesOpt ss eng loop - 1
      have hOld := hPerScopeInv.instrAtPC_atTm1 eng hE frame' rest' f instr' hStack' hStmt' hInstr' loop hMem
      by_cases he : eng = eng0 <;> simp_all [funUpdate]
  | loopEnter hE frame rest lid loopBody hStack hStmt hGuard =>
    have hAllAtT_loop : ∀ eng loop, loop = some lid → eng = eng0 →
        ∀ i, i ∈ scopeInstrs spec.engines eng spec.body loop →
          ss.rc i + inflightCount i (ss.inflight eng) = totalEntriesOpt ss eng loop := by
      intro eng loop hsc he; subst he; subst hsc
      have hNotOn := lid_not_on_stack_at_entry hStack hStmt (hSpecInv.wellFormedPC eng) hUniq
      have hKBeq := scopeKBound_eq_length_of_not_on_stack (spec := spec)
        (by simp [loopsOnStack] at hNotOn; exact hNotOn)
      have ⟨hFwd, _⟩ := hPerScopeInv.pcComplete eng (some lid) hE
      exact pcComplete_allAtT_of_kBound_ge_length spec ss eng (some lid) _ hFwd (by omega)
    have ⟨h2, h3, h4, h5, h6⟩ := invs2to6_loopEntry spec impl alloc eng0 ss is hPerScopeInv lid
        (enclosingLoopsFromStack (frame :: rest)) hAllAtT_loop
    refine ⟨h2, h3, h4, h5, h6, ?_, ?_⟩
    · have hNotBlock : ∀ f, frame.body[frame.stmtIdx]? ≠ some (Stmt.block f) := by intro f; rw [hStmt]; simp
      apply pcComplete_loopEntry_all (sid := lid) (loopBody := loopBody) hStack (Or.inl rfl) hNotBlock
      inv7_loop_entry_args lid
    · -- instrAtPC_atTm1
      intro eng hE' frame1 rest1 f1 instr1 hStack1 hStmt1 hInstr1 loop hMem1
      by_cases he : eng = eng0
      · subst he; simp only [funUpdate, ite_true] at hStack1 hInstr1
        obtain ⟨rfl, rfl⟩ := List.cons.inj hStack1
        -- instr1 is at PC in the new state (loopBody[0] is a block, instrIdx = 0)
        -- Need: rc instr1 + ifCount instr1 = totalEntriesOpt ss' eng loop - 1
        have hNotBlock : ∀ f, frame.body[frame.stmtIdx]? ≠ some (Stmt.block f) := by
          intro f; rw [hStmt]; simp
        by_cases hsc : loop = some lid
        · subst hsc
          have hAtT := hAllAtT_loop eng (some lid) rfl rfl instr1 hMem1
          simp only [totalEntriesOpt, totalEntries] at hAtT ⊢
          simp only [incrScopeEntryHistory_totalEntries]
          omega
        · -- loop ≠ some lid: totalEntriesOpt unchanged, use old Inv7 backward
          have ⟨_, hBack⟩ := hPerScopeInv.pcComplete eng loop hE
          have hOld := hBack instr1 hMem1 (by
            let ss' : SpecState := { ss with
              pc := funUpdate ss.pc eng { stack := ⟨loopBody, 0, .loop lid⟩ :: frame :: rest, instrIdx := 0 }
              controlState := funUpdate ss.controlState eng (spec.controlOp eng lid (ss.controlState eng))
              scopeEntryHistory := incrScopeEntryHistory ss eng lid (enclosingLoopsFromStack (frame :: rest)) }
            have hSpecInv' : SpecInv spec ss' := specInv_step spec eng ss ss' hUniq hSpecInv
              (SpecStep.loopEnter eng ss hE frame rest lid loopBody hStack hStmt hGuard)
            have hNewStack : (ss'.pc eng).stack = ⟨loopBody, 0, .loop lid⟩ :: frame :: rest := by simp [ss', funUpdate]
            have hNewInstr : (f1 eng)[(ss'.pc eng).instrIdx]? = some instr1 := by simp [ss', funUpdate]; exact hInstr1
            have hKBnew := scopeKBound_eq_idxOf_instrAtPC hSpecInv' hUniqueInstr hUniq hE' hNewStack hStmt1 hNewInstr hMem1
            have hKBeq := scopeKBound_loopEntry_other (spec := spec) (loopBody := loopBody) hStack (Or.inl rfl) hsc hNotBlock
            rw [← hKBeq, ← scopeKBound_eq_of_pc_eq (show ss'.pc eng = ({ ss with pc := funUpdate ss.pc eng { stack := ⟨loopBody, 0, .loop lid⟩ :: frame :: rest, instrIdx := 0 } } : SpecState).pc eng from by simp [ss', funUpdate])]
            omega)
          cases loop with
          | none => simp [totalEntriesOpt] at hOld ⊢; exact hOld
          | some sid' =>
            simp [totalEntriesOpt, totalEntries] at hOld ⊢
            have hne : sid' ≠ lid := fun h => hsc (congrArg some h)
            simp [incrScopeEntryHistory_ne_sid hne]; exact hOld
      · instrAtPC_atTm1_ne_engine
  | condTrue hE frame rest thenId elseId thenBody elseBody hStack hStmt hGuard =>
    have hAllAtT_loop : ∀ eng loop, loop = some thenId → eng = eng0 →
        ∀ i, i ∈ scopeInstrs spec.engines eng spec.body loop →
          ss.rc i + inflightCount i (ss.inflight eng) = totalEntriesOpt ss eng loop := by
      intro eng loop hsc he; subst he; subst hsc
      have hThenInBody : thenId ∈ scopeIdsOf frame.body :=
        mem_scopeIdsOf_of_getElem hStmt (by simp [scopeIdsOf])
      have hNotOn := sid_not_on_stack_at_entry hStack hThenInBody (hSpecInv.wellFormedPC eng) hUniq
      have hKBeq := scopeKBound_eq_length_of_not_on_stack (spec := spec)
        (by simp [loopsOnStack] at hNotOn; exact hNotOn)
      have ⟨hFwd, _⟩ := hPerScopeInv.pcComplete eng (some thenId) hE
      exact pcComplete_allAtT_of_kBound_ge_length spec ss eng (some thenId) _ hFwd (by omega)
    have ⟨h2, h3, h4, h5, h6⟩ := invs2to6_loopEntry spec impl alloc eng0 ss is hPerScopeInv thenId
        (enclosingLoopsFromStack (frame :: rest)) hAllAtT_loop
    refine ⟨h2, h3, h4, h5, h6, ?_, ?_⟩
    · have hNotBlock : ∀ f, frame.body[frame.stmtIdx]? ≠ some (Stmt.block f) := by intro f; rw [hStmt]; simp
      apply pcComplete_loopEntry_all (sid := thenId) (loopBody := thenBody) hStack (Or.inr rfl) hNotBlock
      inv7_loop_entry_args thenId
    · -- instrAtPC_atTm1
      intro eng hE' frame1 rest1 f1 instr1 hStack1 hStmt1 hInstr1 loop hMem1
      by_cases he : eng = eng0
      · instrAtPC_atTm1_cond_entry thenId thenBody
          (SpecStep.condTrue eng ss hE frame rest thenId elseId thenBody elseBody hStack hStmt hGuard)
      · instrAtPC_atTm1_ne_engine
  | condFalse hE frame rest thenId elseId thenBody elseBody hStack hStmt hGuard =>
    have hAllAtT_loop : ∀ eng loop, loop = some elseId → eng = eng0 →
        ∀ i, i ∈ scopeInstrs spec.engines eng spec.body loop →
          ss.rc i + inflightCount i (ss.inflight eng) = totalEntriesOpt ss eng loop := by
      intro eng loop hsc he; subst he; subst hsc
      have hElseInBody : elseId ∈ scopeIdsOf frame.body :=
        mem_scopeIdsOf_of_getElem hStmt (by simp [scopeIdsOf])
      have hNotOn := sid_not_on_stack_at_entry hStack hElseInBody (hSpecInv.wellFormedPC eng) hUniq
      have hKBeq := scopeKBound_eq_length_of_not_on_stack (spec := spec)
        (by simp [loopsOnStack] at hNotOn; exact hNotOn)
      have ⟨hFwd, _⟩ := hPerScopeInv.pcComplete eng (some elseId) hE
      exact pcComplete_allAtT_of_kBound_ge_length spec ss eng (some elseId) _ hFwd (by omega)
    have ⟨h2, h3, h4, h5, h6⟩ := invs2to6_loopEntry spec impl alloc eng0 ss is hPerScopeInv elseId
        (enclosingLoopsFromStack (frame :: rest)) hAllAtT_loop
    refine ⟨h2, h3, h4, h5, h6, ?_, ?_⟩
    · have hNotBlock : ∀ f, frame.body[frame.stmtIdx]? ≠ some (Stmt.block f) := by intro f; rw [hStmt]; simp
      apply pcComplete_loopEntry_all (sid := elseId) (loopBody := elseBody) hStack (Or.inr rfl) hNotBlock
      inv7_loop_entry_args elseId
    · -- instrAtPC_atTm1
      intro eng hE' frame1 rest1 f1 instr1 hStack1 hStmt1 hInstr1 loop hMem1
      by_cases he : eng = eng0
      · instrAtPC_atTm1_cond_entry elseId elseBody
          (SpecStep.condFalse eng ss hE frame rest thenId elseId thenBody elseBody hStack hStmt hGuard)
      · instrAtPC_atTm1_ne_engine
  | loopSkip hE frame rest lid loopBody hStack hStmt hGuard =>
    -- Only pc changes; inflight, rc, scopeEntryHistory unchanged
    -- scopeKBound_advance for eng0: instrsBefore unchanged at stmtIdx+1 for loop
    have hAdvLoop : ∀ loop', ∀ ss0 : SpecState, ss0.pc eng0 = ⟨⟨frame.body, frame.stmtIdx + 1, frame.kind⟩ :: rest, 0⟩ →
        scopeKBound spec ss0 eng0 loop' = scopeKBound spec ss eng0 loop' := by
      intro loop' ss0 hPC0
      exact scopeKBound_advance (spec := spec) hStack hPC0
        (by intro loop''
            cases hfa : findActiveFrame (frame :: rest) loop'' with
            | none => trivial
            | some fp => obtain ⟨fr, isTop⟩ := fp; cases isTop with
              | false => trivial
              | true =>
                have hfr := findActiveFrame_isTop_eq hfa; subst hfr
                simp only [hStmt]
                have := instrsBefore_succ_of_loop (engines := spec.engines) (eng := eng0) hStmt; rw [this]
                cases fr.body[fr.stmtIdx + 1]? with | none => rfl | some s => cases s <;> rfl) loop'
    refine ⟨hPerScopeInv.countBalance, hPerScopeInv.issueOrder, hPerScopeInv.queueOrdered, hPerScopeInv.rcMono, hPerScopeInv.rcBound, ?_, ?_⟩
    · intro eng loop hE; by_cases he : eng = eng0
      · subst he
        have hKBeq := hAdvLoop loop _ (show (({ ss with pc := funUpdate ss.pc eng { stack := ⟨frame.body, frame.stmtIdx + 1, frame.kind⟩ :: rest, instrIdx := 0 } } : SpecState).pc eng) = ⟨⟨frame.body, frame.stmtIdx + 1, frame.kind⟩ :: rest, 0⟩ from by simp [funUpdate])
        have ⟨hFwd, hBack⟩ := hPerScopeInv.pcComplete eng loop hE
        simp only [hKBeq]; exact ⟨fun i hi hlt => hFwd i hi hlt, fun i hi hge => hBack i hi hge⟩
      · have hPC : (funUpdate ss.pc eng0 { stack := { body := frame.body, stmtIdx := frame.stmtIdx + 1, kind := frame.kind } :: rest, instrIdx := 0 }) eng = ss.pc eng := by simp [funUpdate, he]
        simp only [scopeKBound, hPC]; exact hPerScopeInv.pcComplete eng loop hE
    · intro eng hE' frame1 rest1 f1 instr1 hStack1 hStmt1 hInstr1 loop hMem1
      by_cases he : eng = eng0
      · subst he; simp only [funUpdate, ite_true] at hStack1 hInstr1
        obtain ⟨rfl, rfl⟩ := List.cons.inj hStack1
        simp only [totalEntriesOpt, totalEntries]
        have ⟨_, hBack⟩ := hPerScopeInv.pcComplete eng loop hE
        exact hBack instr1 hMem1 (by
          let ss' : SpecState := { ss with pc := funUpdate ss.pc eng { stack := ⟨frame.body, frame.stmtIdx + 1, frame.kind⟩ :: rest, instrIdx := 0 } }
          have hSpecInv' : SpecInv spec ss' := specInv_step spec eng ss ss' hUniq hSpecInv
            (SpecStep.loopSkip eng ss hE frame rest lid loopBody hStack hStmt hGuard)
          have hNewStack : (ss'.pc eng).stack = ⟨frame.body, frame.stmtIdx + 1, frame.kind⟩ :: rest := by simp [ss', funUpdate]
          have hNewInstr : (f1 eng)[(ss'.pc eng).instrIdx]? = some instr1 := by simp [ss', funUpdate]; exact hInstr1
          have hKBnew := scopeKBound_eq_idxOf_instrAtPC hSpecInv' hUniqueInstr hUniq hE' hNewStack hStmt1 hNewInstr hMem1
          have hKBeq2 := hAdvLoop loop ss' (by simp [ss', funUpdate])
          omega)
      · simp only [funUpdate, if_neg he] at hStack1 hInstr1
        exact hPerScopeInv.instrAtPC_atTm1 eng hE' frame1 rest1 f1 instr1 hStack1 hStmt1 hInstr1 loop hMem1
  | loopBack hE frame parent rest' lid hStack hKind hEnd =>
    refine ⟨hPerScopeInv.countBalance, hPerScopeInv.issueOrder, hPerScopeInv.queueOrdered, hPerScopeInv.rcMono, hPerScopeInv.rcBound, ?_, ?_⟩
    · intro eng loop hE; by_cases he : eng = eng0
      · subst he
        have hKBeq : scopeKBound spec { ss with pc := funUpdate ss.pc eng { stack := parent :: rest', instrIdx := 0 } } eng loop = scopeKBound spec ss eng loop := by
          simp only [scopeKBound, funUpdate, ite_true, hStack]
          cases loop with
          | none =>
            simp only [findActiveFrame]
            cases hfa : findActiveFrame (parent :: rest') none with
            | none => simp [Option.map]
            | some fp =>
              obtain ⟨fr, b⟩ := fp; simp only [Option.map]
              cases b <;> simp; split <;> rfl
          | some sid =>
            simp only [findActiveFrame, hKind]
            by_cases hsid : lid = sid
            · subst hsid; simp only [ite_true, hEnd]
              have hSMP := hSpecInv.wellFormedPC eng; rw [hStack] at hSMP
              have hNotIn := sid_not_in_rest_enclosing hSMP hUniq (Or.inr hKind)
              rw [findActiveFrame_none_of_not_in_enclosing hNotIn]
              rw [show frame.body[frame.body.length]? = (none : Option Stmt) from List.getElem?_eq_none (by omega)]
              simp only [Nat.add_zero]
              rw [instrsBefore_length_eq_scopeInstrs_none]; congr 1
              have hUSParent := smp_uniqueScopeIds hSMP hUniq parent (List.mem_cons_of_mem _ (List.Mem.head _))
              cases hSMP with
              | loop lb' si ii lid' _ _ hPStmt' hM =>
                have hlid_eq : lid = lid' := by simp at hKind; exact hKind.symm
                subst hlid_eq
                have hSIpf := @scopeInstrs_of_scopeBodyOf spec.engines eng _ _ _ hUSParent (scopeBodyOf_of_getElem hPStmt' hUSParent)
                rw [scopeInstrs_eq_scopeBodyOf hUniq,
                    smp_scopeBodyOf_agree (StackMatchesProgram.loop lb' si ii lid _ _ hPStmt' hM) hUniq parent (List.mem_cons_of_mem _ (List.Mem.head _)) lid
                      (mem_scopeIdsOf_of_getElem hPStmt' (by simp [scopeIdsOf])),
                    ← scopeInstrs_eq_scopeBodyOf hUSParent, hSIpf]
              | cond _ _ _ _ _ _ _ _ _ _ _ => simp at hKind
            · simp only [ite_false, hsid]
              cases hfa : findActiveFrame (parent :: rest') (some sid) with
              | none => simp [Option.map]
              | some fp =>
                obtain ⟨fr, b⟩ := fp; simp only [Option.map]
                cases b <;> simp; split <;> rfl
        exact pcComplete_of_same_kBound hKBeq rfl rfl (by simp [totalEntriesOpt, totalEntries]) (hPerScopeInv.pcComplete eng loop hE).1 (hPerScopeInv.pcComplete eng loop hE).2
      · exact pcComplete_of_same_kBound (scopeKBound_funUpdate_ne he) rfl rfl
          (by simp [totalEntriesOpt, totalEntries]) (hPerScopeInv.pcComplete eng loop hE).1 (hPerScopeInv.pcComplete eng loop hE).2
    · intro eng hE' frame1 rest1 f1 instr1 hStack1 hStmt1 hInstr1 loop hMem1
      by_cases he : eng = eng0
      · subst he; simp only [funUpdate, ite_true] at hStack1 hInstr1
        obtain ⟨rfl, rfl⟩ := List.cons.inj hStack1
        have hSMP := hSpecInv.wellFormedPC eng; rw [hStack] at hSMP
        cases hSMP with
        | loop loopBody si ii lid' pf rest hParStmt hM =>
          rw [hParStmt] at hStmt1; simp at hStmt1
        | cond tb eb si ii thenId elseId pf rest taken hParStmt hM => simp at hKind
      · simp only [funUpdate, if_neg he] at hStack1 hInstr1
        exact hPerScopeInv.instrAtPC_atTm1 eng hE' frame1 rest1 f1 instr1 hStack1 hStmt1 hInstr1 loop hMem1
  | blockDone hE frame rest' f hStack hStmt hDone =>
    -- scopeKBound_advance for eng0: instrsBefore unchanged at stmtIdx+1 for blockDone
    have hAdvBlock : ∀ loop', ∀ ss0 : SpecState, ss0.pc eng0 = ⟨⟨frame.body, frame.stmtIdx + 1, frame.kind⟩ :: rest', 0⟩ →
        scopeKBound spec ss0 eng0 loop' = scopeKBound spec ss eng0 loop' := by
      intro loop' ss0 hPC0
      exact scopeKBound_advance (spec := spec) hStack hPC0
        (by intro loop''
            cases hfa : findActiveFrame (frame :: rest') loop'' with
            | none => trivial
            | some fp => obtain ⟨fr, isTop⟩ := fp; cases isTop with
              | false => trivial
              | true =>
                have hfr := findActiveFrame_isTop_eq hfa; subst hfr
                simp only [hStmt]
                rw [instrsBefore_succ_of_block hStmt, hDone]
                cases fr.body[fr.stmtIdx + 1]? with | none => rfl | some s => cases s <;> rfl) loop'
    refine ⟨hPerScopeInv.countBalance, hPerScopeInv.issueOrder, hPerScopeInv.queueOrdered, hPerScopeInv.rcMono, hPerScopeInv.rcBound, ?_, ?_⟩
    · intro eng loop hE; by_cases he : eng = eng0
      · subst he
        have hKBeq := hAdvBlock loop _ (show (({ ss with pc := funUpdate ss.pc eng { stack := ⟨frame.body, frame.stmtIdx + 1, frame.kind⟩ :: rest', instrIdx := 0 } } : SpecState).pc eng) = ⟨⟨frame.body, frame.stmtIdx + 1, frame.kind⟩ :: rest', 0⟩ from by simp [funUpdate])
        have ⟨hFwd, hBack⟩ := hPerScopeInv.pcComplete eng loop hE
        simp only [hKBeq]; exact ⟨fun i hi hlt => hFwd i hi hlt, fun i hi hge => hBack i hi hge⟩
      · exact pcComplete_of_same_kBound (scopeKBound_funUpdate_ne he) rfl rfl
          (by simp [totalEntriesOpt, totalEntries]) (hPerScopeInv.pcComplete eng loop hE).1 (hPerScopeInv.pcComplete eng loop hE).2
    · intro eng hE' frame1 rest1 f1 instr1 hStack1 hStmt1 hInstr1 loop hMem1
      by_cases he : eng = eng0
      · subst he; simp only [funUpdate, ite_true] at hStack1 hInstr1
        obtain ⟨rfl, rfl⟩ := List.cons.inj hStack1
        simp only [totalEntriesOpt, totalEntries]
        have ⟨_, hBack⟩ := hPerScopeInv.pcComplete eng loop hE
        exact hBack instr1 hMem1 (by
          let ss' : SpecState := { ss with pc := funUpdate ss.pc eng { stack := ⟨frame.body, frame.stmtIdx + 1, frame.kind⟩ :: rest', instrIdx := 0 } }
          have hSpecInv' : SpecInv spec ss' := specInv_step spec eng ss ss' hUniq hSpecInv
            (SpecStep.blockDone eng ss hE frame rest' f hStack hStmt hDone)
          have hNewStack : (ss'.pc eng).stack = ⟨frame.body, frame.stmtIdx + 1, frame.kind⟩ :: rest' := by simp [ss', funUpdate]
          have hNewInstr : (f1 eng)[(ss'.pc eng).instrIdx]? = some instr1 := by simp [ss', funUpdate]; exact hInstr1
          have hKBnew := scopeKBound_eq_idxOf_instrAtPC hSpecInv' hUniqueInstr hUniq hE' hNewStack hStmt1 hNewInstr hMem1
          have hKBeq2 := hAdvBlock loop ss' (by simp [ss', funUpdate])
          omega)
      · simp only [funUpdate, if_neg he] at hStack1 hInstr1
        exact hPerScopeInv.instrAtPC_atTm1 eng hE' frame1 rest1 f1 instr1 hStack1 hStmt1 hInstr1 loop hMem1
  | condDone hE frame parent rest' sid hStack hKind hEnd =>
    -- Extract common facts used by both pcComplete and instrAtPC_atTm1
    have hSMP0 := hSpecInv.wellFormedPC eng0; rw [hStack] at hSMP0
    have hParStmt0 : ∃ thenId elseId tb eb, parent.body[parent.stmtIdx]? = some (Stmt.cond thenId elseId tb eb) := by
      cases hSMP0 with
      | cond tb eb si ii thenId elseId pf rest taken hPStmt hM =>
        exact ⟨thenId, elseId, tb, eb, hPStmt⟩
      | loop lb si ii lid' pf rest hPStmt hM => simp at hKind
    obtain ⟨thenId0, elseId0, tb0, eb0, hPStmt0⟩ := hParStmt0
    have hIBCond0 : instrsBefore spec.engines eng0 parent.body (parent.stmtIdx + 1) = instrsBefore spec.engines eng0 parent.body parent.stmtIdx :=
      instrsBefore_succ_of_cond hPStmt0
    -- scopeKBound equality for eng0: used by both pcComplete and instrAtPC_atTm1
    have hKBeq0 : ∀ loop, scopeKBound spec { ss with pc := funUpdate ss.pc eng0 { stack := ⟨parent.body, parent.stmtIdx + 1, parent.kind⟩ :: rest', instrIdx := 0 } } eng0 loop = scopeKBound spec ss eng0 loop := by
      intro loop
      simp only [scopeKBound, funUpdate, ite_true, hStack]
      rw [findActiveFrame_change_stmtIdx]
      cases loop with
      | none =>
        simp only [findActiveFrame]
        cases hfa : findActiveFrame (parent :: rest') none with
        | none => simp [Option.map]
        | some fp =>
          obtain ⟨fr, b⟩ := fp; simp only [Option.map]
          cases b with
          | false => simp
          | true =>
            have hfr := findActiveFrame_isTop_eq hfa; subst hfr
            simp only [ite_true, hIBCond0, hPStmt0]
            split <;> simp
      | some sid' =>
        simp only [findActiveFrame, hKind]
        by_cases hsid : sid = sid'
        · subst hsid; simp only [ite_true, hEnd]
          have hNotIn := sid_not_in_rest_enclosing hSMP0 hUniq (Or.inl hKind)
          rw [findActiveFrame_none_of_not_in_enclosing hNotIn]; simp only [Option.map]
          rw [show frame.body[frame.body.length]? = (none : Option Stmt) from List.getElem?_eq_none (by omega)]
          simp only [Nat.add_zero]
          rw [instrsBefore_length_eq_scopeInstrs_none]; congr 1
          have hUSParent := smp_uniqueScopeIds hSMP0 hUniq parent (List.mem_cons_of_mem _ (List.Mem.head _))
          cases hSMP0 with
          | cond tb' eb' si ii thenId' elseId' _ _ taken hPStmt' hM =>
            cases taken with
            | false =>
              simp at hKind ⊢
              have hsid_eq : sid = elseId' := hKind.symm
              subst hsid_eq
              have hSIpf := @scopeInstrs_of_scopeBodyOf spec.engines eng0 _ _ _ hUSParent (scopeBodyOf_of_getElem_condFalse hPStmt' hUSParent)
              rw [scopeInstrs_eq_scopeBodyOf hUniq,
                  smp_scopeBodyOf_agree (StackMatchesProgram.cond tb' eb' si ii thenId' sid _ _ false hPStmt' hM) hUniq parent (List.mem_cons_of_mem _ (List.Mem.head _)) sid
                    (mem_scopeIdsOf_of_getElem hPStmt' (by simp [scopeIdsOf])),
                  ← scopeInstrs_eq_scopeBodyOf hUSParent, hSIpf]
            | true =>
              simp at hKind ⊢
              have hsid_eq : sid = thenId' := hKind.symm
              subst hsid_eq
              have hSIpf := @scopeInstrs_of_scopeBodyOf spec.engines eng0 _ _ _ hUSParent (scopeBodyOf_of_getElem_condTrue hPStmt' hUSParent)
              rw [scopeInstrs_eq_scopeBodyOf hUniq,
                  smp_scopeBodyOf_agree (StackMatchesProgram.cond tb' eb' si ii sid elseId' _ _ true hPStmt' hM) hUniq parent (List.mem_cons_of_mem _ (List.Mem.head _)) sid
                    (mem_scopeIdsOf_of_getElem hPStmt' (by simp [scopeIdsOf])),
                  ← scopeInstrs_eq_scopeBodyOf hUSParent, hSIpf]
          | loop _ _ _ _ _ _ _ _ => simp at hKind
        · simp only [ite_false, hsid]
          cases hfa : findActiveFrame (parent :: rest') (some sid') with
          | none => simp [Option.map]
          | some fp =>
            obtain ⟨fr, b⟩ := fp; simp only [Option.map]
            cases b with
            | false => simp
            | true =>
              have hfr := findActiveFrame_isTop_eq hfa; subst hfr
              simp only [ite_true, hIBCond0, hPStmt0]
              split <;> simp
    refine ⟨hPerScopeInv.countBalance, hPerScopeInv.issueOrder, hPerScopeInv.queueOrdered, hPerScopeInv.rcMono, hPerScopeInv.rcBound, ?_, ?_⟩
    · intro eng loop hE; by_cases he : eng = eng0
      · subst he
        exact pcComplete_of_same_kBound (hKBeq0 loop) rfl rfl (by simp [totalEntriesOpt, totalEntries]) (hPerScopeInv.pcComplete eng loop hE).1 (hPerScopeInv.pcComplete eng loop hE).2
      · exact pcComplete_of_same_kBound (scopeKBound_funUpdate_ne he) rfl rfl
          (by simp [totalEntriesOpt, totalEntries]) (hPerScopeInv.pcComplete eng loop hE).1 (hPerScopeInv.pcComplete eng loop hE).2
    · intro eng hE' frame1 rest1 f1 instr1 hStack1 hStmt1 hInstr1 loop hMem1
      by_cases he : eng = eng0
      · subst he; simp only [funUpdate, ite_true] at hStack1 hInstr1
        obtain ⟨rfl, rfl⟩ := List.cons.inj hStack1
        simp only [totalEntriesOpt, totalEntries]
        have ⟨_, hBack⟩ := hPerScopeInv.pcComplete eng loop hE
        exact hBack instr1 hMem1 (by
          let ss' : SpecState := { ss with pc := funUpdate ss.pc eng { stack := ⟨parent.body, parent.stmtIdx + 1, parent.kind⟩ :: rest', instrIdx := 0 } }
          have hSpecInv' : SpecInv spec ss' := specInv_step spec eng ss ss' hUniq hSpecInv
            (SpecStep.condDone eng ss hE frame parent rest' sid hStack hKind hEnd)
          have hNewStack : (ss'.pc eng).stack = ⟨parent.body, parent.stmtIdx + 1, parent.kind⟩ :: rest' := by simp [ss', funUpdate]
          have hNewInstr : (f1 eng)[(ss'.pc eng).instrIdx]? = some instr1 := by simp [ss', funUpdate]; exact hInstr1
          have hKBnew := scopeKBound_eq_idxOf_instrAtPC hSpecInv' hUniqueInstr hUniq hE' hNewStack hStmt1 hNewInstr hMem1
          have hKBeq' : scopeKBound spec ss' eng loop = scopeKBound spec ss eng loop :=
            show scopeKBound spec { ss with pc := funUpdate ss.pc eng { stack := ⟨parent.body, parent.stmtIdx + 1, parent.kind⟩ :: rest', instrIdx := 0 } } eng loop = _ from hKBeq0 loop
          omega)
      · simp only [funUpdate, if_neg he] at hStack1 hInstr1
        exact hPerScopeInv.instrAtPC_atTm1 eng hE' frame1 rest1 f1 instr1 hStack1 hStmt1 hInstr1 loop hMem1
