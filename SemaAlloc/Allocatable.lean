import SemaAlloc.SpecInv

-- Runtime well-formedness: cumExecs equals a closed-form expression at issue time.
def AllocatableAt (spec : Program) (ss : SpecState) (e : EngineId) (instr : DataPathInstrId) : Prop :=
  match spec.depGraph instr with
  | .none => True
  | .dep producer offset =>
    let sharedLoop := innermostSharedScope spec.engines spec.body producer instr
    let producerLoop := innermostParentScope spec.engines spec.body producer
    match producerLoop with
    | none => True
    | some plid =>
      if sharedLoop = producerLoop then
        cumExecs ss e plid sharedLoop (totalEntriesOpt ss e sharedLoop - offset) =
          totalEntries ss e plid - offset
      else
        cumExecs ss e plid sharedLoop (totalEntriesOpt ss e sharedLoop - offset) =
          totalEntries ss e plid

-- Static well-formedness of the dependency graph (assumed by top-level theorems).
def Allocatable (spec : Program) : Prop :=
  ∀ instr, match spec.depGraph instr with
  | .none => True
  | .dep producer offset =>
    instrInBody spec.engines spec.body producer = true ∧
    (let producerLoop := innermostParentScope spec.engines spec.body producer
    match producerLoop with
    | none => True
    | some plid =>
      let sharedLoop := innermostSharedScope spec.engines spec.body producer instr
      sharedLoop = some plid -- Producer in S, forward or backward.
      ∨ (forwardDep spec.engines spec.body producer instr
          ∧ offset = 0) -- producerFirst, offset 0
      ∨ (backwardDep spec.engines spec.body producer instr
          ∧ offset = 1)) -- backwardDep, offset 1

-- The key theorem.
theorem allocatable_implies_allocatableAt (spec : Program) (ss : SpecState) (e : EngineId) (instr : DataPathInstrId)
    (hWf : Allocatable spec) (hSpecInv : SpecInv spec ss)
    (hPlidInSl : ∀ p c plid sl, innermostParentScope spec.engines spec.body p = some plid →
      innermostSharedScope spec.engines spec.body p c = some sl → sl ≠ plid →
      plid ∈ scopeIdsOf ((scopeBodyOf spec.body sl).getD []))
    (_hPlidInBody : ∀ p plid, innermostParentScope spec.engines spec.body p = some plid →
      plid ∈ scopeIdsOf spec.body)
    (hZeroBefore : ∀ p plid sl, backwardDep spec.engines spec.body p instr →
      innermostParentScope spec.engines spec.body p = some plid →
      innermostSharedScope spec.engines spec.body p instr = some sl → sl ≠ plid →
      ss.scopeEntryHistory e plid (some sl) (totalEntries ss e sl) = 0)
    (hZeroBeforeTop : ∀ p plid, backwardDep spec.engines spec.body p instr →
      innermostParentScope spec.engines spec.body p = some plid →
      innermostSharedScope spec.engines spec.body p instr = none →
      totalEntries ss e plid = 0)
    : AllocatableAt spec ss e instr := by
  unfold Allocatable at hWf; have hI := hWf instr
  simp only [AllocatableAt]
  match hDep : spec.depGraph instr with
  | .none => simp
  | .dep producer offset =>
    simp [hDep] at hI ⊢
    obtain ⟨_, hI⟩ := hI
    match hPL : innermostParentScope spec.engines spec.body producer with
    | none => simp
    | some plid =>
      simp [hPL] at hI ⊢
      match hSL : innermostSharedScope spec.engines spec.body producer instr with
      | some sl =>
        simp
        by_cases hEq : some sl = some plid
        · -- producerIsParent
          rw [show sl = plid from by simp at hEq; exact hEq]; simp
          exact cumExecs_of_all_ones (hSpecInv.selfHistory e plid) (Nat.sub_le _ _)
        · -- child/sibling
          have hNe : sl ≠ plid := by simp at hEq; exact hEq
          simp [hNe]
          have hPlidMem := hPlidInSl producer instr plid sl hPL hSL hNe
          rcases hI with hPI | ⟨_, hOff0⟩ | ⟨hCF, hOff1⟩
          · simp [hSL] at hPI; contradiction
          · -- offset = 0
            rw [hOff0]; simp
            exact hSpecInv.cumulative e plid sl hPlidMem
          · -- backwardDep, offset = 1
            rw [hOff1]
            have hCum := hSpecInv.cumulative e plid sl hPlidMem
            have hZero : ss.scopeEntryHistory e plid (some sl) (totalEntries ss e sl) = 0 :=
              hZeroBefore producer plid sl hCF hPL hSL hNe
            rcases Nat.eq_zero_or_pos (totalEntries ss e sl) with h0 | hpos
            · simp only [h0, totalEntriesOpt, Nat.zero_sub, cumExecs, List.range_zero, List.foldl_nil]
              simp only [h0, cumExecs, List.range_zero, List.foldl_nil] at hCum
              exact hCum
            · simp only [totalEntriesOpt] at *
              have hSucc := cumExecs_succ ss e plid (some sl) (totalEntries ss e sl - 1)
              have hTE : totalEntries ss e sl - 1 + 1 = totalEntries ss e sl := by omega
              rw [hTE] at hSucc; omega
      | none =>
        simp [totalEntriesOpt]
        rcases hI with hPI | ⟨_, hOff0⟩ | ⟨hCF, hOff1⟩
        · simp [hSL] at hPI
        · rw [hOff0]; simp [cumExecs, totalEntries]
        · rw [hOff1]; simp
          exact (hZeroBeforeTop producer plid hCF hPL hSL).symm

theorem discharge_zeroBefore {spec : Program} {ss : SpecState} {e : EngineId}
    {p c : DataPathInstrId} {plid sl : ScopeId} {si : Nat}
    (hSpecInv : SpecInv spec ss)
    (hCF : backwardDep spec.engines spec.body p c)
    (hPL : innermostParentScope spec.engines spec.body p = some plid)
    (hSL : innermostSharedScope spec.engines spec.body p c = some sl)
    (hNe : sl ≠ plid)
    (hUI : UniqueInstrIds spec.engines spec.body)
    (hUL : UniqueScopeIds spec.body)
    (hOnStack : sl ∈ loopsOnStack ss e)
    (hSi : stmtIdxInLoop (ss.pc e).stack sl = some si)
    (hConsumerAt : ∃ s, ((scopeBodyOf spec.body sl).getD [])[si]? = some s ∧
      instrInBody spec.engines [s] c = true)
    : ss.scopeEntryHistory e plid (some sl) (totalEntries ss e sl) = 0 := by
  unfold backwardDep at hCF; simp [hSL] at hCF
  obtain ⟨ci, pi, hLt, ⟨cs, hcs, hcIn⟩, ⟨ps, hps, hpIn⟩⟩ := hCF
  have hLB : scopeBodyOf spec.body sl = some ((scopeBodyOf spec.body sl).getD []) := by
    cases h : scopeBodyOf spec.body sl with | some lb => simp | none => simp [h] at hps
  have hUISB := uniqueInstrIds_of_scopeBodyOf hUI hLB
  obtain ⟨cs', hcs', hcIn'⟩ := hConsumerAt
  have hEq : si = ci := uniqueInstrIds_unique_index hUISB hcs' hcs hcIn' hcIn
  have hSiLtPi : si < pi := hEq ▸ hLt
  have hPLSB := innermostParentScope_of_scopeBodyOf hUI hUL hPL hLB hNe
    (instrInBody_of_getElem_rest hps hpIn)
  have hPlidInPs := innermostParentScope_at_stmt hUISB hPLSB hps hpIn
  exact hSpecInv.zeroBeforeEntry e plid sl si pi ps hOnStack hSi hps hPlidInPs hSiLtPi

theorem discharge_zeroBeforeTop {spec : Program} {ss : SpecState} {e : EngineId}
    {p c : DataPathInstrId} {plid : ScopeId} {si : Nat}
    (hSpecInv : SpecInv spec ss)
    (hCF : backwardDep spec.engines spec.body p c)
    (hPL : innermostParentScope spec.engines spec.body p = some plid)
    (hSL : innermostSharedScope spec.engines spec.body p c = none)
    (hUI : UniqueInstrIds spec.engines spec.body)
    (_ : UniqueScopeIds spec.body)
    (hSi : stmtIdxAtTop (ss.pc e).stack = some si)
    (hConsumerAt : ∃ s, spec.body[si]? = some s ∧ instrInBody spec.engines [s] c = true)
    : totalEntries ss e plid = 0 := by
  unfold backwardDep at hCF; simp [hSL] at hCF
  obtain ⟨ci, pi, hLt, ⟨cs, hcs, hcIn⟩, ⟨ps, hps, hpIn⟩⟩ := hCF
  obtain ⟨cs', hcs', hcIn'⟩ := hConsumerAt
  have hEq : si = ci := uniqueInstrIds_unique_index hUI hcs' hcs hcIn' hcIn
  have hSiLtPi : si < pi := hEq ▸ hLt
  have hPlidInPs := innermostParentScope_at_stmt hUI hPL hps hpIn
  exact hSpecInv.zeroBeforeEntryTop e plid si pi ps hSi hps hPlidInPs hSiLtPi

theorem findInBlock_isSome_of_mem {engines : List EngineId} {f : EngineId → List DataPathInstrId}
    {e : EngineId} {instr : DataPathInstrId}
    (hE : e ∈ engines) (hIn : instr ∈ f e) : (findInBlock engines f instr).isSome = true := by
  induction engines with
  | nil => simp at hE
  | cons e' rest ih =>
    simp [findInBlock]
    aesop

theorem instrInBody_block_of_mem {engines : List EngineId} {f : EngineId → List DataPathInstrId}
    {e : EngineId} {instr : DataPathInstrId}
    (hE : e ∈ engines) (hIn : instr ∈ f e)
    : instrInBody engines [Stmt.block f] instr = true := by
  simp [instrInBody]; exact findInBlock_isSome_of_mem hE hIn

theorem smp_instr_in_loop_stmt {progBody : List Stmt}
    {stack : List Frame}
    (hSMP : StackMatchesProgram progBody stack) (hUniq : UniqueScopeIds progBody)
    {frame : Frame} {rest : List Frame} (hEq : stack = frame :: rest)
    {engines : List EngineId} {instr : DataPathInstrId}
    (hInFrame : instrInBody engines frame.body instr = true)
    {loop : ScopeId} {si : Nat} (hSi : stmtIdxInLoop rest loop = some si)
    : ∃ s, ((scopeBodyOf progBody loop).getD [])[si]? = some s ∧ instrInBody engines [s] instr = true := by
  induction hSMP generalizing frame rest loop si with
  | base si' ii =>
    have ⟨_, rfl⟩ := List.cons.inj hEq; simp [stmtIdxInLoop] at hSi
  | loop lb si' ii lid' parentFrame rest' hStmt' hMatch ih =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hEq
    have hInParent : instrInBody engines parentFrame.body instr = true :=
      instrInBody_of_getElem_rest hStmt' (by simp [instrInBody]; exact hInFrame)
    cases hpk : parentFrame.kind with
    | top => simp [stmtIdxInLoop, hpk] at hSi; exact ih rfl hInParent hSi
    | cond sid =>
      simp [stmtIdxInLoop, hpk] at hSi
      by_cases heq : sid = loop
      · subst heq; simp at hSi; subst hSi
        have hLBOf := smp_scopeBodyOf_loop hMatch hUniq parentFrame (List.Mem.head _) (by rw [hpk]; rfl)
        simp [hLBOf]
        exact ⟨Stmt.loop lid' lb, hStmt', by simp [instrInBody]; exact hInFrame⟩
      · simp [heq] at hSi; exact ih rfl hInParent hSi
    | loop plid =>
      simp [stmtIdxInLoop, hpk] at hSi
      by_cases heq : plid = loop
      · subst heq; simp at hSi; subst hSi
        have hLBOf := smp_scopeBodyOf hMatch hUniq parentFrame (List.Mem.head _) hpk
        simp [hLBOf]
        exact ⟨Stmt.loop lid' lb, hStmt', by simp [instrInBody]; exact hInFrame⟩
      · simp [heq] at hSi; exact ih rfl hInParent hSi
  | cond tb eb si' ii tid eid parentFrame rest' taken hStmt' hMatch ih =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hEq
    have hInParent : instrInBody engines parentFrame.body instr = true :=
      instrInBody_of_getElem_rest hStmt' (by cases taken with | false => simp at hInFrame; simp [instrInBody]; right; exact hInFrame | true => simp at hInFrame; simp [instrInBody]; left; exact hInFrame)
    cases hpk : parentFrame.kind with
    | top => simp [stmtIdxInLoop, hpk] at hSi; exact ih rfl hInParent hSi
    | cond sid =>
      simp [stmtIdxInLoop, hpk] at hSi
      by_cases heq : sid = loop
      · subst heq; simp at hSi; subst hSi
        have hLBOf := smp_scopeBodyOf_loop hMatch hUniq parentFrame (List.Mem.head _) (by rw [hpk]; rfl)
        simp [hLBOf]
        exact ⟨Stmt.cond tid eid tb eb, hStmt', by cases taken with | false => simp at hInFrame; simp [instrInBody]; right; exact hInFrame | true => simp at hInFrame; simp [instrInBody]; left; exact hInFrame⟩
      · simp [heq] at hSi; exact ih rfl hInParent hSi
    | loop plid =>
      simp [stmtIdxInLoop, hpk] at hSi
      by_cases heq : plid = loop
      · subst heq; simp at hSi; subst hSi
        have hLBOf := smp_scopeBodyOf hMatch hUniq parentFrame (List.Mem.head _) hpk
        simp [hLBOf]
        exact ⟨Stmt.cond tid eid tb eb, hStmt', by cases taken with | false => simp at hInFrame; simp [instrInBody]; right; exact hInFrame | true => simp at hInFrame; simp [instrInBody]; left; exact hInFrame⟩
      · simp [heq] at hSi; exact ih rfl hInParent hSi

-- Top-level version

theorem smp_instr_in_top_stmt {progBody : List Stmt}
    {stack : List Frame}
    (hSMP : StackMatchesProgram progBody stack)
    {frame : Frame} {rest : List Frame} (hEq : stack = frame :: rest)
    {engines : List EngineId} {instr : DataPathInstrId}
    (hInFrame : instrInBody engines frame.body instr = true)
    {si : Nat} (hSi : stmtIdxAtTop rest = some si)
    : ∃ s, progBody[si]? = some s ∧ instrInBody engines [s] instr = true := by
  induction hSMP generalizing frame rest si with
  | base si' ii =>
    have ⟨_, rfl⟩ := List.cons.inj hEq; simp [stmtIdxAtTop] at hSi
  | loop lb si' ii lid' parentFrame rest' hStmt' hMatch ih =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hEq
    have hInParent : instrInBody engines parentFrame.body instr = true :=
      instrInBody_of_getElem_rest hStmt' (by simp [instrInBody]; exact hInFrame)
    cases hpk : parentFrame.kind with
    | top =>
      simp [stmtIdxAtTop, hpk] at hSi; subst hSi
      have hBodyEq : parentFrame.body = progBody := by
        cases hMatch with | base _ _ => rfl | _ => simp at *
      rw [← hBodyEq]
      exact ⟨Stmt.loop lid' lb, hStmt', by simp [instrInBody]; exact hInFrame⟩
    | cond _ => simp [stmtIdxAtTop, hpk] at hSi; exact ih rfl hInParent hSi
    | loop _ => simp [stmtIdxAtTop, hpk] at hSi; exact ih rfl hInParent hSi
  | cond tb eb si' ii tid eid parentFrame rest' taken hStmt' hMatch ih =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hEq
    have hInParent : instrInBody engines parentFrame.body instr = true :=
      instrInBody_of_getElem_rest hStmt' (by cases taken with | false => simp at hInFrame; simp [instrInBody]; right; exact hInFrame | true => simp at hInFrame; simp [instrInBody]; left; exact hInFrame)
    cases hpk : parentFrame.kind with
    | top =>
      simp [stmtIdxAtTop, hpk] at hSi; subst hSi
      have hBodyEq : parentFrame.body = progBody := by
        cases hMatch with | base _ _ => rfl | _ => simp at *
      rw [← hBodyEq]
      exact ⟨Stmt.cond tid eid tb eb, hStmt', by cases taken with | false => simp at hInFrame; simp [instrInBody]; right; exact hInFrame | true => simp at hInFrame; simp [instrInBody]; left; exact hInFrame⟩
    | cond _ => simp [stmtIdxAtTop, hpk] at hSi; exact ih rfl hInParent hSi
    | loop _ => simp [stmtIdxAtTop, hpk] at hSi; exact ih rfl hInParent hSi

theorem scopeIdsOf_exists_getElem {body : List Stmt} {lid : ScopeId}
    (h : lid ∈ scopeIdsOf body)
    : ∃ (j : Nat) (s : Stmt), body[j]? = some s ∧ lid ∈ scopeIdsOf [s] := by
  induction body with
  | nil => simp [scopeIdsOf] at h
  | cons s rest ih =>
    cases s with
    | block f =>
      simp [scopeIdsOf] at h
      obtain ⟨j, s', hj, hm⟩ := ih h; exact ⟨j + 1, s', by simp; exact hj, hm⟩
    | loop lid' body' =>
      simp [scopeIdsOf] at h; rcases h with rfl | h | h
      · exact ⟨0, _, rfl, by simp [scopeIdsOf]⟩
      · exact ⟨0, _, rfl, by simp [scopeIdsOf]; right; exact h⟩
      · obtain ⟨j, s', hj, hm⟩ := ih h; exact ⟨j + 1, s', by simp; exact hj, hm⟩
    | cond thenId elseId b1 b2 =>
      simp [scopeIdsOf] at h; rcases h with rfl | rfl | h | h | h
      · exact ⟨0, _, rfl, by simp [scopeIdsOf]⟩
      · exact ⟨0, _, rfl, by simp [scopeIdsOf]⟩
      · exact ⟨0, _, rfl, by simp_all [scopeIdsOf, List.mem_append]⟩
      · exact ⟨0, _, rfl, by simp_all [scopeIdsOf, List.mem_append]⟩
      · obtain ⟨j, s', hj, hm⟩ := ih h; exact ⟨j + 1, s', by simp; exact hj, hm⟩


theorem sl_not_in_frame_loopIds {engines : List EngineId} {progBody : List Stmt}
    {stack : List Frame}
    (hSMP : StackMatchesProgram progBody stack) (hUniq : UniqueScopeIds progBody)
    (hUI : UniqueInstrIds engines progBody)
    {frame : Frame} (hMem : frame ∈ stack)
    {f : EngineId → List DataPathInstrId} {instr : DataPathInstrId}
    (hIdx : frame.body[frame.stmtIdx]? = some (Stmt.block f))
    (hIn : instrInBody engines [Stmt.block f] instr = true)
    {sl : ScopeId}
    (hSlContains : instrInBody engines ((scopeBodyOf progBody sl).getD []) instr = true)
    : sl ∉ scopeIdsOf frame.body := by
  intro hSlIn
  obtain ⟨j, s, hJ, hSlInS⟩ := scopeIdsOf_exists_getElem hSlIn
  have hFUniq := smp_uniqueScopeIds hSMP hUniq frame hMem
  have hFUI := smp_uniqueInstrIds hSMP hUI frame hMem
  have hAgree := smp_scopeBodyOf_agree hSMP hUniq frame hMem sl hSlIn
  rw [hAgree] at hSlContains
  have hInS : instrInBody engines [s] instr = true := by
    cases s with
    | block fb => simp [scopeIdsOf] at hSlInS
    | loop lid' lb =>
      simp [scopeIdsOf] at hSlInS; simp [instrInBody]
      rcases hSlInS with rfl | hSlInS
      · have hLB := scopeBodyOf_of_getElem hJ hFUniq
        simp [hLB] at hSlContains; exact hSlContains
      · have hDesc := scopeBodyOf_descend_loop hJ hSlInS hFUniq
        rw [hDesc] at hSlContains
        cases hLB : scopeBodyOf lb sl with
        | some val => simp [hLB] at hSlContains; exact instrInBody_of_scopeBodyOf hLB hSlContains
        | none => simp [hLB] at hSlContains; simp [instrInBody] at hSlContains
    | cond tid eid b1 b2 =>
      simp only [scopeIdsOf, List.mem_cons, List.mem_append, List.mem_nil_iff, or_false] at hSlInS
      simp [instrInBody]
      rcases hSlInS with (rfl | rfl | hSlInS) | hSlInS
      · -- sl = tid (thenId of this cond)
        have hLB := scopeBodyOf_of_getElem_condTrue hJ hFUniq
        simp [hLB] at hSlContains; left; exact hSlContains
      · -- sl = eid (elseId of this cond)
        have hLB := scopeBodyOf_of_getElem_condFalse hJ hFUniq
        simp [hLB] at hSlContains; right; exact hSlContains
      · -- sl ∈ scopeIdsOf b1
        left; have hDesc := scopeBodyOf_descend_condTrue hJ hSlInS hFUniq
        rw [hDesc] at hSlContains
        cases hLB : scopeBodyOf b1 sl with
        | some val => simp [hLB] at hSlContains; exact instrInBody_of_scopeBodyOf hLB hSlContains
        | none => simp [hLB] at hSlContains; simp [instrInBody] at hSlContains
      · -- sl ∈ scopeIdsOf b2
        right; have hDesc := scopeBodyOf_descend_condFalse hJ hSlInS hFUniq
        rw [hDesc] at hSlContains
        cases hLB : scopeBodyOf b2 sl with
        | some val => simp [hLB] at hSlContains; exact instrInBody_of_scopeBodyOf hLB hSlContains
        | none => simp [hLB] at hSlContains; simp [instrInBody] at hSlContains
  have hEqIdx := uniqueInstrIds_unique_index hFUI hJ hIdx hInS hIn
  subst hEqIdx; rw [hJ] at hIdx; cases hIdx; simp [scopeIdsOf] at hSlInS

private theorem sl_not_in_parent {engines : List EngineId} {progBody : List Stmt}
    {stack : List Frame}
    (hSMP : StackMatchesProgram progBody stack) (hUniq : UniqueScopeIds progBody)
    (hUI : UniqueInstrIds engines progBody)
    {pf : Frame} (hPfMem : pf ∈ stack)
    {instr : DataPathInstrId} (_ : instrInBody engines pf.body instr = true)
    {sl : ScopeId}
    (hSlContains : instrInBody engines ((scopeBodyOf progBody sl).getD []) instr = true)
    {stmt : Stmt} (hStmt : pf.body[pf.stmtIdx]? = some stmt)
    (hInStmt : instrInBody engines [stmt] instr = true)
    (hSlNotStmt : sl ∉ scopeIdsOf [stmt])
    : sl ∉ scopeIdsOf pf.body := by
  intro hSlPf
  have hFUniq := smp_uniqueScopeIds hSMP hUniq pf hPfMem
  have hFUI := smp_uniqueInstrIds hSMP hUI pf hPfMem
  obtain ⟨j, s, hJ, hSlInS⟩ := scopeIdsOf_exists_getElem hSlPf
  have hNe : j ≠ pf.stmtIdx := by
    intro heq; subst heq; rw [hJ] at hStmt; cases hStmt; exact hSlNotStmt hSlInS
  have hAgree := smp_scopeBodyOf_agree hSMP hUniq pf hPfMem sl hSlPf
  rw [hAgree] at hSlContains
  have hInS : instrInBody engines [s] instr = true := by
    cases s with
    | block fb => simp [scopeIdsOf] at hSlInS
    | loop lid' lb' =>
      simp [scopeIdsOf] at hSlInS; simp [instrInBody]
      rcases hSlInS with rfl | hSlInS
      · simp [scopeBodyOf_of_getElem hJ hFUniq] at hSlContains; exact hSlContains
      · have hDesc := scopeBodyOf_descend_loop hJ hSlInS hFUniq; rw [hDesc] at hSlContains
        cases hLB : scopeBodyOf lb' sl with
        | some val => simp [hLB] at hSlContains; exact instrInBody_of_scopeBodyOf hLB hSlContains
        | none => simp [hLB] at hSlContains; simp [instrInBody] at hSlContains
    | cond tid eid b1 b2 =>
      simp only [scopeIdsOf, List.mem_cons, List.mem_append, List.mem_nil_iff, or_false] at hSlInS
      simp [instrInBody]
      rcases hSlInS with (rfl | rfl | hSlInS) | hSlInS
      · -- sl = tid
        have hLB := scopeBodyOf_of_getElem_condTrue hJ hFUniq
        simp [hLB] at hSlContains; left; exact hSlContains
      · -- sl = eid
        have hLB := scopeBodyOf_of_getElem_condFalse hJ hFUniq
        simp [hLB] at hSlContains; right; exact hSlContains
      · -- sl ∈ scopeIdsOf b1
        left; have hDesc := scopeBodyOf_descend_condTrue hJ hSlInS hFUniq; rw [hDesc] at hSlContains
        cases hLB : scopeBodyOf b1 sl with
        | some val => simp [hLB] at hSlContains; exact instrInBody_of_scopeBodyOf hLB hSlContains
        | none => simp [hLB] at hSlContains; simp [instrInBody] at hSlContains
      · -- sl ∈ scopeIdsOf b2
        right; have hDesc := scopeBodyOf_descend_condFalse hJ hSlInS hFUniq; rw [hDesc] at hSlContains
        cases hLB : scopeBodyOf b2 sl with
        | some val => simp [hLB] at hSlContains; exact instrInBody_of_scopeBodyOf hLB hSlContains
        | none => simp [hLB] at hSlContains; simp [instrInBody] at hSlContains
  exact hNe (uniqueInstrIds_unique_index hFUI hJ hStmt hInS hInStmt)

private theorem uniqueInstrIds_cond_instrDisjoint {engines : List EngineId} {body : List Stmt}
    {idx : Nat} {thenId elseId : ScopeId} {tb eb : List Stmt}
    (hUI : UniqueInstrIds engines body) (hIdx : body[idx]? = some (Stmt.cond thenId elseId tb eb))
    {instr : DataPathInstrId} (hInTb : instrInBody engines tb instr = true)
    : instrInBody engines eb instr = false := by
  induction hUI generalizing idx with
  | nil => simp at hIdx
  | block _ _ _ _ ih => cases idx <;> aesop
  | loop _ _ _ _ _ _ _ ih_rest => cases idx <;> aesop
  | cond _ _ _ _ _ hD12 _ _ _ _ _ ih_rest => cases idx <;> aesop

-- uniqueInstrIds_cond_instrDisjoint' moved to ASTLemmas.lean


theorem sl_on_stack {progBody : List Stmt}
    {stack : List Frame}
    (hSMP : StackMatchesProgram progBody stack) (hUniq : UniqueScopeIds progBody)
    (hUI : UniqueInstrIds (engines : List EngineId) progBody)
    {frame : Frame} {rest : List Frame} (hEq : stack = frame :: rest)
    {instr : DataPathInstrId} (hInFrame : instrInBody engines frame.body instr = true)
    {sl : ScopeId}
    (hSlContains : instrInBody engines ((scopeBodyOf progBody sl).getD []) instr = true)
    (hSlNotFrame : sl ∉ scopeIdsOf frame.body)
    : sl ∈ enclosingLoopsFromStack stack := by
  induction hSMP generalizing frame rest with
  | base si ii =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hEq
    cases hLB : scopeBodyOf progBody sl with
    | some val => exact absurd (scopeBodyOf_mem_scopeIdsOf hLB) hSlNotFrame
    | none => simp [hLB] at hSlContains; simp [instrInBody] at hSlContains
  | loop lb si' ii lid pf rest' hStmt hMatch ih =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hEq
    simp [enclosingLoopsFromStack]
    by_cases hEqLid : lid = sl
    · left; exact hEqLid.symm
    · right
      have hInPf : instrInBody engines pf.body instr = true :=
        instrInBody_of_getElem_rest hStmt (by simp [instrInBody]; exact hInFrame)
      have hSlNotPf : sl ∉ scopeIdsOf pf.body :=
        sl_not_in_parent hMatch hUniq hUI (List.Mem.head _) hInPf hSlContains hStmt
          (by simp [instrInBody]; exact hInFrame)
          (by simp [scopeIdsOf]; exact ⟨Ne.symm hEqLid, hSlNotFrame⟩)
      exact ih rfl hInPf hSlNotPf
  | cond tb eb si' ii tid eid pf rest' taken hStmt hMatch ih =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hEq
    cases taken with
    | true =>
      simp at hInFrame hSlNotFrame ⊢; simp [enclosingLoopsFromStack]
      by_cases hEqTid : tid = sl
      · left; exact hEqTid.symm
      · right
        have hInPf : instrInBody engines pf.body instr = true :=
          instrInBody_of_getElem_rest hStmt (by simp [instrInBody]; left; exact hInFrame)
        have hFUI := smp_uniqueInstrIds hMatch hUI pf (List.Mem.head _)
        have hFUniq := smp_uniqueScopeIds hMatch hUniq pf (List.Mem.head _)
        have hSlNotStmt : sl ∉ scopeIdsOf [Stmt.cond tid eid tb eb] := by
          simp only [scopeIdsOf, List.mem_cons, List.mem_append, List.mem_nil_iff, or_false]
          intro h; rcases h with (rfl | rfl | h) | h
          · exact hEqTid rfl
          · have hLB := scopeBodyOf_of_getElem_condFalse hStmt hFUniq
            have hSlPf : sl ∈ scopeIdsOf pf.body :=
              mem_scopeIdsOf_of_getElem hStmt (by simp [scopeIdsOf])
            have hAgree := smp_scopeBodyOf_agree hMatch hUniq pf (List.Mem.head _) sl hSlPf
            rw [hAgree, hLB] at hSlContains
            exact absurd (uniqueInstrIds_cond_instrDisjoint hFUI hStmt hInFrame) (by simp; exact hSlContains)
          · exact hSlNotFrame h
          · have hSlPf : sl ∈ scopeIdsOf pf.body :=
              mem_scopeIdsOf_of_getElem hStmt (show sl ∈ scopeIdsOf [Stmt.cond tid eid tb eb] from by
                unfold scopeIdsOf; apply List.mem_append_left; apply List.mem_cons_of_mem; apply List.mem_cons_of_mem; apply List.mem_append_right; exact h)
            have hAgree := smp_scopeBodyOf_agree hMatch hUniq pf (List.Mem.head _) sl hSlPf
            rw [hAgree] at hSlContains
            have hDesc := scopeBodyOf_descend_condFalse hStmt h hFUniq
            rw [hDesc] at hSlContains
            cases hLB : scopeBodyOf eb sl with
            | none => simp [hLB] at hSlContains; simp [instrInBody] at hSlContains
            | some val =>
              simp [hLB] at hSlContains
              exact absurd (uniqueInstrIds_cond_instrDisjoint hFUI hStmt hInFrame)
                (by simp; exact instrInBody_of_scopeBodyOf hLB hSlContains)
        have hSlNotPf : sl ∉ scopeIdsOf pf.body :=
          sl_not_in_parent hMatch hUniq hUI (List.Mem.head _) hInPf hSlContains hStmt
            (by simp [instrInBody]; left; exact hInFrame) hSlNotStmt
        exact ih rfl hInPf hSlNotPf
    | false =>
      simp at hInFrame hSlNotFrame ⊢; simp [enclosingLoopsFromStack]
      by_cases hEqEid : eid = sl
      · left; exact hEqEid.symm
      · right
        have hInPf : instrInBody engines pf.body instr = true :=
          instrInBody_of_getElem_rest hStmt (by simp [instrInBody]; right; exact hInFrame)
        have hFUI := smp_uniqueInstrIds hMatch hUI pf (List.Mem.head _)
        have hFUniq := smp_uniqueScopeIds hMatch hUniq pf (List.Mem.head _)
        have hSlNotStmt : sl ∉ scopeIdsOf [Stmt.cond tid eid tb eb] := by
          simp only [scopeIdsOf, List.mem_cons, List.mem_append, List.mem_nil_iff, or_false]
          intro h; rcases h with (rfl | rfl | h) | h
          · have hLB := scopeBodyOf_of_getElem_condTrue hStmt hFUniq
            have hSlPf : sl ∈ scopeIdsOf pf.body :=
              mem_scopeIdsOf_of_getElem hStmt (by simp [scopeIdsOf])
            have hAgree := smp_scopeBodyOf_agree hMatch hUniq pf (List.Mem.head _) sl hSlPf
            rw [hAgree, hLB] at hSlContains
            exact absurd (uniqueInstrIds_cond_instrDisjoint' hFUI hStmt hInFrame) (by simp; exact hSlContains)
          · exact hEqEid rfl
          · have hSlPf : sl ∈ scopeIdsOf pf.body :=
              mem_scopeIdsOf_of_getElem hStmt (show sl ∈ scopeIdsOf [Stmt.cond tid eid tb eb] from by
                unfold scopeIdsOf; apply List.mem_append_left; apply List.mem_cons_of_mem; apply List.mem_cons_of_mem; apply List.mem_append_left; exact h)
            have hAgree := smp_scopeBodyOf_agree hMatch hUniq pf (List.Mem.head _) sl hSlPf
            rw [hAgree] at hSlContains
            have hDesc := scopeBodyOf_descend_condTrue hStmt h hFUniq
            rw [hDesc] at hSlContains
            cases hLB : scopeBodyOf tb sl with
            | none => simp [hLB] at hSlContains; simp [instrInBody] at hSlContains
            | some val =>
              simp [hLB] at hSlContains
              exact absurd (uniqueInstrIds_cond_instrDisjoint' hFUI hStmt hInFrame)
                (by simp; exact instrInBody_of_scopeBodyOf hLB hSlContains)
          · exact hSlNotFrame h
        have hSlNotPf : sl ∉ scopeIdsOf pf.body :=
          sl_not_in_parent hMatch hUniq hUI (List.Mem.head _) hInPf hSlContains hStmt
            (by simp [instrInBody]; right; exact hInFrame) hSlNotStmt
        exact ih rfl hInPf hSlNotPf

theorem smp_has_stmtIdxAtTop {progBody : List Stmt} {stack : List Frame}
    (hSMP : StackMatchesProgram progBody stack)
    : ∃ si, stmtIdxAtTop stack = some si := by
  induction hSMP with
  | base si ii => exact ⟨si, by simp [stmtIdxAtTop]⟩
  | loop _ _ _ _ _ _ _ _ ih => simp [stmtIdxAtTop]; exact ih
  | cond _ _ _ _ _ _ _ _ _ _ _ ih => simp [stmtIdxAtTop]; exact ih

theorem enclosing_stmtIdxInLoop {stack : List Frame} {sl : ScopeId}
    (h : sl ∈ enclosingLoopsFromStack stack)
    : ∃ si, stmtIdxInLoop stack sl = some si := by
  induction stack with
  | nil => simp [enclosingLoopsFromStack] at h
  | cons f rest ih =>
    cases hk : f.kind with
    | top =>
      simp [enclosingLoopsFromStack, hk] at h
      obtain ⟨si, hsi⟩ := ih h
      exact ⟨si, by simp [stmtIdxInLoop, hk]; exact hsi⟩
    | loop lid =>
      simp [enclosingLoopsFromStack, hk] at h
      rcases h with rfl | h
      · exact ⟨f.stmtIdx, by simp [stmtIdxInLoop, hk]⟩
      · obtain ⟨si, hsi⟩ := ih h
        by_cases heq : lid = sl
        · exact ⟨f.stmtIdx, by simp [stmtIdxInLoop, hk, heq]⟩
        · exact ⟨si, by simp [stmtIdxInLoop, hk, heq]; exact hsi⟩
    | cond sid =>
      simp [enclosingLoopsFromStack, hk] at h
      rcases h with rfl | h
      · exact ⟨f.stmtIdx, by simp [stmtIdxInLoop, hk]⟩
      · obtain ⟨si, hsi⟩ := ih h
        by_cases heq : sid = sl
        · exact ⟨f.stmtIdx, by simp [stmtIdxInLoop, hk, heq]⟩
        · exact ⟨si, by simp [stmtIdxInLoop, hk, heq]; exact hsi⟩
