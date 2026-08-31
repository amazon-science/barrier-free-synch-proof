import SemaAlloc.MatchStates

-- Run all remaining regOps from current regOpIdx to regOps.length.
-- Run all stmtRegOp ops from index 0 to completion, then advance stmtIdx.
-- Starts from stmtRegOpIdx = 0 for simplicity (the common case at loop entry).
theorem stmtRegOpSteps_to_done (impl : ImplProgram) (e : EngineId) (is : ImplState)
    (hEngines : e ∈ impl.engines)
    (frame : ImplFrame) (rest : List ImplFrame)
    (ops : EngineId → List RegOp)
    (hStack : (is.pc e).stack = frame :: rest)
    (hStmt : frame.body[frame.stmtIdx]? = some (ImplStmt.regOp ops))
    (hIdx0 : (is.pc e).stmtRegOpIdx = 0)
    : ∃ is', ImplStar impl e is is' ∧
        (is'.pc e).stack = ⟨frame.body, frame.stmtIdx + 1, frame.kind⟩ :: rest ∧
        (is'.pc e).instrIdx = (is.pc e).instrIdx ∧
        (is'.pc e).regOpIdx = 0 ∧
        (is'.pc e).stmtRegOpIdx = 0 ∧
        (∀ e', e' ≠ e → is'.pc e' = is.pc e') ∧
        is'.inflight = is.inflight ∧
        is'.semaphores = is.semaphores ∧
        is'.dataPathState = is.dataPathState ∧
        is'.controlState = is.controlState ∧
        (∀ e', e' ≠ e → is'.registers e' = is.registers e') ∧
        is'.registers e = foldRegOps (ops e) (is.registers e) := by
  -- Induction on ops list length via fuel
  suffices h : ∀ (n : Nat) (is : ImplState),
      (is.pc e).stack = frame :: rest →
      frame.body[frame.stmtIdx]? = some (ImplStmt.regOp ops) →
      (is.pc e).stmtRegOpIdx + n = (ops e).length →
      (is.pc e).stmtRegOpIdx ≤ (ops e).length →
      ∃ is', ImplStar impl e is is' ∧
        (is'.pc e).stack = ⟨frame.body, frame.stmtIdx + 1, frame.kind⟩ :: rest ∧
        (is'.pc e).instrIdx = (is.pc e).instrIdx ∧
        (is'.pc e).regOpIdx = 0 ∧
        (is'.pc e).stmtRegOpIdx = 0 ∧
        (∀ e', e' ≠ e → is'.pc e' = is.pc e') ∧
        is'.inflight = is.inflight ∧
        is'.semaphores = is.semaphores ∧
        is'.dataPathState = is.dataPathState ∧
        is'.controlState = is.controlState ∧
        (∀ e', e' ≠ e → is'.registers e' = is.registers e') ∧
        is'.registers e = foldRegOps ((ops e).drop (is.pc e).stmtRegOpIdx) (is.registers e) by
    have := h (ops e).length is hStack hStmt (by omega) (by omega)
    rw [hIdx0, List.drop_zero] at this; exact this
  intro n; induction n with
  | zero =>
    intro is' hStack' hStmt' hLen hBound
    have hEq : (is'.pc e).stmtRegOpIdx = (ops e).length := by omega
    have stepDone := ImplStep.stmtRegOpDone e is' hEngines frame rest ops hStack' hStmt' hEq
    exact ⟨_, ImplStar.step stepDone ImplStar.refl,
      by simp [funUpdate], by simp [funUpdate], by simp [funUpdate], by simp [funUpdate],
      fun e' he => by simp [funUpdate, he], rfl, rfl, rfl, rfl, fun e' he => rfl,
      by rw [hEq, List.drop_length]; rfl⟩
  | succ n ih =>
    intro is' hStack' hStmt' hLen hBound
    have hLt : (is'.pc e).stmtRegOpIdx < (ops e).length := by omega
    obtain ⟨dst, src, t, hOp⟩ : ∃ dst src t, (ops e)[(is'.pc e).stmtRegOpIdx]? = some (dst, src, t) :=
      ⟨_, _, _, List.getElem?_eq_some_iff.mpr ⟨hLt, rfl⟩⟩
    have step := ImplStep.stmtRegOpStep e is' hEngines frame rest ops dst src t hStack' hStmt' hOp
    let is₁ : ImplState := ⟨is'.controlState, is'.dataPathState,
      funUpdate is'.pc e { (is'.pc e) with stmtRegOpIdx := (is'.pc e).stmtRegOpIdx + 1 },
      is'.inflight,
      funUpdate is'.registers e (funUpdate (is'.registers e) dst (applyRegOpKind t (is'.registers e src) (is'.registers e dst))),
      is'.semaphores⟩
    have hStack₁ : (is₁.pc e).stack = frame :: rest := by simp [is₁, funUpdate, hStack']
    have hStmt₁ : frame.body[frame.stmtIdx]? = some (ImplStmt.regOp ops) := hStmt'
    have hLen₁ : (is₁.pc e).stmtRegOpIdx + n = (ops e).length := by simp [is₁, funUpdate]; omega
    have hBound₁ : (is₁.pc e).stmtRegOpIdx ≤ (ops e).length := by simp [is₁, funUpdate]; omega
    obtain ⟨is'', hStar, hStack'', hInstr'', hRegOp'', hSROI'', hPC'', hInfl'', hSema'', hDataPath'', hControl'', hRegs'', hRegsE''⟩ :=
      ih is₁ hStack₁ hStmt₁ hLen₁ hBound₁
    refine ⟨is'', ImplStar.step step hStar, hStack'',
      by rw [hInstr'']; simp [is₁, funUpdate],
      hRegOp'', hSROI'',
      fun e' he => by rw [hPC'' e' he]; simp [is₁, funUpdate, he],
      hInfl'', hSema'', hDataPath'', hControl'',
      fun e' he => by rw [hRegs'' e' he]; simp [is₁, funUpdate, he], ?_⟩
    rw [hRegsE'']
    simp only [is₁, funUpdate, ite_true]
    exact (foldRegOps_drop_step hLt hOp).symm

-- Generalized: run remaining stmtRegOps from arbitrary stmtRegOpIdx to completion.
theorem stmtRegOpSteps_from (impl : ImplProgram) (e : EngineId) (is : ImplState)
    (hEngines : e ∈ impl.engines)
    (frame : ImplFrame) (rest : List ImplFrame)
    (ops : EngineId → List RegOp)
    (hStack : (is.pc e).stack = frame :: rest)
    (hStmt : frame.body[frame.stmtIdx]? = some (ImplStmt.regOp ops))
    (hBound : (is.pc e).stmtRegOpIdx ≤ (ops e).length)
    : ∃ is', ImplStar impl e is is' ∧
        (is'.pc e).stack = ⟨frame.body, frame.stmtIdx + 1, frame.kind⟩ :: rest ∧
        (is'.pc e).instrIdx = (is.pc e).instrIdx ∧
        (is'.pc e).regOpIdx = 0 ∧
        (is'.pc e).stmtRegOpIdx = 0 ∧
        (∀ e', e' ≠ e → is'.pc e' = is.pc e') ∧
        is'.inflight = is.inflight ∧
        is'.semaphores = is.semaphores ∧
        is'.dataPathState = is.dataPathState ∧
        is'.controlState = is.controlState ∧
        (∀ e', e' ≠ e → is'.registers e' = is.registers e') ∧
        is'.registers e = foldRegOps ((ops e).drop (is.pc e).stmtRegOpIdx) (is.registers e) := by
  induction h : (ops e).length - (is.pc e).stmtRegOpIdx generalizing is with
  | zero =>
    have hEq : (is.pc e).stmtRegOpIdx = (ops e).length := by omega
    have stepDone := ImplStep.stmtRegOpDone e is hEngines frame rest ops hStack hStmt hEq
    exact ⟨_, ImplStar.step stepDone ImplStar.refl,
      by simp [funUpdate], by simp [funUpdate], by simp [funUpdate], by simp [funUpdate],
      fun e' he => by simp [funUpdate, he], rfl, rfl, rfl, rfl, fun e' he => rfl,
      by rw [hEq, List.drop_length]; rfl⟩
  | succ n ih =>
    have hLt : (is.pc e).stmtRegOpIdx < (ops e).length := by omega
    obtain ⟨dst, src, t, hOp⟩ : ∃ dst src t, (ops e)[(is.pc e).stmtRegOpIdx]? = some (dst, src, t) :=
      ⟨_, _, _, List.getElem?_eq_some_iff.mpr ⟨hLt, rfl⟩⟩
    have step := ImplStep.stmtRegOpStep e is hEngines frame rest ops dst src t hStack hStmt hOp
    let is₁ : ImplState := ⟨is.controlState, is.dataPathState,
      funUpdate is.pc e { (is.pc e) with stmtRegOpIdx := (is.pc e).stmtRegOpIdx + 1 },
      is.inflight,
      funUpdate is.registers e (funUpdate (is.registers e) dst (applyRegOpKind t (is.registers e src) (is.registers e dst))),
      is.semaphores⟩
    have hStack₁ : (is₁.pc e).stack = frame :: rest := by simp [is₁, funUpdate, hStack]
    have hBound₁ : (is₁.pc e).stmtRegOpIdx ≤ (ops e).length := by simp [is₁, funUpdate]; omega
    have hH₁ : (ops e).length - (is₁.pc e).stmtRegOpIdx = n := by simp [is₁, funUpdate]; omega
    obtain ⟨is', hStar, hStack', hInstr', hRegOp', hSROI', hPC', hInfl', hSema', hDataPath', hControl', hRegs', hRegsE'⟩ :=
      ih is₁ hStack₁ hBound₁ hH₁
    refine ⟨is', ImplStar.step step hStar, hStack',
      by rw [hInstr']; simp [is₁, funUpdate],
      hRegOp', hSROI',
      fun e' he => by rw [hPC' e' he]; simp [is₁, funUpdate, he],
      hInfl', hSema', hDataPath', hControl',
      fun e' he => by rw [hRegs' e' he]; simp [is₁, funUpdate, he], ?_⟩
    rw [hRegsE']
    simp only [is₁, funUpdate, ite_true]
    exact (foldRegOps_drop_step hLt hOp).symm

-- Run all remaining regOps from current regOpIdx to regOps.length.
theorem regOpSteps_to_done (impl : ImplProgram) (e : EngineId) (is : ImplState)
    (hEngines : e ∈ impl.engines)
    (frame : ImplFrame) (rest : List ImplFrame) (f : EngineId → List DataPathInstrId) (instr : DataPathInstrId)
    (hStack : (is.pc e).stack = frame :: rest)
    (hStmt : frame.body[frame.stmtIdx]? = some (ImplStmt.block f))
    (hInstr : (f e)[(is.pc e).instrIdx]? = some instr)
    (hBound : (is.pc e).regOpIdx ≤ (impl.regOps e instr).length)
    : ∃ is', ImplStar impl e is is' ∧
        (is'.pc e).stack = (is.pc e).stack ∧
        (is'.pc e).instrIdx = (is.pc e).instrIdx ∧
        (is'.pc e).regOpIdx = (impl.regOps e instr).length ∧
        (∀ e', e' ≠ e → is'.pc e' = is.pc e') ∧
        is'.inflight = is.inflight ∧
        is'.semaphores = is.semaphores ∧
        is'.dataPathState = is.dataPathState ∧
        is'.controlState = is.controlState ∧
        (∀ e', e' ≠ e → is'.registers e' = is.registers e') ∧
        is'.registers e = foldRegOps ((impl.regOps e instr).drop (is.pc e).regOpIdx) (is.registers e) := by
  induction h : (impl.regOps e instr).length - (is.pc e).regOpIdx generalizing is with
  | zero =>
    have hEq : (is.pc e).regOpIdx = (impl.regOps e instr).length := by omega
    exact ⟨is, ImplStar.refl, rfl, rfl, by omega, fun _ _ => rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl,
      by rw [hEq, List.drop_length]; rfl⟩
  | succ n ih =>
    have hLt : (is.pc e).regOpIdx < (impl.regOps e instr).length := by omega
    obtain ⟨dst, src, t, hRegOp⟩ : ∃ dst src t, (impl.regOps e instr)[(is.pc e).regOpIdx]? = some (dst, src, t) :=
      ⟨_, _, _, List.getElem?_eq_some_iff.mpr ⟨hLt, rfl⟩⟩
    have step := ImplStep.regOpStep e is hEngines frame rest f instr dst src t hStack hStmt hInstr hRegOp
    let is₁ : ImplState := ⟨is.controlState, is.dataPathState,
      funUpdate is.pc e { (is.pc e) with regOpIdx := (is.pc e).regOpIdx + 1 },
      is.inflight,
      funUpdate is.registers e (funUpdate (is.registers e) dst (applyRegOpKind t (is.registers e src) (is.registers e dst))),
      is.semaphores⟩
    obtain ⟨is', hStar, hStack', hDataPathInstrIdx', hDone, hPC', hInfl', hSema', hDataPath', hControl', hRegs', hRegsE'⟩ :=
      ih is₁ (by simp [is₁, funUpdate, hStack]) (by simp [is₁, funUpdate]; exact hInstr)
        (by simp [is₁, funUpdate]; omega) (by simp [is₁, funUpdate]; omega)
    refine ⟨is', ImplStar.step step hStar, by rw [hStack']; simp [is₁, funUpdate],
      by rw [hDataPathInstrIdx']; simp [is₁, funUpdate], hDone,
      fun e' he => by rw [hPC' e' he]; simp [is₁, funUpdate, he],
      hInfl', hSema', hDataPath', hControl',
      fun e' he => by rw [hRegs' e' he]; simp [is₁, funUpdate, he], ?_⟩
    rw [hRegsE']
    simp only [is₁, funUpdate, ite_true]
    exact (foldRegOps_drop_step hLt hRegOp).symm

theorem bodyMatch_block_at_spec {monotoneReg tripReg specBody implBody}
    (hBM : BodyMatch monotoneReg tripReg specBody implBody)
    {i : Nat} {f : EngineId → List DataPathInstrId} (hIdx : specBody[i]? = some (Stmt.block f))
    : implBody[i]? = some (ImplStmt.block f) := by
  induction hBM generalizing i with
  | nil => simp at hIdx
  | block _ _ _ _ ih => cases i with | zero => simp_all | succ n => simp at hIdx ⊢; exact ih hIdx
  | loop _ _ _ _ _ _ _ _ ih => cases i with | zero => simp at hIdx | succ n => simp at hIdx ⊢; exact ih hIdx
  | cond _ _ _ _ _ _ _ _ _ _ _ _ _ ih => cases i with | zero => simp at hIdx | succ n => simp at hIdx ⊢; exact ih hIdx

theorem frameCorr_spec_block_stmt {ab : AllocBase spec impl} {sf : Frame} {imf : ImplFrame}
    (hFC : FrameCorr ab sf imf) (hNotRO : ¬ atRegOp imf)
    {f : EngineId → List DataPathInstrId} (hSpecStmt : sf.body[sf.stmtIdx]? = some (Stmt.block f))
    : imf.body[imf.stmtIdx]? = some (ImplStmt.block f) := by
  obtain ⟨hKC, ⟨implBody, hBM, hBE⟩, hIC⟩ := hFC
  have hImplBody := bodyMatch_block_at_spec hBM hSpecStmt
  have hIC2 := hIC.2 hNotRO
  cases hk : imf.kind with
  | loop lid =>
    rw [hk] at hBE hIC2; simp at hBE hIC2; rw [hBE]
    cases hsi : imf.stmtIdx with
    | zero => exact absurd hsi (by simp [atRegOp, hk] at hNotRO; exact hNotRO)
    | succ n => simp [List.getElem?_cons_succ]; rw [show sf.stmtIdx = n from by omega] at hImplBody; exact hImplBody
  | cond sid =>
    rw [hk] at hBE hIC2; simp at hBE hIC2; rw [hBE]
    cases hsi : imf.stmtIdx with
    | zero => exact absurd hsi (by simp [atRegOp, hk] at hNotRO; exact hNotRO)
    | succ n => simp [List.getElem?_cons_succ]; rw [show sf.stmtIdx = n from by omega] at hImplBody; exact hImplBody
  | _ => rw [hk] at hBE hIC2; simp at hBE hIC2; rw [hBE, ← hIC2]; exact hImplBody

theorem bodyMatch_loop_at_spec {monotoneReg tripReg specBody implBody}
    (hBM : BodyMatch monotoneReg tripReg specBody implBody)
    {i : Nat} {lid : ScopeId} {specLoopBody : List Stmt}
    (hIdx : specBody[i]? = some (Stmt.loop lid specLoopBody))
    : ∃ implInner, implBody[i]? = some (ImplStmt.loop lid
        ([ImplStmt.regOp (scopeEntryOps monotoneReg tripReg specLoopBody · lid)] ++ implInner)) ∧
        BodyMatch monotoneReg tripReg specLoopBody implInner := by
  induction hBM generalizing i with
  | nil => simp at hIdx
  | block _ _ _ _ ih => cases i with | zero => simp at hIdx | succ n => simp at hIdx ⊢; exact ih hIdx
  | loop lid' specBody' implBody' _ _ hBody _ _ ih =>
    cases i with
    | zero => simp at hIdx; obtain ⟨rfl, rfl⟩ := hIdx; exact ⟨implBody', by simp, hBody⟩
    | succ n => simp at hIdx ⊢; exact ih hIdx
  | cond _ _ _ _ _ _ _ _ _ _ _ _ _ ih => cases i with | zero => simp at hIdx | succ n => simp at hIdx ⊢; exact ih hIdx

-- NOTE: The impl cond body has prepended regOps: [regOp thenId] ++ implThenInner, [regOp elseId] ++ implElseInner.
-- The BodyMatch is on the INNER bodies (without the regOp prefix).
theorem bodyMatch_cond_at_spec {monotoneReg tripReg specBody implBody}
    (hBM : BodyMatch monotoneReg tripReg specBody implBody)
    {i : Nat} {specThen specElse : List Stmt}
    (hIdx : specBody[i]? = some (Stmt.cond thenId elseId specThen specElse))
    : ∃ implThenInner implElseInner,
        implBody[i]? = some (ImplStmt.cond thenId elseId
          ([ImplStmt.regOp (scopeEntryOps monotoneReg tripReg specThen · thenId)] ++ implThenInner)
          ([ImplStmt.regOp (scopeEntryOps monotoneReg tripReg specElse · elseId)] ++ implElseInner)) ∧
        BodyMatch monotoneReg tripReg specThen implThenInner ∧ BodyMatch monotoneReg tripReg specElse implElseInner := by
  induction hBM generalizing i with
  | nil => simp at hIdx
  | block _ _ _ _ ih => cases i with | zero => simp at hIdx | succ n => simp at hIdx ⊢; exact ih hIdx
  | loop _ _ _ _ _ _ _ _ ih => cases i with | zero => simp at hIdx | succ n => simp at hIdx ⊢; exact ih hIdx
  | cond thenId' elseId' specThen' specElse' _ _ _ _ hThen hElse _ _ _ ih =>
    cases i with
    | zero => simp at hIdx; obtain ⟨rfl, rfl, rfl, rfl⟩ := hIdx; exact ⟨_, _, by simp, hThen, hElse⟩
    | succ n => simp at hIdx ⊢; exact ih hIdx

theorem frameCorr_spec_loop_stmt {ab : AllocBase spec impl} {sf : Frame} {imf : ImplFrame}
    (hFC : FrameCorr ab sf imf) (hNotRO : ¬ atRegOp imf)
    {lid : ScopeId} {specLoopBody : List Stmt}
    (hSpecStmt : sf.body[sf.stmtIdx]? = some (Stmt.loop lid specLoopBody))
    : ∃ implInner, imf.body[imf.stmtIdx]? = some (ImplStmt.loop lid
        ([ImplStmt.regOp (scopeEntryOps ab.monotoneReg ab.tripReg specLoopBody · lid)] ++ implInner)) ∧
        BodyMatch ab.monotoneReg ab.tripReg specLoopBody implInner := by
  obtain ⟨hKC, ⟨implBody, hBM, hBE⟩, hIC⟩ := hFC
  have hImplBody := bodyMatch_loop_at_spec hBM hSpecStmt
  obtain ⟨implInner, hLookup, hBMInner⟩ := hImplBody
  have hIC2 := hIC.2 hNotRO
  cases hk : imf.kind with
  | loop plid =>
    rw [hk] at hBE hIC2; rw [hBE]
    refine ⟨implInner, ?_, hBMInner⟩
    cases hsi : imf.stmtIdx with
    | zero => exact absurd hsi (by simp [atRegOp, hk] at hNotRO; exact hNotRO)
    | succ n => simp [List.getElem?_cons_succ]; rw [show sf.stmtIdx = n from by omega] at hLookup; exact hLookup
  | cond sid =>
    rw [hk] at hBE hIC2; rw [hBE]
    refine ⟨implInner, ?_, hBMInner⟩
    cases hsi : imf.stmtIdx with
    | zero => exact absurd hsi (by simp [atRegOp, hk] at hNotRO; exact hNotRO)
    | succ n => simp [List.getElem?_cons_succ]; rw [show sf.stmtIdx = n from by omega] at hLookup; exact hLookup
  | _ => rw [hk] at hBE hIC2; rw [hBE, ← hIC2]; exact ⟨implInner, hLookup, hBMInner⟩

-- Returns inner bodies (without regOp prefix) and the full impl cond body decomposition.
theorem frameCorr_spec_cond_stmt {ab : AllocBase spec impl} {sf : Frame} {imf : ImplFrame}
    (hFC : FrameCorr ab sf imf) (hNotRO : ¬ atRegOp imf)
    {specThen specElse : List Stmt}
    (hSpecStmt : sf.body[sf.stmtIdx]? = some (Stmt.cond thenId elseId specThen specElse))
    : ∃ implThenInner implElseInner,
        imf.body[imf.stmtIdx]? = some (ImplStmt.cond thenId elseId
          ([ImplStmt.regOp (scopeEntryOps ab.monotoneReg ab.tripReg specThen · thenId)] ++ implThenInner)
          ([ImplStmt.regOp (scopeEntryOps ab.monotoneReg ab.tripReg specElse · elseId)] ++ implElseInner)) ∧
        BodyMatch ab.monotoneReg ab.tripReg specThen implThenInner ∧ BodyMatch ab.monotoneReg ab.tripReg specElse implElseInner := by
  obtain ⟨hKC, ⟨implBody, hBM, hBE⟩, hIC⟩ := hFC
  have hImplBody := bodyMatch_cond_at_spec hBM hSpecStmt
  obtain ⟨implTI, implEI, hLookup, hBMT, hBME⟩ := hImplBody
  have hIC2 := hIC.2 hNotRO
  cases hk : imf.kind with
  | loop plid =>
    rw [hk] at hBE hIC2; rw [hBE]
    refine ⟨implTI, implEI, ?_, hBMT, hBME⟩
    cases hsi : imf.stmtIdx with
    | zero => exact absurd hsi (by simp [atRegOp, hk] at hNotRO; exact hNotRO)
    | succ n => simp [List.getElem?_cons_succ]; rw [show sf.stmtIdx = n from by omega] at hLookup; exact hLookup
  | cond sid =>
    rw [hk] at hBE hIC2; rw [hBE]
    refine ⟨implTI, implEI, ?_, hBMT, hBME⟩
    cases hsi : imf.stmtIdx with
    | zero => exact absurd hsi (by simp [atRegOp, hk] at hNotRO; exact hNotRO)
    | succ n => simp [List.getElem?_cons_succ]; rw [show sf.stmtIdx = n from by omega] at hLookup; exact hLookup
  | _ => rw [hk] at hBE hIC2; rw [hBE, ← hIC2]; exact ⟨implTI, implEI, hLookup, hBMT, hBME⟩

def NotAtRegOp (is : ImplState) : Prop :=
  ∀ e frame rest, (is.pc e).stack = frame :: rest → ¬ atRegOp frame

-- After executing scopeEntryOps, monotoneReg e lid' has the right value:
-- - lid' = sid: old_value + 1
-- - otherwise: unchanged (no clobbering between monotoneReg/tripReg)
private theorem foldRegOps_scopeEntryOps_monotoneReg
    {ab : AllocBase spec impl} {regs : RegId → Nat} {loopBody : List Stmt}
    {e : EngineId} {sid lid' : ScopeId}
    (hInj : ∀ l1 l2, ab.monotoneReg e l1 = ab.monotoneReg e l2 → l1 = l2)
    (hNoClobRS : ∀ l1 l2, ab.tripReg e l1 ≠ ab.monotoneReg e l2)
    : foldRegOps (scopeEntryOps ab.monotoneReg ab.tripReg loopBody e sid) regs (ab.monotoneReg e lid') =
      if lid' = sid then regs (ab.monotoneReg e sid) + 1
      else regs (ab.monotoneReg e lid') := by
  unfold scopeEntryOps
  rw [foldRegOps_append]
  simp only [foldRegOps, applyRegOpKind]
  rw [foldRegOps_other (fun op hMem h => by
    simp [List.mem_map] at hMem
    obtain ⟨child, _, rfl⟩ := hMem
    exact hNoClobRS child lid' h)]
  simp only [funUpdate]
  by_cases hLid : lid' = sid
  · subst hLid; simp [Ne.symm (hNoClobRS lid' lid')]
  · have hRegNe : ab.monotoneReg e lid' ≠ ab.monotoneReg e sid :=
      fun h => hLid (hInj _ _ h)
    simp [hLid, hRegNe, Ne.symm (hNoClobRS sid lid')]

-- shared MatchStates+NotAtRegOp block for forward loop-enter cases.
-- sid param is used to instantiate the FrameKind (.loop sid or .cond sid) and monotoneRegInv.
-- The macro detects whether we're in loopEnter (implLoopBody) or condTrue/condFalse (implThenBody/implElseBody).
-- Expects in loop: hFullPlus, is₁, hDataPath, hInflight, hControl, hSema, hLoopRegInv, hTripRegInv, hPC,
-- hWaitChain, hControlOpEq, hSemaInvMono, ss, is, e, hNotALS, hSfLt, hImfLt, hNewFC, hOldSC,
-- hNotRO, hNARO, sf, srest, imf, imrest, ab, hParentInOuter, hNotSelfParent, hSimReconstructed, hImplStackEq,
-- hFrameKindIsLoop OR hFrameKindIsCond (proof that new frame's kind is .loop sid or .cond sid).
set_option hygiene false in
macro "fwd_loop_enter_matchstates " sid:ident _fkind:term : tactic => `(tactic|
  (refine ⟨_, hFullPlus, ?_, ?_⟩
   · exact { dataPathEq := hDataPath, inflightEq := hInflight
             controlEq := by
               intro e'; simp only [is₂, is₁, funUpdate]; split
               · rw [hControlOpEq, ← hControl]
               · exact hControl e'
             semaInv := hSemaInvMono ss _ is _ rfl rfl hSema
             monotoneRegInv := by
               have hOldNALS := not_atLoopStart_of_not_atRegOp hImplStackEq hNotRO
               intro e' lid' hNALS; by_cases he : e' = e
               · subst he; simp only [is₂, is₁, funUpdate, ite_true]
                 rw [foldRegOps_scopeEntryOps_monotoneReg (ab.monotoneRegInj _) (fun l1 l2 => ab.noClob_trip_loop _ l1 l2)]
                 have hOldVal := hLoopRegInv _ lid' (hOldNALS lid')
                 by_cases hEq : lid' = $sid
                 · rw [if_pos hEq, hEq]; rw [hEq] at hOldVal; rw [hOldVal]
                   exact incrScopeEntryHistory_totalEntries.symm
                 · rw [if_neg hEq]
                   change _ = totalEntries { ss with scopeEntryHistory := incrScopeEntryHistory _ _ _ _ } _ _
                   simp only [totalEntries, incrScopeEntryHistory_ne_sid hEq]
                   exact hOldVal
               · simp only [is₂, is₁, funUpdate, if_neg he] at hNALS ⊢
                 have hNALS' : ¬ atLoopStart is e' lid' := by
                   intro h; apply hNALS; simp only [atLoopStart, funUpdate, if_neg he] at h ⊢; exact h
                 simp only [totalEntries, incrScopeEntryHistory_ne_engine he]
                 exact hLoopRegInv e' lid' hNALS'
             tripRegInv := by
               have hOldNALS := not_atLoopStart_of_not_atRegOp hImplStackEq hNotRO
               intro e' lid' hNALS_all; by_cases he : e' = e
               · subst he; simp only [is₂, is₁, funUpdate, ite_true]
                 have hFold := regOpFold_tripReg_loop_entry hSimReconstructed (not_atLoopStart_of_not_atRegOp hImplStackEq hNotRO) hSidNotChild hSpecInv hUniq hLoopBOf hDirectChild _ hParentInOuter hNotSelfParent
                 simp only [tripEntries, totalEntries]; exact hFold lid'
               · simp only [is₂, is₁, funUpdate, if_neg he] at hNALS_all ⊢
                 have hNALS_all' : ∀ lid'', ¬ atLoopStart is e' lid'' := by
                   intro lid'' h; apply hNALS_all lid''; simp only [atLoopStart, funUpdate, if_neg he] at h ⊢; exact h
                 simp only [tripEntries, scopeParent, totalEntries, incrScopeEntryHistory_ne_engine he]
                 exact hTripRegInv e' lid' hNALS_all'
             pcCorr := by
               intro e'; by_cases he : e' = e
               · subst he; simp only [is₂, is₁, funUpdate, ite_true]
                 refine ⟨StackCorr.cons _ _ (sf :: srest) (imf :: imrest) hNewFC hOldSC
                   (fun _ _ h => by simp at h; obtain ⟨rfl, rfl⟩ := h; exact hSfLt)
                   (fun _ _ h => by simp at h; obtain ⟨rfl, rfl⟩ := h; exact hImfLt)
                   (fun _ _ h => by simp at h; obtain ⟨rfl, rfl⟩ := h; exact hNotRO), rfl⟩
               · simp only [is₂, is₁, funUpdate, if_neg he]; exact hPC e'
             regOpFold := by
               intro e' frame' rest' ops' hStack' hStmt'
               by_cases he : e' = e
               · subst he; simp only [is₂, is₁, funUpdate, ite_true] at hStack'
                 obtain ⟨rfl, rfl⟩ := List.cons.inj hStack'
                 exfalso; exact frameCorr_no_regOp hNewFC (fun hRO => by simp [atRegOp] at hRO) (Nat.le_refl _) hStmt'
               · simp only [is₂, is₁, funUpdate, if_neg he] at hStack' ⊢
                 have ⟨h1, h2⟩ := hRegOpFold e' frame' rest' ops' hStack' hStmt'
                 exact ⟨fun lid => by simp [totalEntries, incrScopeEntryHistory_ne_engine he]; exact h1 lid,
                        fun lid => by simp [tripEntries, scopeParent, totalEntries, incrScopeEntryHistory_ne_engine he]; exact h2 lid⟩
             waitRegChain := by
               intro e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
               by_cases he : e' = e
               · subst he; simp only [is₂, is₁, funUpdate, ite_true] at hROI; omega
               · simp only [is₂, is₁, funUpdate, if_neg he] at hStack' hInstr' hROI ⊢
                 exact hWaitChain e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
             gateRegChain := by
               intro e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
               by_cases he : e' = e
               · subst he; simp only [is₂, is₁, funUpdate, ite_true] at hROI; omega
               · simp only [is₂, is₁, funUpdate, if_neg he] at hStack' hInstr' hROI ⊢
                 exact hGateChain e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI }
   · intro e' fr r hS; by_cases he : e' = e
     · subst he; simp only [is₂, is₁, funUpdate, ite_true] at hS
       obtain ⟨rfl, rfl⟩ := List.cons.inj hS; intro hRO; simp [atRegOp] at hRO
     · simp only [is₂, is₁, funUpdate, if_neg he] at hS; exact hNARO e' fr r hS))

namespace ForwardSim

theorem case_commit (spec : Program) (impl : ImplProgram) (ab : AllocBase spec impl)
    (SemaInv : SpecState → ImplState → Prop)
    (hSemaInvMono : SemaInvMono SemaInv)
    (e : EngineId) (ss : SpecState) (is : ImplState)
    (hSim : MatchStates spec impl ab SemaInv ss is)
    (hNARO : NotAtRegOp is)
    (hEngines : e ∈ impl.engines)
    (idx : Nat) (instr : DataPathInstrId)
    (hSpecIdx : (ss.inflight e)[idx]? = some (instr, Phase.issued))
    : let ss' := { ss with
        dataPathState := spec.instrOp instr ss.dataPathState
        inflight := funUpdate ss.inflight e
          ((ss.inflight e).set idx (instr, Phase.committed)) }
      ∃ is', ImplPlusAny impl is is' ∧ MatchStates spec impl ab SemaInv ss' is' ∧ NotAtRegOp is' := by
    obtain ⟨hDataPath, hInflight, hControl, hSema, hLoopRegInv, hTripRegInv, hRegOpFold, hPC, hWaitChain, hGateChain⟩ := hSim
    have hImplIdx : (is.inflight e)[idx]? = some (instr, Phase.issued) := by rw [hInflight]; exact hSpecIdx
    refine ⟨_, ImplPlusAny.step (ImplStep.commit e is hEngines idx instr hImplIdx) ImplStarAny.refl, ?_, ?_⟩
    · exact { dataPathEq := by rw [congrArg ProgramBase.instrOp ab.baseEq, hDataPath]
              inflightEq := by intro e'; simp only [funUpdate]; split <;> simp [hInflight]
              controlEq := hControl, semaInv := hSemaInvMono ss _ is _ rfl rfl hSema, monotoneRegInv := hLoopRegInv
              tripRegInv := hTripRegInv, regOpFold := hRegOpFold, pcCorr := hPC
              waitRegChain := hWaitChain, gateRegChain := hGateChain }
    · exact hNARO

theorem case_retire (spec : Program) (impl : ImplProgram) (ab : AllocBase spec impl)
    (SemaInv : SpecState → ImplState → Prop)
    (hRetireSema : ∀ (e' : EngineId) (instr : DataPathInstrId) (rest : List (DataPathInstrId × Phase))
      (ss0 : SpecState) (is0 : ImplState),
      SemaInv ss0 is0 →
      ss0.inflight e' = (instr, Phase.committed) :: rest →
      let ss1 := specRetireUpdate ss0 e' instr rest
      let is1 := { is0 with inflight := funUpdate is0.inflight e' rest,
                            semaphores := funUpdate is0.semaphores (impl.updateOf instr) (is0.semaphores (impl.updateOf instr) + 1) }
      SemaInv ss1 is1)
    (e : EngineId) (ss : SpecState) (is : ImplState)
    (hSim : MatchStates spec impl ab SemaInv ss is)
    (hNARO : NotAtRegOp is)
    (hEngines : e ∈ impl.engines)
    (instr : DataPathInstrId) (inflightRest : List (DataPathInstrId × Phase))
    (hSpecHead : ss.inflight e = (instr, Phase.committed) :: inflightRest)
    : let ss' := specRetireUpdate ss e instr inflightRest
      ∃ is', ImplPlusAny impl is is' ∧ MatchStates spec impl ab SemaInv ss' is' ∧ NotAtRegOp is' := by
    obtain ⟨hDataPath, hInflight, hControl, hSema, hLoopRegInv, hTripRegInv, hRegOpFold, hPC, hWaitChain, hGateChain⟩ := hSim
    have hImplHead : is.inflight e = (instr, Phase.committed) :: inflightRest := by rw [hInflight]; exact hSpecHead
    refine ⟨_, ImplPlusAny.step (ImplStep.retire e is hEngines instr inflightRest hImplHead) ImplStarAny.refl, ?_, ?_⟩
    · exact { dataPathEq := hDataPath
              inflightEq := by intro e'; simp only [funUpdate]; split <;> simp [hInflight]
              controlEq := hControl
              semaInv := hRetireSema e instr inflightRest ss is hSema hSpecHead
              monotoneRegInv := by
                intro e' lid hNALS; simp [totalEntries]
                exact hLoopRegInv e' lid hNALS
              tripRegInv := by
                intro e' lid hNALS_all; simp [tripEntries]
                exact hTripRegInv e' lid hNALS_all
              regOpFold := by
                intro e' fr r ops hStack hStmt
                have ⟨h1, h2⟩ := hRegOpFold e' fr r ops hStack hStmt
                exact ⟨fun lid => by simp [totalEntries]; exact h1 lid,
                       fun lid => by simp [tripEntries, totalEntries]; exact h2 lid⟩
              pcCorr := hPC
              waitRegChain := hWaitChain, gateRegChain := hGateChain }
    · exact hNARO

theorem case_blockDone (spec : Program) (impl : ImplProgram) (ab : AllocBase spec impl)
    (SemaInv : SpecState → ImplState → Prop)
    (hSemaInvMono : SemaInvMono SemaInv)
    (e : EngineId) (ss : SpecState) (is : ImplState)
    (hSim : MatchStates spec impl ab SemaInv ss is)
    (hNARO : NotAtRegOp is)
    (hEngines : e ∈ impl.engines)
    (sf : Frame) (srest : List Frame) (f : EngineId → List DataPathInstrId)
    (hSpecStack : (ss.pc e).stack = sf :: srest)
    (hSpecStmt : sf.body[sf.stmtIdx]? = some (Stmt.block f))
    (hSpecDone : (ss.pc e).instrIdx = (f e).length)
    : let ss' := { ss with
        pc := funUpdate ss.pc e
          { stack := ⟨sf.body, sf.stmtIdx + 1, sf.kind⟩ :: srest, instrIdx := 0 } }
      ∃ is', ImplPlusAny impl is is' ∧ MatchStates spec impl ab SemaInv ss' is' ∧ NotAtRegOp is' := by
    obtain ⟨hDataPath, hInflight, hControl, hSema, hLoopRegInv, hTripRegInv, hRegOpFold, hPC, hWaitChain, hGateChain⟩ := hSim
    have hSC := (hPC e).stackCorr; rw [hSpecStack] at hSC
    obtain ⟨imf, imrest, hImplStackEq, hFC, hRestCorr, hCovS, hCovI, hNRO⟩ := stackCorr_spec_cons_inv hSC
    have hNotRO : ¬ atRegOp imf := hNARO e imf imrest hImplStackEq
    have hImplStmt := frameCorr_spec_block_stmt hFC hNotRO hSpecStmt
    have hImplDone : (is.pc e).instrIdx = (f e).length := by rw [← (hPC e).instrEq]; exact hSpecDone
    refine ⟨_, ImplPlusAny.step (ImplStep.blockDone e is hEngines imf imrest f hImplStackEq hImplStmt hImplDone) ImplStarAny.refl, ?_, ?_⟩
    · have hNewFC : FrameCorr ab ⟨sf.body, sf.stmtIdx + 1, sf.kind⟩ ⟨imf.body, imf.stmtIdx + 1, imf.kind⟩ := by
        obtain ⟨hKC, ⟨ib, hBM, hBE⟩, hIC⟩ := hFC
        exact ⟨hKC, ⟨ib, hBM, hBE⟩, ⟨fun hRO => by cases hk : imf.kind <;> simp [atRegOp, hk] at hRO,
          fun _ => by have hIdx := hIC.2 hNotRO; cases hk : imf.kind <;> (rw [hk] at hIdx; simp at hIdx; simp; omega)⟩⟩
      exact MatchStates.of_funUpdate_pc ⟨hDataPath, hInflight, hControl, hSema, hLoopRegInv, hTripRegInv, hRegOpFold, hPC, hWaitChain, hGateChain⟩ hSemaInvMono _ _
              ⟨StackCorr.cons _ _ srest imrest hNewFC hRestCorr hCovS hCovI hNRO, rfl⟩
              rfl (by
                intro e' lid; constructor
                · intro ⟨fr, r, hS, hK, hI⟩; by_cases he : e' = e
                  · subst he; simp at hS; obtain ⟨rfl, rfl⟩ := hS; simp at hI
                  · exact ⟨fr, r, by simp [he] at hS; exact hS, hK, hI⟩
                · intro ⟨fr, r, hS, hK, hI⟩; by_cases he : e' = e
                  · subst he; rw [hImplStackEq] at hS; obtain rfl := (List.cons.inj hS).1
                    exact absurd (by cases hk : imf.kind <;> simp [atRegOp, hk] at hK ⊢ <;> exact hI) hNotRO
                  · exact ⟨fr, r, by simp [he]; exact hS, hK, hI⟩)
              (fun _ _ _ hStack hStmt => by
                simp at hStack; obtain ⟨rfl, rfl⟩ := hStack
                exact frameCorr_no_regOp hFC hNotRO (Nat.le_succ _) hStmt)
    · intro e' fr r hS; by_cases he : e' = e
      · subst he; simp only [funUpdate, ite_true] at hS
        obtain ⟨rfl, rfl⟩ := List.cons.inj hS
        intro hRO; cases hk : imf.kind <;> simp [atRegOp, hk] at hRO
      · simp only [funUpdate, if_neg he] at hS; exact hNARO e' fr r hS

theorem case_loopEnter (spec : Program) (impl : ImplProgram) (ab : AllocBase spec impl)
    (SemaInv : SpecState → ImplState → Prop)
    (hSemaInvMono : SemaInvMono SemaInv)
    (e : EngineId) (ss : SpecState) (is : ImplState)
    (hSim : MatchStates spec impl ab SemaInv ss is)
    (hNARO : NotAtRegOp is)
    (hEngines : e ∈ impl.engines)
    (hSpecInv : SpecInv spec ss) (hUniq : UniqueScopeIds spec.body)
    (sf : Frame) (srest : List Frame) (lid : ScopeId) (loopBody : List Stmt)
    (hSpecStack : (ss.pc e).stack = sf :: srest)
    (hSpecStmt : sf.body[sf.stmtIdx]? = some (Stmt.loop lid loopBody))
    (hSpecGuard : spec.guard e lid (ss.controlState e) = true)
    (hParentInOuter : ∀ parent, scopeParent spec.body lid = some parent →
        parent ∈ enclosingLoopsFromStack (sf :: srest))
    (hNotSelfParent : ∀ parent, scopeParent spec.body lid = some parent → parent ≠ lid)
    : let ss' := { ss with
        pc := funUpdate ss.pc e
          { stack := ⟨loopBody, 0, .loop lid⟩ :: sf :: srest, instrIdx := 0 }
        controlState := funUpdate ss.controlState e
          (spec.controlOp e lid (ss.controlState e))
        scopeEntryHistory := incrScopeEntryHistory ss e lid
          (enclosingLoopsFromStack (sf :: srest)) }
      ∃ is', ImplPlusAny impl is is' ∧ MatchStates spec impl ab SemaInv ss' is' ∧ NotAtRegOp is' := by
    obtain ⟨hDataPath, hInflight, hControl, hSema, hLoopRegInv, hTripRegInv, hRegOpFold, hPC, hWaitChain, hGateChain⟩ := hSim
    have hSC := (hPC e).stackCorr; rw [hSpecStack] at hSC
    obtain ⟨imf, imrest, hImplStackEq, hFC, hRestCorr, hCovS, hCovI, hNRO⟩ := stackCorr_spec_cons_inv hSC
    have hNotRO : ¬ atRegOp imf := hNARO e imf imrest hImplStackEq
    obtain ⟨implInner, hImplLoop, hInnerMatch⟩ := frameCorr_spec_loop_stmt hFC hNotRO hSpecStmt
    have hGuardEq : spec.guard = impl.guard := congrArg ProgramBase.guard ab.baseEq
    have hImplGuard : impl.guard e lid (is.controlState e) = true := by rw [← hGuardEq, hControl]; exact hSpecGuard
    let implLoopBody := [ImplStmt.regOp (fun e' => scopeEntryOps ab.monotoneReg ab.tripReg loopBody e' lid)] ++ implInner
    have step1 := ImplStep.loopEnter e is hEngines imf imrest lid implLoopBody hImplStackEq hImplLoop hImplGuard
    let is₁ : ImplState := { is with
      pc := funUpdate is.pc e { stack := ⟨implLoopBody, 0, .loop lid⟩ :: imf :: imrest, instrIdx := 0, regOpIdx := 0, stmtRegOpIdx := 0 }
      controlState := funUpdate is.controlState e (impl.controlOp e lid (is.controlState e)) }
    have hStack₁ : (is₁.pc e).stack = ⟨implLoopBody, 0, .loop lid⟩ :: imf :: imrest := by simp [is₁, funUpdate]
    have hStmt₁ : implLoopBody[0]? = some (ImplStmt.regOp (fun e' => scopeEntryOps ab.monotoneReg ab.tripReg loopBody e' lid)) := by
      simp [implLoopBody]
    have hIdx0₁ : (is₁.pc e).stmtRegOpIdx = 0 := by simp [is₁, funUpdate]
    obtain ⟨is₂_wit, step2_wit, hStack₂, hInstr₂, hRegOp₂, hSROI₂, hPC₂, hInfl₂, hSema₂, hDataPath₂, hControl₂, hRegs₂, hRegsE₂⟩ :=
      stmtRegOpSteps_to_done impl e is₁ hEngines ⟨implLoopBody, 0, .loop lid⟩ (imf :: imrest)
        (fun e' => scopeEntryOps ab.monotoneReg ab.tripReg loopBody e' lid) hStack₁ hStmt₁ hIdx0₁
    let is₂ : ImplState := { is₁ with
      pc := funUpdate is₁.pc e { stack := ⟨implLoopBody, 1, .loop lid⟩ :: imf :: imrest, instrIdx := (is₁.pc e).instrIdx, regOpIdx := 0, stmtRegOpIdx := 0 }
      registers := funUpdate is₁.registers e (foldRegOps (scopeEntryOps ab.monotoneReg ab.tripReg loopBody e lid) (is₁.registers e)) }
    have step2 : ImplStar impl e is₁ is₂ := by
      have hEq : is₂_wit = is₂ := by
        have hPCe : is₂_wit.pc e = is₂.pc e := by
          simp only [is₂, funUpdate, ite_true]
          have h1 := hStack₂; simp at h1
          exact ImplPC.ext h1 hInstr₂ (by simpa using hRegOp₂) (by simpa using hSROI₂)
        exact ImplState.ext hControl₂ hDataPath₂
          (funext fun e' => by
            by_cases he : e' = e
            · subst he; exact hPCe
            · simp only [is₂, funUpdate, if_neg he]; exact hPC₂ _ he)
          hInfl₂
          (funext fun e' => funext fun r => by
            by_cases he : e' = e
            · subst he; simp only [is₂, funUpdate, ite_true]; exact congrFun hRegsE₂ r
            · simp only [is₂, funUpdate, if_neg he]; exact congrFun (hRegs₂ _ he) r)
          hSema₂
      exact hEq ▸ step2_wit
    have hFullPlus : ImplPlusAny impl is is₂ := ImplPlusAny.step step1 (ImplStar_to_ImplStarAny step2)
    have hControlOpEq : spec.controlOp = impl.controlOp := congrArg ProgramBase.controlOp ab.baseEq
    have hNotALS : ∀ lid', ¬ atLoopStart is e lid' := not_atLoopStart_of_not_atRegOp hImplStackEq hNotRO
    have hSfLt : sf.stmtIdx < sf.body.length := Nat.lt_of_not_le (fun h => by simp [List.getElem?_eq_none h] at hSpecStmt)
    have hImfLt : imf.stmtIdx < imf.body.length := Nat.lt_of_not_le (fun h => by simp [List.getElem?_eq_none h] at hImplLoop)
    have hNewFC : FrameCorr ab ⟨loopBody, 0, .loop lid⟩ ⟨implLoopBody, 1, .loop lid⟩ :=
      ⟨by simp [frameKindCorr], ⟨implInner, hInnerMatch, rfl⟩,
       ⟨fun hRO => by simp [atRegOp] at hRO,
        fun _ => by simp⟩⟩
    have hOldSC := StackCorr.cons sf imf srest imrest hFC hRestCorr hCovS hCovI hNRO
    have hSimReconstructed : MatchStates spec impl ab SemaInv ss is :=
      { dataPathEq := hDataPath, inflightEq := hInflight, controlEq := hControl, semaInv := hSema,
        monotoneRegInv := hLoopRegInv, tripRegInv := hTripRegInv, regOpFold := hRegOpFold, pcCorr := hPC, waitRegChain := hWaitChain, gateRegChain := hGateChain }
    have hSMP_fwd := hSpecInv.wellFormedPC e; rw [hSpecStack] at hSMP_fwd
    have hUniqBody_fwd := smp_uniqueScopeIds hSMP_fwd hUniq sf (List.Mem.head _)
    have hSidNotChild : lid ∉ directChildScopes loopBody := by
      have h := uniqueScopeIds_of_getElem hSpecStmt hUniqBody_fwd
      cases h with | loop _ _ _ hNB _ _ _ _ => exact fun hC => hNB (directChildScopes_mem_scopeIdsOf _ _ hC)
    have hLoopBOf : scopeBodyOf spec.body lid = some loopBody := by
      have hLocal := scopeBodyOf_of_getElem hSpecStmt hUniqBody_fwd
      exact smp_scopeBodyOf_agree hSMP_fwd hUniq sf (List.Mem.head _) lid
        (mem_scopeIdsOf_of_getElem hSpecStmt (by simp [scopeIdsOf])) |>.symm ▸ hLocal
    have hDirectChild : ∀ lid', lid' ∈ directChildScopes loopBody → lid' ≠ lid → scopeParent spec.body lid' = some lid := by
      intro lid' hChild hNeLid
      have hLidInSB := directChildScopes_mem_scopeIdsOf _ _ hChild
      have hUniqSB : UniqueScopeIds loopBody := by
        have h := uniqueScopeIds_of_getElem hSpecStmt hUniqBody_fwd
        cases h with | loop _ _ _ _ _ _ hU _ => exact hU
      have hGoInner := directChild_scopeParent_go loopBody lid' lid hChild hUniqSB
      have hGoLocal := scopeParent_go_lift_loop (container := sf.kind.loopId?) hSpecStmt hUniqBody_fwd hGoInner hLidInSB
      have hMem := mem_scopeIdsOf_of_getElem hSpecStmt (by simp [scopeIdsOf]; right; exact hLidInSB)
      unfold scopeParent; exact smp_lift_scopeParent_go hSMP_fwd hUniq sf srest rfl hGoLocal hMem
    fwd_loop_enter_matchstates lid (.loop lid)

theorem case_loopSkip (spec : Program) (impl : ImplProgram) (ab : AllocBase spec impl)
    (SemaInv : SpecState → ImplState → Prop)
    (hSemaInvMono : SemaInvMono SemaInv)
    (e : EngineId) (ss : SpecState) (is : ImplState)
    (hSim : MatchStates spec impl ab SemaInv ss is)
    (hNARO : NotAtRegOp is)
    (hEngines : e ∈ impl.engines)
    (sf : Frame) (srest : List Frame) (lid : ScopeId) (loopBody : List Stmt)
    (hSpecStack : (ss.pc e).stack = sf :: srest)
    (hSpecStmt : sf.body[sf.stmtIdx]? = some (Stmt.loop lid loopBody))
    (hSpecGuard : spec.guard e lid (ss.controlState e) = false)
    : let ss' := { ss with
        pc := funUpdate ss.pc e
          { stack := ⟨sf.body, sf.stmtIdx + 1, sf.kind⟩ :: srest, instrIdx := 0 } }
      ∃ is', ImplPlusAny impl is is' ∧ MatchStates spec impl ab SemaInv ss' is' ∧ NotAtRegOp is' := by
    obtain ⟨hDataPath, hInflight, hControl, hSema, hLoopRegInv, hTripRegInv, hRegOpFold, hPC, hWaitChain, hGateChain⟩ := hSim
    have hSC := (hPC e).stackCorr; rw [hSpecStack] at hSC
    obtain ⟨imf, imrest, hImplStackEq, hFC, hRestCorr, hCovS, hCovI, hNRO⟩ := stackCorr_spec_cons_inv hSC
    have hNotRO : ¬ atRegOp imf := hNARO e imf imrest hImplStackEq
    obtain ⟨implInner, hImplLoop, hInnerMatch⟩ := frameCorr_spec_loop_stmt hFC hNotRO hSpecStmt
    have hGuardEq : spec.guard = impl.guard := congrArg ProgramBase.guard ab.baseEq
    have hImplGuard : impl.guard e lid (is.controlState e) = false := by rw [← hGuardEq, hControl]; exact hSpecGuard
    have step1 := ImplStep.loopSkip e is hEngines imf imrest lid _ hImplStackEq hImplLoop hImplGuard
    have hNewFC : FrameCorr ab ⟨sf.body, sf.stmtIdx + 1, sf.kind⟩ ⟨imf.body, imf.stmtIdx + 1, imf.kind⟩ := by
      obtain ⟨hKC, ⟨ib, hBM, hBE⟩, hIC⟩ := hFC
      exact ⟨hKC, ⟨ib, hBM, hBE⟩, ⟨fun hRO => by cases hk : imf.kind <;> simp [atRegOp, hk] at hRO,
        fun _ => by have hIdx := hIC.2 hNotRO; cases hk : imf.kind <;> (rw [hk] at hIdx; simp at hIdx; simp; omega)⟩⟩
    refine ⟨_, ImplPlusAny.step step1 ImplStarAny.refl, ?_, ?_⟩
    · exact MatchStates.of_funUpdate_pc ⟨hDataPath, hInflight, hControl, hSema, hLoopRegInv, hTripRegInv, hRegOpFold, hPC, hWaitChain, hGateChain⟩ hSemaInvMono _ _
              ⟨StackCorr.cons _ _ srest imrest hNewFC hRestCorr hCovS hCovI hNRO, rfl⟩
              rfl (by
                intro e' lid'; constructor
                · intro ⟨fr, r, hS, hK, hI⟩; by_cases he : e' = e
                  · subst he; simp only [funUpdate, ite_true] at hS
                    obtain ⟨rfl, rfl⟩ := List.cons.inj hS; simp at hI
                  · simp only [funUpdate, if_neg he] at hS; exact ⟨fr, r, hS, hK, hI⟩
                · intro ⟨fr, r, hS, hK, hI⟩; by_cases he : e' = e
                  · subst he; rw [hImplStackEq] at hS; obtain rfl := (List.cons.inj hS).1
                    exact absurd (by cases hk : imf.kind <;> simp [atRegOp, hk] at hK ⊢ <;> exact hI) hNotRO
                  · exact ⟨fr, r, by simp only [funUpdate, if_neg he]; exact hS, hK, hI⟩)
              (fun _ _ _ hStack hStmt => by
                simp at hStack; obtain ⟨rfl, rfl⟩ := hStack
                exact frameCorr_no_regOp hFC hNotRO (Nat.le_succ _) hStmt)
    · intro e' fr r hS; by_cases he : e' = e
      · subst he; simp only [funUpdate, ite_true] at hS
        obtain ⟨rfl, rfl⟩ := List.cons.inj hS
        intro hRO; cases hk : imf.kind <;> simp [atRegOp, hk] at hRO
      · simp only [funUpdate, if_neg he] at hS; exact hNARO e' fr r hS

theorem case_loopBack (spec : Program) (impl : ImplProgram) (ab : AllocBase spec impl)
    (SemaInv : SpecState → ImplState → Prop)
    (hSemaInvMono : SemaInvMono SemaInv)
    (e : EngineId) (ss : SpecState) (is : ImplState)
    (hSim : MatchStates spec impl ab SemaInv ss is)
    (hNARO : NotAtRegOp is)
    (hEngines : e ∈ impl.engines)
    (sf sparent : Frame) (srest : List Frame) (lid : ScopeId)
    (hSpecStack : (ss.pc e).stack = sf :: sparent :: srest)
    (hSpecKind : sf.kind = .loop lid)
    (hSpecEnd : sf.stmtIdx = sf.body.length)
    : let ss' := { ss with
        pc := funUpdate ss.pc e
          { stack := sparent :: srest, instrIdx := 0 } }
      ∃ is', ImplPlusAny impl is is' ∧ MatchStates spec impl ab SemaInv ss' is' ∧ NotAtRegOp is' := by
    obtain ⟨hDataPath, hInflight, hControl, hSema, hLoopRegInv, hTripRegInv, hRegOpFold, hPC, hWaitChain, hGateChain⟩ := hSim
    have hSC := (hPC e).stackCorr; rw [hSpecStack] at hSC
    obtain ⟨imf, imrest', hImplStackEq, hFC, hRestCorr', hCovS', hCovI', hNRO'⟩ := stackCorr_spec_cons_inv hSC
    obtain ⟨parent, imrest, hImrest', hPFC, hRestCorr, hCovS, hCovI, hNRO⟩ := stackCorr_spec_cons_inv hRestCorr'
    have hImplKind : imf.kind = .loop lid := by
      obtain ⟨hKC, _, _⟩ := hFC; revert hKC; rw [hSpecKind]; cases imf.kind <;> simp [frameKindCorr, eq_comm]
    have hNotRO : ¬ atRegOp imf := hNARO e imf imrest' hImplStackEq
    have hImplEnd : imf.stmtIdx = imf.body.length := by
      obtain ⟨_, ⟨ib, hBM, hBE⟩, hIC⟩ := hFC
      have hIC2 := hIC.2 hNotRO; rw [hImplKind] at hBE hIC2; simp at hBE hIC2
      rw [hBE]; simp; rw [← bodyMatch_length hBM, ← hSpecEnd]; omega
    have step1 := ImplStep.loopBack (impl := impl) e is hEngines imf parent imrest lid
      (by rw [hImplStackEq, hImrest']) hImplKind hImplEnd
    refine ⟨_, ImplPlusAny.step step1 ImplStarAny.refl, ?_, ?_⟩
    · exact MatchStates.of_funUpdate_pc ⟨hDataPath, hInflight, hControl, hSema, hLoopRegInv, hTripRegInv, hRegOpFold, hPC, hWaitChain, hGateChain⟩ hSemaInvMono _ _
              ⟨StackCorr.cons _ _ srest imrest hPFC hRestCorr hCovS hCovI hNRO, rfl⟩
              rfl (by
                intro e' lid'; constructor
                · intro ⟨fr, r, hS, hK, hI⟩; by_cases he : e' = e
                  · subst he; simp only [funUpdate, ite_true] at hS
                    obtain ⟨rfl, rfl⟩ := List.cons.inj hS
                    exact absurd (by cases hk : parent.kind <;> simp [atRegOp, hk] at hK ⊢ <;> exact hI)
                      (hNRO' parent imrest hImrest')
                  · simp only [funUpdate, if_neg he] at hS; exact ⟨fr, r, hS, hK, hI⟩
                · intro ⟨fr, r, hS, hK, hI⟩; by_cases he : e' = e
                  · subst he; rw [hImplStackEq] at hS; obtain rfl := (List.cons.inj hS).1
                    rw [hImplEnd] at hI
                    have : imf.body.length ≥ 1 := by
                      obtain ⟨_, ⟨ib, _, hBE⟩, _⟩ := hFC; rw [hImplKind] at hBE; simp at hBE; rw [hBE]; simp
                    exact absurd hI (by omega)
                  · exact ⟨fr, r, by simp only [funUpdate, if_neg he]; exact hS, hK, hI⟩)
              (fun _ _ _ hStack hStmt => by
                simp at hStack; obtain ⟨rfl, rfl⟩ := hStack
                exact frameCorr_no_regOp hPFC (hNRO' parent imrest hImrest') (Nat.le_refl _) hStmt)
    · intro e' fr r hS; by_cases he : e' = e
      · subst he; simp only [funUpdate, ite_true] at hS
        obtain ⟨rfl, rfl⟩ := List.cons.inj hS; exact hNRO' parent imrest hImrest'
      · simp only [funUpdate, if_neg he] at hS; exact hNARO e' fr r hS

theorem case_condTrue (spec : Program) (impl : ImplProgram) (ab : AllocBase spec impl)
    (SemaInv : SpecState → ImplState → Prop)
    (hSemaInvMono : SemaInvMono SemaInv)
    (e : EngineId) (ss : SpecState) (is : ImplState)
    (hSim : MatchStates spec impl ab SemaInv ss is)
    (hNARO : NotAtRegOp is)
    (hEngines : e ∈ impl.engines)
    (hSpecInv : SpecInv spec ss) (hUniq : UniqueScopeIds spec.body)
    (sf : Frame) (srest : List Frame)
    (thenId elseId : ScopeId) (specThen specElse : List Stmt)
    (hSpecStack : (ss.pc e).stack = sf :: srest)
    (hSpecStmt : sf.body[sf.stmtIdx]? = some (Stmt.cond thenId elseId specThen specElse))
    (hSpecGuard : spec.guard e thenId (ss.controlState e) = true)
    (hParentInOuter : ∀ parent, scopeParent spec.body thenId = some parent →
        parent ∈ enclosingLoopsFromStack (sf :: srest))
    (hNotSelfParent : ∀ parent, scopeParent spec.body thenId = some parent → parent ≠ thenId)
    : let ss' := { ss with
        pc := funUpdate ss.pc e
          { stack := ⟨specThen, 0, .cond thenId⟩ :: sf :: srest, instrIdx := 0 }
        controlState := funUpdate ss.controlState e
          (spec.controlOp e thenId (ss.controlState e))
        scopeEntryHistory := incrScopeEntryHistory ss e thenId
          (enclosingLoopsFromStack (sf :: srest)) }
      ∃ is', ImplPlusAny impl is is' ∧ MatchStates spec impl ab SemaInv ss' is' ∧ NotAtRegOp is' := by
    obtain ⟨hDataPath, hInflight, hControl, hSema, hLoopRegInv, hTripRegInv, hRegOpFold, hPC, hWaitChain, hGateChain⟩ := hSim
    have hSC := (hPC e).stackCorr; rw [hSpecStack] at hSC
    obtain ⟨imf, imrest, hImplStackEq, hFC, hRestCorr, hCovS, hCovI, hNRO⟩ := stackCorr_spec_cons_inv hSC
    have hNotRO : ¬ atRegOp imf := hNARO e imf imrest hImplStackEq
    obtain ⟨implThenInner, implElseInner, hImplStmt, hThenMatch, _⟩ := frameCorr_spec_cond_stmt hFC hNotRO hSpecStmt
    have hGuardEq : spec.guard = impl.guard := congrArg ProgramBase.guard ab.baseEq
    have hControlOpEq : spec.controlOp = impl.controlOp := congrArg ProgramBase.controlOp ab.baseEq
    let implThenBody := [ImplStmt.regOp (fun e' => scopeEntryOps ab.monotoneReg ab.tripReg specThen e' thenId)] ++ implThenInner
    let implElseBody := [ImplStmt.regOp (fun e' => scopeEntryOps ab.monotoneReg ab.tripReg specElse e' elseId)] ++ implElseInner
    have step1 := ImplStep.condTrue e is hEngines imf imrest thenId elseId implThenBody implElseBody hImplStackEq hImplStmt
      (by rw [← hGuardEq, hControl]; exact hSpecGuard)
    let is₁ : ImplState := { is with
      pc := funUpdate is.pc e { stack := ⟨implThenBody, 0, .cond thenId⟩ :: imf :: imrest, instrIdx := 0, regOpIdx := 0, stmtRegOpIdx := 0 }
      controlState := funUpdate is.controlState e (impl.controlOp e thenId (is.controlState e)) }
    have hStack₁ : (is₁.pc e).stack = ⟨implThenBody, 0, .cond thenId⟩ :: imf :: imrest := by simp [is₁, funUpdate]
    have hStmt₁ : implThenBody[0]? = some (ImplStmt.regOp (fun e' => scopeEntryOps ab.monotoneReg ab.tripReg specThen e' thenId)) := by
      simp [implThenBody]
    have hIdx0₁ : (is₁.pc e).stmtRegOpIdx = 0 := by simp [is₁, funUpdate]
    obtain ⟨is₂_wit, step2_wit, hStack₂, hInstr₂, hRegOp₂, hSROI₂, hPC₂, hInfl₂, hSema₂, hDataPath₂, hControl₂, hRegs₂, hRegsE₂⟩ :=
      stmtRegOpSteps_to_done impl e is₁ hEngines ⟨implThenBody, 0, .cond thenId⟩ (imf :: imrest)
        (fun e' => scopeEntryOps ab.monotoneReg ab.tripReg specThen e' thenId) hStack₁ hStmt₁ hIdx0₁
    let is₂ : ImplState := { is₁ with
      pc := funUpdate is₁.pc e { stack := ⟨implThenBody, 1, .cond thenId⟩ :: imf :: imrest, instrIdx := (is₁.pc e).instrIdx, regOpIdx := 0, stmtRegOpIdx := 0 }
      registers := funUpdate is₁.registers e (foldRegOps (scopeEntryOps ab.monotoneReg ab.tripReg specThen e thenId) (is₁.registers e)) }
    have step2 : ImplStar impl e is₁ is₂ := by
      have hEq : is₂_wit = is₂ := by
        have hPCe : is₂_wit.pc e = is₂.pc e := by
          simp only [is₂, funUpdate, ite_true]
          have h1 := hStack₂; simp at h1
          exact ImplPC.ext h1 hInstr₂ (by simpa using hRegOp₂) (by simpa using hSROI₂)
        exact ImplState.ext hControl₂ hDataPath₂
          (funext fun e' => by
            by_cases he : e' = e
            · subst he; exact hPCe
            · simp only [is₂, funUpdate, if_neg he]; exact hPC₂ _ he)
          hInfl₂
          (funext fun e' => funext fun r => by
            by_cases he : e' = e
            · subst he; simp only [is₂, funUpdate, ite_true]; exact congrFun hRegsE₂ r
            · simp only [is₂, funUpdate, if_neg he]; exact congrFun (hRegs₂ _ he) r)
          hSema₂
      exact hEq ▸ step2_wit
    have hFullPlus : ImplPlusAny impl is is₂ := ImplPlusAny.step step1 (ImplStar_to_ImplStarAny step2)
    have hNotALS : ∀ lid', ¬ atLoopStart is e lid' := not_atLoopStart_of_not_atRegOp hImplStackEq hNotRO
    have hSfLt : sf.stmtIdx < sf.body.length := Nat.lt_of_not_le (fun h => by simp [List.getElem?_eq_none h] at hSpecStmt)
    have hImfLt : imf.stmtIdx < imf.body.length := Nat.lt_of_not_le (fun h => by simp [List.getElem?_eq_none h] at hImplStmt)
    have hNewFC : FrameCorr ab ⟨specThen, 0, .cond thenId⟩ ⟨implThenBody, 1, .cond thenId⟩ :=
      ⟨by simp [frameKindCorr], ⟨implThenInner, hThenMatch, rfl⟩,
       ⟨fun hRO => by simp [atRegOp] at hRO,
        fun _ => by simp⟩⟩
    have hOldSC := StackCorr.cons sf imf srest imrest hFC hRestCorr hCovS hCovI hNRO
    have hSimReconstructed : MatchStates spec impl ab SemaInv ss is :=
      { dataPathEq := hDataPath, inflightEq := hInflight, controlEq := hControl, semaInv := hSema,
        monotoneRegInv := hLoopRegInv, tripRegInv := hTripRegInv, regOpFold := hRegOpFold, pcCorr := hPC, waitRegChain := hWaitChain, gateRegChain := hGateChain }
    have hSMP_fwd := hSpecInv.wellFormedPC e; rw [hSpecStack] at hSMP_fwd
    have hUniqBody_fwd := smp_uniqueScopeIds hSMP_fwd hUniq sf (List.Mem.head _)
    have hSidNotChild : thenId ∉ directChildScopes specThen := by
      have h := uniqueScopeIds_of_getElem hSpecStmt hUniqBody_fwd
      cases h with | cond _ _ _ _ _ _ hTnTb _ _ _ _ _ _ _ _ _ _ => exact fun hC => hTnTb (directChildScopes_mem_scopeIdsOf _ _ hC)
    have hLoopBOf : scopeBodyOf spec.body thenId = some specThen := by
      have hLocal := scopeBodyOf_of_getElem_condTrue hSpecStmt hUniqBody_fwd
      exact smp_scopeBodyOf_agree hSMP_fwd hUniq sf (List.Mem.head _) thenId
        (mem_scopeIdsOf_of_getElem hSpecStmt (by simp [scopeIdsOf])) |>.symm ▸ hLocal
    have hDirectChild : ∀ lid', lid' ∈ directChildScopes specThen → lid' ≠ thenId → scopeParent spec.body lid' = some thenId := by
      intro lid' hChild hNeLid
      have hLidInSB := directChildScopes_mem_scopeIdsOf _ _ hChild
      have hUniqSB : UniqueScopeIds specThen := by
        have h := uniqueScopeIds_of_getElem hSpecStmt hUniqBody_fwd
        cases h with | cond _ _ _ _ _ _ _ _ _ _ _ _ _ _ hU _ _ => exact hU
      have hGoInner := directChild_scopeParent_go specThen lid' thenId hChild hUniqSB
      have hGoLocal := scopeParent_go_lift_cond_then (container := sf.kind.loopId?) hSpecStmt hUniqBody_fwd hGoInner hLidInSB
      have hMem := mem_scopeIdsOf_of_getElem hSpecStmt (by simp [scopeIdsOf]; right; right; left; exact hLidInSB)
      unfold scopeParent; exact smp_lift_scopeParent_go hSMP_fwd hUniq sf srest rfl hGoLocal hMem
    fwd_loop_enter_matchstates thenId (.cond thenId)

theorem case_condFalse (spec : Program) (impl : ImplProgram) (ab : AllocBase spec impl)
    (SemaInv : SpecState → ImplState → Prop)
    (hSemaInvMono : SemaInvMono SemaInv)
    (e : EngineId) (ss : SpecState) (is : ImplState)
    (hSim : MatchStates spec impl ab SemaInv ss is)
    (hNARO : NotAtRegOp is)
    (hEngines : e ∈ impl.engines)
    (hSpecInv : SpecInv spec ss) (hUniq : UniqueScopeIds spec.body)
    (sf : Frame) (srest : List Frame)
    (thenId elseId : ScopeId) (specThen specElse : List Stmt)
    (hSpecStack : (ss.pc e).stack = sf :: srest)
    (hSpecStmt : sf.body[sf.stmtIdx]? = some (Stmt.cond thenId elseId specThen specElse))
    (hSpecGuard : spec.guard e thenId (ss.controlState e) = false)
    (hParentInOuter : ∀ parent, scopeParent spec.body elseId = some parent →
        parent ∈ enclosingLoopsFromStack (sf :: srest))
    (hNotSelfParent : ∀ parent, scopeParent spec.body elseId = some parent → parent ≠ elseId)
    : let ss' := { ss with
        pc := funUpdate ss.pc e
          { stack := ⟨specElse, 0, .cond elseId⟩ :: sf :: srest, instrIdx := 0 }
        controlState := funUpdate ss.controlState e
          (spec.controlOp e elseId (ss.controlState e))
        scopeEntryHistory := incrScopeEntryHistory ss e elseId
          (enclosingLoopsFromStack (sf :: srest)) }
      ∃ is', ImplPlusAny impl is is' ∧ MatchStates spec impl ab SemaInv ss' is' ∧ NotAtRegOp is' := by
    obtain ⟨hDataPath, hInflight, hControl, hSema, hLoopRegInv, hTripRegInv, hRegOpFold, hPC, hWaitChain, hGateChain⟩ := hSim
    have hSC := (hPC e).stackCorr; rw [hSpecStack] at hSC
    obtain ⟨imf, imrest, hImplStackEq, hFC, hRestCorr, hCovS, hCovI, hNRO⟩ := stackCorr_spec_cons_inv hSC
    have hNotRO : ¬ atRegOp imf := hNARO e imf imrest hImplStackEq
    obtain ⟨implThenInner, implElseInner, hImplStmt, _, hElseMatch⟩ := frameCorr_spec_cond_stmt hFC hNotRO hSpecStmt
    have hGuardEq : spec.guard = impl.guard := congrArg ProgramBase.guard ab.baseEq
    have hControlOpEq : spec.controlOp = impl.controlOp := congrArg ProgramBase.controlOp ab.baseEq
    let implThenBody := [ImplStmt.regOp (fun e' => scopeEntryOps ab.monotoneReg ab.tripReg specThen e' thenId)] ++ implThenInner
    let implElseBody := [ImplStmt.regOp (fun e' => scopeEntryOps ab.monotoneReg ab.tripReg specElse e' elseId)] ++ implElseInner
    have step1 := ImplStep.condFalse e is hEngines imf imrest thenId elseId implThenBody implElseBody hImplStackEq hImplStmt
      (by rw [← hGuardEq, hControl]; exact hSpecGuard)
    let is₁ : ImplState := { is with
      pc := funUpdate is.pc e { stack := ⟨implElseBody, 0, .cond elseId⟩ :: imf :: imrest, instrIdx := 0, regOpIdx := 0, stmtRegOpIdx := 0 }
      controlState := funUpdate is.controlState e (impl.controlOp e elseId (is.controlState e)) }
    have hStack₁ : (is₁.pc e).stack = ⟨implElseBody, 0, .cond elseId⟩ :: imf :: imrest := by simp [is₁, funUpdate]
    have hStmt₁ : implElseBody[0]? = some (ImplStmt.regOp (fun e' => scopeEntryOps ab.monotoneReg ab.tripReg specElse e' elseId)) := by
      simp [implElseBody]
    have hIdx0₁ : (is₁.pc e).stmtRegOpIdx = 0 := by simp [is₁, funUpdate]
    obtain ⟨is₂_wit, step2_wit, hStack₂, hInstr₂, hRegOp₂, hSROI₂, hPC₂, hInfl₂, hSema₂, hDataPath₂, hControl₂, hRegs₂, hRegsE₂⟩ :=
      stmtRegOpSteps_to_done impl e is₁ hEngines ⟨implElseBody, 0, .cond elseId⟩ (imf :: imrest)
        (fun e' => scopeEntryOps ab.monotoneReg ab.tripReg specElse e' elseId) hStack₁ hStmt₁ hIdx0₁
    let is₂ : ImplState := { is₁ with
      pc := funUpdate is₁.pc e { stack := ⟨implElseBody, 1, .cond elseId⟩ :: imf :: imrest, instrIdx := (is₁.pc e).instrIdx, regOpIdx := 0, stmtRegOpIdx := 0 }
      registers := funUpdate is₁.registers e (foldRegOps (scopeEntryOps ab.monotoneReg ab.tripReg specElse e elseId) (is₁.registers e)) }
    have step2 : ImplStar impl e is₁ is₂ := by
      have hEq : is₂_wit = is₂ := by
        have hPCe : is₂_wit.pc e = is₂.pc e := by
          simp only [is₂, funUpdate, ite_true]
          have h1 := hStack₂; simp at h1
          exact ImplPC.ext h1 hInstr₂ (by simpa using hRegOp₂) (by simpa using hSROI₂)
        exact ImplState.ext hControl₂ hDataPath₂
          (funext fun e' => by
            by_cases he : e' = e
            · subst he; exact hPCe
            · simp only [is₂, funUpdate, if_neg he]; exact hPC₂ _ he)
          hInfl₂
          (funext fun e' => funext fun r => by
            by_cases he : e' = e
            · subst he; simp only [is₂, funUpdate, ite_true]; exact congrFun hRegsE₂ r
            · simp only [is₂, funUpdate, if_neg he]; exact congrFun (hRegs₂ _ he) r)
          hSema₂
      exact hEq ▸ step2_wit
    have hFullPlus : ImplPlusAny impl is is₂ := ImplPlusAny.step step1 (ImplStar_to_ImplStarAny step2)
    have hNotALS : ∀ lid', ¬ atLoopStart is e lid' := not_atLoopStart_of_not_atRegOp hImplStackEq hNotRO
    have hSfLt : sf.stmtIdx < sf.body.length := Nat.lt_of_not_le (fun h => by simp [List.getElem?_eq_none h] at hSpecStmt)
    have hImfLt : imf.stmtIdx < imf.body.length := Nat.lt_of_not_le (fun h => by simp [List.getElem?_eq_none h] at hImplStmt)
    have hNewFC : FrameCorr ab ⟨specElse, 0, .cond elseId⟩ ⟨implElseBody, 1, .cond elseId⟩ :=
      ⟨by simp [frameKindCorr], ⟨implElseInner, hElseMatch, rfl⟩,
       ⟨fun hRO => by simp [atRegOp] at hRO,
        fun _ => by simp⟩⟩
    have hOldSC := StackCorr.cons sf imf srest imrest hFC hRestCorr hCovS hCovI hNRO
    have hSimReconstructed : MatchStates spec impl ab SemaInv ss is :=
      { dataPathEq := hDataPath, inflightEq := hInflight, controlEq := hControl, semaInv := hSema,
        monotoneRegInv := hLoopRegInv, tripRegInv := hTripRegInv, regOpFold := hRegOpFold, pcCorr := hPC, waitRegChain := hWaitChain, gateRegChain := hGateChain }
    have hSMP_fwd := hSpecInv.wellFormedPC e; rw [hSpecStack] at hSMP_fwd
    have hUniqBody_fwd := smp_uniqueScopeIds hSMP_fwd hUniq sf (List.Mem.head _)
    have hSidNotChild : elseId ∉ directChildScopes specElse := by
      have h := uniqueScopeIds_of_getElem hSpecStmt hUniqBody_fwd
      cases h with | cond _ _ _ _ _ _ _ _ _ _ hEnEb _ _ _ _ _ _ => exact fun hC => hEnEb (directChildScopes_mem_scopeIdsOf _ _ hC)
    have hLoopBOf : scopeBodyOf spec.body elseId = some specElse := by
      have hLocal := scopeBodyOf_of_getElem_condFalse hSpecStmt hUniqBody_fwd
      have hElseInBody : elseId ∈ scopeIdsOf sf.body :=
        mem_scopeIdsOf_of_getElem hSpecStmt (by simp [scopeIdsOf])
      exact smp_scopeBodyOf_agree hSMP_fwd hUniq sf (List.Mem.head _) elseId hElseInBody |>.symm ▸ hLocal
    have hDirectChild : ∀ lid', lid' ∈ directChildScopes specElse → lid' ≠ elseId → scopeParent spec.body lid' = some elseId := by
      intro lid' hChild hNeLid
      have hLidInSB := directChildScopes_mem_scopeIdsOf _ _ hChild
      have hUniqSB : UniqueScopeIds specElse := by
        have h := uniqueScopeIds_of_getElem hSpecStmt hUniqBody_fwd
        cases h with | cond _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hU _ => exact hU
      have hGoInner := directChild_scopeParent_go specElse lid' elseId hChild hUniqSB
      have hGoLocal := scopeParent_go_lift_cond_else (container := sf.kind.loopId?) hSpecStmt hUniqBody_fwd hGoInner hLidInSB
      have hMem := mem_scopeIdsOf_of_getElem hSpecStmt (by simp [scopeIdsOf]; right; right; right; exact hLidInSB)
      unfold scopeParent; exact smp_lift_scopeParent_go hSMP_fwd hUniq sf srest rfl hGoLocal hMem
    fwd_loop_enter_matchstates elseId (.cond elseId)

theorem case_condDone (spec : Program) (impl : ImplProgram) (ab : AllocBase spec impl)
    (SemaInv : SpecState → ImplState → Prop)
    (hSemaInvMono : SemaInvMono SemaInv)
    (e : EngineId) (ss : SpecState) (is : ImplState)
    (hSim : MatchStates spec impl ab SemaInv ss is)
    (hNARO : NotAtRegOp is)
    (hEngines : e ∈ impl.engines)
    (sf sparent : Frame) (srest : List Frame) (sid : ScopeId)
    (hSpecStack : (ss.pc e).stack = sf :: sparent :: srest)
    (hSpecKind : sf.kind = .cond sid)
    (hSpecEnd : sf.stmtIdx = sf.body.length)
    : let ss' := { ss with
        pc := funUpdate ss.pc e
          { stack := ⟨sparent.body, sparent.stmtIdx + 1, sparent.kind⟩ :: srest, instrIdx := 0 } }
      ∃ is', ImplPlusAny impl is is' ∧ MatchStates spec impl ab SemaInv ss' is' ∧ NotAtRegOp is' := by
    obtain ⟨hDataPath, hInflight, hControl, hSema, hLoopRegInv, hTripRegInv, hRegOpFold, hPC, hWaitChain, hGateChain⟩ := hSim
    have hSC := (hPC e).stackCorr; rw [hSpecStack] at hSC
    obtain ⟨imf, imrest', hImplStackEq, hFC, hRestCorr', hCovS', hCovI', hNRO'⟩ := stackCorr_spec_cons_inv hSC
    obtain ⟨parent, imrest, hImrest', hPFC, hRestCorr, hCovS, hCovI, hNRO⟩ := stackCorr_spec_cons_inv hRestCorr'
    have hImplKind : imf.kind = .cond sid := by
      obtain ⟨hKC, _, _⟩ := hFC; revert hKC; rw [hSpecKind]; cases imf.kind <;> simp [frameKindCorr, eq_comm]
    have hNotRO : ¬ atRegOp imf := hNARO e imf imrest' hImplStackEq
    have hImplEnd : imf.stmtIdx = imf.body.length := by
      obtain ⟨_, ⟨ib, hBM, hBE⟩, hIC⟩ := hFC
      have hIC2 := hIC.2 hNotRO; rw [hImplKind] at hBE hIC2; simp at hBE hIC2
      rw [hBE]; simp; rw [← bodyMatch_length hBM, ← hSpecEnd]; omega
    have hNotROParent : ¬ atRegOp parent := hNRO' parent imrest hImrest'
    have step1 := ImplStep.condDone (impl := impl) e is hEngines imf parent imrest sid
      (by rw [hImplStackEq, hImrest']) hImplKind hImplEnd
    have hNewPFC : FrameCorr ab ⟨sparent.body, sparent.stmtIdx + 1, sparent.kind⟩ ⟨parent.body, parent.stmtIdx + 1, parent.kind⟩ := by
      obtain ⟨hPKC, ⟨pib, hPBM, hPBE⟩, hPIC⟩ := hPFC
      exact ⟨hPKC, ⟨pib, hPBM, hPBE⟩, ⟨fun hRO => by cases hk : parent.kind <;> simp [atRegOp, hk] at hRO,
        fun _ => by have hIdx := hPIC.2 hNotROParent; cases hk : parent.kind <;> (rw [hk] at hIdx; simp at hIdx; simp; omega)⟩⟩
    refine ⟨_, ImplPlusAny.step step1 ImplStarAny.refl, ?_, ?_⟩
    · exact MatchStates.of_funUpdate_pc ⟨hDataPath, hInflight, hControl, hSema, hLoopRegInv, hTripRegInv, hRegOpFold, hPC, hWaitChain, hGateChain⟩ hSemaInvMono _ _
              ⟨StackCorr.cons _ _ srest imrest hNewPFC hRestCorr hCovS hCovI hNRO, rfl⟩
              rfl (by
                intro e' lid; constructor
                · intro ⟨fr, r, hS, hK, hI⟩; by_cases he : e' = e
                  · subst he; simp only [funUpdate, ite_true] at hS
                    obtain ⟨rfl, rfl⟩ := List.cons.inj hS; simp at hI
                  · simp only [funUpdate, if_neg he] at hS; exact ⟨fr, r, hS, hK, hI⟩
                · intro ⟨fr, r, hS, hK, hI⟩; by_cases he : e' = e
                  · subst he; rw [hImplStackEq] at hS; obtain rfl := (List.cons.inj hS).1
                    exact absurd (by simp only [atRegOp]; rw [hImplKind]; exact hI) hNotRO
                  · exact ⟨fr, r, by simp only [funUpdate, if_neg he]; exact hS, hK, hI⟩)
              (fun _ _ _ hStack hStmt => by
                simp at hStack; obtain ⟨rfl, rfl⟩ := hStack
                exact frameCorr_no_regOp hPFC hNotROParent (Nat.le_succ _) hStmt)
    · intro e' fr r hS; by_cases he : e' = e
      · subst he; simp only [funUpdate, ite_true] at hS
        obtain ⟨rfl, rfl⟩ := List.cons.inj hS
        intro hRO; simp [atRegOp] at hRO; cases hk : parent.kind <;> simp [hk] at hRO
      · simp only [funUpdate, if_neg he] at hS; exact hNARO e' fr r hS

theorem case_issue (spec : Program) (impl : ImplProgram) (ab : AllocBase spec impl)
    (SemaInv : SpecState → ImplState → Prop)
    (hSemaInvMono : SemaInvMono SemaInv)
    (innerOps : EngineId → DataPathInstrId → List RegOp)
    (hInnerOpsWf : InnerRegOpsWf innerOps ab)
    (hRegOpsEq : ∀ e i, impl.regOps e i = wrapWithGate spec (ab.gateReg e) (ab.waitReg e) ab.tripReg e i (innerOps e i))
    (e : EngineId) (ss : SpecState) (is : ImplState)
    (hSim : MatchStates spec impl ab SemaInv ss is)
    (hInv : ImplInv impl is)
    (hNARO : NotAtRegOp is)
    (_hWf : Allocatable spec) (_hSpecInv : SpecInv spec ss)
    (_hUniq : UniqueScopeIds spec.body) (_hUniqueInstr : UniqueInstrIds spec.engines spec.body)
    (hEngines : e ∈ spec.engines)
    (sf : Frame) (srest : List Frame)
    (f : EngineId → List DataPathInstrId) (instr : DataPathInstrId)
    (hSpecStack : (ss.pc e).stack = sf :: srest)
    (hSpecStmt : sf.body[sf.stmtIdx]? = some (Stmt.block f))
    (hSpecInstr : (f e)[(ss.pc e).instrIdx]? = some instr)
    (hDeps : depSatisfied spec (spec.depGraph instr) instr ss e = true)
    (hForwardIssueSemaGe : ∀ (is : ImplState),
      SemaInv ss is →
      (∀ plid, is.registers e (ab.monotoneReg e plid) = totalEntries ss e plid) →
      (∀ lid, is.registers e (ab.tripReg e lid) = tripEntries ss e spec.body lid) →
      is.semaphores (impl.waitOf instr) ≥
        foldRegOps (impl.regOps e instr) (fun r => if r = ab.waitReg e then 0 else is.registers e r) (ab.waitReg e))
    : let ss' := { ss with
        pc := funUpdate ss.pc e
          { (ss.pc e) with instrIdx := (ss.pc e).instrIdx + 1 }
        inflight := funUpdate ss.inflight e
          (ss.inflight e ++ [(instr, Phase.issued)]) }
      ∃ is', ImplPlusAny impl is is' ∧ MatchStates spec impl ab SemaInv ss' is' ∧ NotAtRegOp is' := by
    have hImplEngines : e ∈ impl.engines := congrArg ProgramBase.engines ab.baseEq ▸ hEngines
    obtain ⟨hDataPath, hInflight, hControl, hSema, hLoopRegInv, hTripRegInv, hRegOpFold, hPC, hWaitChain, hGateChain⟩ := hSim
    have hSC := (hPC e).stackCorr; rw [hSpecStack] at hSC
    obtain ⟨imf, imrest, hImplStackEq, hFC, hRestCorr, hCovS, hCovI, hNRO⟩ := stackCorr_spec_cons_inv hSC
    have hNotRO : ¬ atRegOp imf := hNARO e imf imrest hImplStackEq
    have hImplStmt := frameCorr_spec_block_stmt hFC hNotRO hSpecStmt
    have hInstrEq := (hPC e).instrEq
    have hImplInstr : (f e)[(is.pc e).instrIdx]? = some instr := by rw [← hInstrEq]; exact hSpecInstr
    have hBound := hInv.regOpBound e imf imrest f instr hImplStackEq hImplStmt hImplInstr
    obtain ⟨is₁, hRegStar, hStack₁, hDataPathInstrIdx₁, hDone₁, hPC₁, hInfl₁, hSema₁, hDataPath₁, hControl₁, hRegs₁, hRegsE₁⟩ :=
      regOpSteps_to_done impl e is hImplEngines imf imrest f instr hImplStackEq hImplStmt hImplInstr hBound
    have hNotALS : ∀ lid, ¬ atLoopStart is e lid := not_atLoopStart_of_not_atRegOp hImplStackEq hNotRO
    have hLoopRegs : ∀ plid, is.registers e (ab.monotoneReg e plid) = totalEntries ss e plid :=
      fun plid => hLoopRegInv e plid (hNotALS plid)
    have hSemaInvIs₁ : SemaInv ss is₁ := hSemaInvMono ss ss is is₁ rfl hSema₁.symm hSema
    have hAllDstOr : ∀ op ∈ impl.regOps e instr, op.1 = ab.waitReg e ∨ op.1 = ab.gateReg e := by
      rw [hRegOpsEq]; intro op hMem
      exact wrapWithGate_dst (fun o hO => hInnerOpsWf.dstWaitReg e instr _ _ _ _ (List.mem_iff_getElem?.mp hO |>.choose_spec)) (List.mem_iff_getElem?.mp hMem |>.choose_spec)
    have hLoopRegsIs₁ : ∀ plid, is₁.registers e (ab.monotoneReg e plid) = totalEntries ss e plid := by
      intro plid; rw [hRegsE₁]
      rw [foldRegOps_other (fun op hMem => by
        intro hr; rcases hAllDstOr op (List.mem_of_mem_drop hMem) with h | h
        · exact (ab.noClob e plid) (h.symm ▸ hr)
        · exact (ab.noClob_gate_loop e plid) (h.symm ▸ hr))]
      exact hLoopRegs plid
    have hTripRegs : ∀ lid, is.registers e (ab.tripReg e lid) = tripEntries ss e spec.body lid :=
      fun lid => hTripRegInv e lid hNotALS
    have hTripRegsIs₁ : ∀ lid, is₁.registers e (ab.tripReg e lid) = tripEntries ss e spec.body lid := by
      intro lid; rw [hRegsE₁]
      rw [foldRegOps_other (fun op hMem => by
        intro hr; rcases hAllDstOr op (List.mem_of_mem_drop hMem) with h | h
        · exact (ab.noClob_trip_wait e lid) (hr ▸ h.symm)
        · exact (ab.noClob_gate_trip e lid) (hr ▸ h.symm))]
      exact hTripRegs lid
    have hIssueGe := hForwardIssueSemaGe is₁ hSemaInvIs₁ hLoopRegsIs₁ hTripRegsIs₁
    have hWaitGe : is₁.semaphores (impl.waitOf instr) ≥ is₁.registers e (impl.waitReg e instr) := by
      rw [ab.waitRegEq, hRegsE₁]
      -- Goal: is₁.sema ≥ foldRegOps(drop n ops)(is.regs e)(waitR)
      -- Apply hForwardIssueSemaGe to `is` (loop/trip regs correct in is)
      have hIssueGe' := hForwardIssueSemaGe is hSema hLoopRegs hTripRegs
      rw [← hSema₁] at hIssueGe'
      -- hIssueGe': is₁.sema ≥ foldRegOps ops base₀ waitR
      --   where base₀ r = if r = waitR then 0 else is.regs e r
      -- Need: foldRegOps ops base₀ waitR = foldRegOps(drop n ops)(is.regs e)(waitR)
      -- This follows from: foldRegOps(take n ops)(base₀) = is.regs e (pointwise)
      rcases Nat.eq_zero_or_pos (is.pc e).regOpIdx with h0 | hPos
      · rw [h0, List.drop_zero]
        have hEq : foldRegOps (impl.regOps e instr) (is.registers e) (ab.waitReg e) =
            foldRegOps (impl.regOps e instr) (fun r => if r = ab.waitReg e then 0 else is.registers e r) (ab.waitReg e) := by
          rw [hRegOpsEq]
          exact foldRegOps_wrapWithGate_waitR_init_irrelevant
            (fun r hr => by simp [hr])
            (ab.noClob_gate_wait e)
            (fun op hMem => hInnerOpsWf.dstWaitReg e instr _ _ _ _ (List.mem_iff_getElem?.mp hMem |>.choose_spec))
            (fun sid => Ne.symm (ab.noClob_trip_wait e sid))
            (hInnerOpsWf.firstSafe e instr)
            (hInnerOpsWf.nonEmpty e instr)
        rw [hEq]; exact hIssueGe'
      · -- n > 0: fold(take n)(base₀) = is.regs e pointwise, so fold(all)(base₀) = fold(drop n)(is.regs e)
        have hWC := hWaitChain e imf imrest f instr hImplStackEq hImplStmt hImplInstr hPos
        have hGC := hGateChain e imf imrest f instr hImplStackEq hImplStmt hImplInstr hPos
        have hFoldPw : ∀ r, foldRegOps ((impl.regOps e instr).take (is.pc e).regOpIdx)
            (fun r => if r = ab.waitReg e then 0 else is.registers e r) r = is.registers e r := by
          intro r
          by_cases hw : r = ab.waitReg e
          · rw [hw]; exact hWC.symm
          · by_cases hg : r = ab.gateReg e
            · rw [hg]; exact hGC.symm
            · rw [foldRegOps_other (fun op hMem => by
                have hMemFull := List.mem_of_mem_take hMem
                rw [hRegOpsEq] at hMemFull
                have ⟨idx, hGet⟩ := List.mem_iff_getElem?.mp hMemFull
                rcases wrapWithGate_dst (fun op hM => hInnerOpsWf.dstWaitReg e instr _ _ _ _ (List.mem_iff_getElem?.mp hM |>.choose_spec)) hGet with h | h
                · exact fun heq => hw (heq.symm.trans h)
                · exact fun heq => hg (heq.symm.trans h))]
              simp [hw]
        -- foldRegOps ops base₀ = foldRegOps (take n ++ drop n) base₀
        -- = foldRegOps (drop n) (foldRegOps (take n) base₀)
        -- = foldRegOps (drop n) (is.regs e)  [by hFoldPw]
        have hSplit := foldRegOps_append ((impl.regOps e instr).take (is.pc e).regOpIdx)
          ((impl.regOps e instr).drop (is.pc e).regOpIdx)
          (fun r => if r = ab.waitReg e then 0 else is.registers e r)
        rw [List.take_append_drop] at hSplit
        rw [show foldRegOps (impl.regOps e instr)
            (fun r => if r = ab.waitReg e then 0 else is.registers e r) =
          foldRegOps ((impl.regOps e instr).drop (is.pc e).regOpIdx)
            (foldRegOps ((impl.regOps e instr).take (is.pc e).regOpIdx)
              (fun r => if r = ab.waitReg e then 0 else is.registers e r)) from hSplit,
          foldRegOps_congr hFoldPw] at hIssueGe'
        exact hIssueGe'

    have hIssueStep := ImplStep.issue e is₁ hImplEngines imf imrest f instr
      (hStack₁ ▸ hImplStackEq ▸ rfl) hImplStmt (by rw [hDataPathInstrIdx₁]; exact hImplInstr) hDone₁ hWaitGe
    let is₂ := { is₁ with
      pc := funUpdate is₁.pc e { (is₁.pc e) with instrIdx := (is₁.pc e).instrIdx + 1, regOpIdx := 0 }
      inflight := funUpdate is₁.inflight e (is₁.inflight e ++ [(instr, Phase.issued)]) }
    refine ⟨is₂,
      (ImplStar_to_ImplStarAny hRegStar).trans_plus (ImplPlusAny.step hIssueStep ImplStarAny.refl), ?_, ?_⟩
    · exact { dataPathEq := by simp [is₂, hDataPath₁, hDataPath]
              inflightEq := by intro e'; simp only [is₂, funUpdate]; split <;> simp [hInfl₁, hInflight]
              controlEq := by intro e'; simp [is₂, hControl₁, hControl]
              semaInv := hSemaInvMono ss _ is _ rfl (by simp [is₂, hSema₁]) hSema
              monotoneRegInv := by
                intro e' lid hNALS_all; by_cases he : e' = e
                · subst he
                  simp only [is₂, totalEntries] at hNALS_all ⊢
                  rw [hRegsE₁, foldRegOps_other (fun op hMem => by
                    intro hr; rcases hAllDstOr op (List.mem_of_mem_drop hMem) with h | h
                    · exact (Ne.symm (ab.noClob e' lid)) (hr ▸ h)
                    · exact (Ne.symm (ab.noClob_gate_loop e' lid)) (hr ▸ h))]
                  exact hLoopRegInv e' lid (hNotALS lid)
                · simp only [is₂, totalEntries] at hNALS_all ⊢
                  rw [hRegs₁ e' he]
                  have hNALS' : ¬ atLoopStart is e' lid := by
                    intro ⟨fr, r, hS, hK, hI⟩; apply hNALS_all
                    exact ⟨fr, r, by simp [funUpdate, if_neg he]; rw [hPC₁ e' he]; exact hS, hK, hI⟩
                  exact hLoopRegInv e' lid hNALS'
              tripRegInv := by
                intro e' lid hNALS; by_cases he : e' = e
                · subst he
                  simp only [is₂, tripEntries] at hNALS ⊢
                  rw [hRegsE₁, foldRegOps_other (fun op hMem => by
                    intro hr; rcases hAllDstOr op (List.mem_of_mem_drop hMem) with h | h
                    · exact absurd (hr ▸ h) (Ne.symm (ab.noClob_trip_wait e' lid))
                    · exact absurd (hr ▸ h) (Ne.symm (ab.noClob_gate_trip e' lid)))]
                  exact hTripRegInv e' lid hNotALS
                · simp only [is₂, tripEntries] at hNALS ⊢
                  rw [hRegs₁ e' he]
                  have hOldNALS : ∀ lid', ¬ atLoopStart is e' lid' := by
                    intro lid' ⟨fr, r, hS, hK, hI⟩; apply hNALS lid'
                    exact ⟨fr, r, by simp [funUpdate, if_neg he]; rw [hPC₁ e' he]; exact hS, hK, hI⟩
                  exact hTripRegInv e' lid hOldNALS
              regOpFold := by
                intro e' frame' rest' ops' hStack' hStmt'
                simp only [is₂] at hStack' ⊢
                by_cases he : e' = e
                · subst he; simp only [funUpdate, ite_true] at hStack'
                  rw [hStack₁, hImplStackEq] at hStack'
                  obtain ⟨rfl, rfl⟩ := List.cons.inj hStack'
                  rw [hImplStmt] at hStmt'; simp at hStmt'
                · simp only [funUpdate, if_neg he] at hStack' ⊢
                  rw [show is₁.pc e' = is.pc e' from hPC₁ e' he] at hStack'
                  rw [hRegs₁ e' he, show is₁.pc e' = is.pc e' from hPC₁ e' he]
                  exact hRegOpFold e' frame' rest' ops' hStack' hStmt'
              pcCorr := by
                intro e'; by_cases he : e' = e
                · subst he; simp only [is₂, funUpdate, ite_true]
                  constructor
                  · rw [hStack₁, hImplStackEq]
                    rw [hImplStackEq] at hSC; simp only [hSpecStack]; exact hSC
                  · simp [hDataPathInstrIdx₁, hInstrEq]
                · simp only [is₂, funUpdate, if_neg he]
                  have : is₁.pc e' = is.pc e' := hPC₁ e' he
                  rw [this]; exact hPC e'
              waitRegChain := by
                intro e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
                simp only [is₂] at hStack' hStmt' hInstr' hROI ⊢
                by_cases he : e' = e
                · subst he; simp only [funUpdate, ite_true] at hROI; omega
                · simp only [funUpdate, if_neg he] at hStack' hInstr' hROI ⊢
                  rw [hRegs₁ e' he, show is₁.pc e' = is.pc e' from hPC₁ e' he]
                  rw [show is₁.pc e' = is.pc e' from hPC₁ e' he] at hStack' hInstr' hROI
                  exact hWaitChain e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
              gateRegChain := by
                intro e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
                simp only [is₂] at hStack' hStmt' hInstr' hROI ⊢
                by_cases he : e' = e
                · subst he; simp only [funUpdate, ite_true] at hROI; omega
                · simp only [funUpdate, if_neg he] at hStack' hInstr' hROI ⊢
                  rw [hRegs₁ e' he, show is₁.pc e' = is.pc e' from hPC₁ e' he]
                  rw [show is₁.pc e' = is.pc e' from hPC₁ e' he] at hStack' hInstr' hROI
                  exact hGateChain e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI }
    · intro e' fr r hS; simp only [is₂] at hS
      by_cases he : e' = e
      · subst he; simp only [funUpdate, ite_true] at hS
        rw [hStack₁, hImplStackEq] at hS; obtain ⟨rfl, rfl⟩ := List.cons.inj hS; exact hNotRO
      · simp only [funUpdate, if_neg he] at hS; rw [hPC₁ e' he] at hS; exact hNARO e' fr r hS

end ForwardSim

theorem forward_sim (spec : Program) (impl : ImplProgram) (ab : AllocBase spec impl)
    (SemaInv : SpecState → ImplState → Prop)
    (hForwardIssueSemaGe : ForwardIssueSemaGe spec impl ab SemaInv)
    (hRetireSema : ∀ (e' : EngineId) (instr : DataPathInstrId) (rest : List (DataPathInstrId × Phase))
      (ss0 : SpecState) (is0 : ImplState),
      SemaInv ss0 is0 →
      ss0.inflight e' = (instr, Phase.committed) :: rest →
      let ss1 := specRetireUpdate ss0 e' instr rest
      let is1 := { is0 with inflight := funUpdate is0.inflight e' rest,
                            semaphores := funUpdate is0.semaphores (impl.updateOf instr) (is0.semaphores (impl.updateOf instr) + 1) }
      SemaInv ss1 is1)
    (hSemaInvMono : SemaInvMono SemaInv)
    (innerOps : EngineId → DataPathInstrId → List RegOp)
    (hInnerOpsWf : InnerRegOpsWf innerOps ab)
    (hRegOpsEq : ∀ e i, impl.regOps e i = wrapWithGate spec (ab.gateReg e) (ab.waitReg e) ab.tripReg e i (innerOps e i))
    (e : EngineId) (ss ss' : SpecState) (is : ImplState)
    (hSim : MatchStates spec impl ab SemaInv ss is)
    (hInv : ImplInv impl is)
    (hNARO : NotAtRegOp is)
    (hWf : Allocatable spec) (hSpecInv : SpecInv spec ss)
    (hUniq : UniqueScopeIds spec.body) (hUniqueInstr : UniqueInstrIds spec.engines spec.body)
    (hEngines : e ∈ spec.engines)
    (hStep : SpecStep spec e ss ss')
    : ∃ is', ImplPlusAny impl is is' ∧ MatchStates spec impl ab SemaInv ss' is' ∧ NotAtRegOp is' := by
  have hImplEngines : e ∈ impl.engines := congrArg ProgramBase.engines ab.baseEq ▸ hEngines
  cases hStep with
  | commit _ idx instr hSpecIdx =>
    exact ForwardSim.case_commit spec impl ab SemaInv hSemaInvMono e ss is hSim hNARO hImplEngines idx instr hSpecIdx
  | retire _ instr inflightRest hSpecHead =>
    exact ForwardSim.case_retire spec impl ab SemaInv hRetireSema e ss is hSim hNARO hImplEngines instr inflightRest hSpecHead
  | blockDone _ sf srest f hSpecStack hSpecStmt hSpecDone =>
    exact ForwardSim.case_blockDone spec impl ab SemaInv hSemaInvMono e ss is hSim hNARO hImplEngines sf srest f hSpecStack hSpecStmt hSpecDone
  | loopEnter _ sf srest lid loopBody hSpecStack hSpecStmt hSpecGuard =>
    have hPIO : ∀ parent, scopeParent spec.body lid = some parent →
        parent ∈ enclosingLoopsFromStack (sf :: srest) := by
      intro parent hP
      have hSMP := hSpecInv.wellFormedPC e
      rw [hSpecStack] at hSMP
      have hUniqBody := smp_uniqueScopeIds hSMP hUniq sf (List.Mem.head _)
      have hMem : lid ∈ scopeIdsOf sf.body := mem_scopeIdsOf_of_getElem hSpecStmt (by simp [scopeIdsOf])
      cases hk : sf.kind with
      | top =>
        have hBodyEq : sf.body = spec.body := by
          cases hSMP with | base => rfl | loop => simp at hk | cond _ _ _ _ _ _ _ _ taken => cases taken <;> simp at hk
        have hGoEq : scopeParent.go sf.body lid none = none :=
          scopeParent_go_of_direct_loop (container := none) hSpecStmt hUniqBody
        rw [scopeParent] at hP; rw [hBodyEq] at hGoEq; rw [hGoEq] at hP; simp at hP
      | loop plid =>
        have hGoEq : scopeParent.go sf.body lid sf.kind.loopId? = some plid := by
          simp [hk]; exact scopeParent_go_of_direct_loop (container := some plid) hSpecStmt hUniqBody
        have hLift := smp_lift_scopeParent_go hSMP hUniq sf srest rfl hGoEq hMem
        rw [scopeParent] at hP; rw [hLift] at hP; simp at hP; subst hP
        simp [enclosingLoopsFromStack, hk]
      | cond cid =>
        have hGoEq : scopeParent.go sf.body lid sf.kind.loopId? = some cid := by
          simp [hk]; exact scopeParent_go_of_direct_loop (container := some cid) hSpecStmt hUniqBody
        have hLift := smp_lift_scopeParent_go hSMP hUniq sf srest rfl hGoEq hMem
        rw [scopeParent] at hP; rw [hLift] at hP; simp at hP; subst hP
        simp [enclosingLoopsFromStack, hk]
    have hNSP : ∀ parent, scopeParent spec.body lid = some parent → parent ≠ lid :=
      fun _ hP => scopeParent_ne_self hUniq hP
    exact ForwardSim.case_loopEnter spec impl ab SemaInv hSemaInvMono e ss is hSim hNARO hImplEngines hSpecInv hUniq sf srest lid loopBody hSpecStack hSpecStmt hSpecGuard hPIO hNSP
  | loopSkip _ sf srest lid loopBody hSpecStack hSpecStmt hSpecGuard =>
    exact ForwardSim.case_loopSkip spec impl ab SemaInv hSemaInvMono e ss is hSim hNARO hImplEngines sf srest lid loopBody hSpecStack hSpecStmt hSpecGuard
  | loopBack _ sf sparent srest lid hSpecStack hSpecKind hSpecEnd =>
    exact ForwardSim.case_loopBack spec impl ab SemaInv hSemaInvMono e ss is hSim hNARO hImplEngines sf sparent srest lid hSpecStack hSpecKind hSpecEnd
  | condTrue _ sf srest thenId elseId specThen specElse hSpecStack hSpecStmt hSpecGuard =>
    have hPIO : ∀ parent, scopeParent spec.body thenId = some parent →
        parent ∈ enclosingLoopsFromStack (sf :: srest) := by
      intro parent hP
      have hSMP := hSpecInv.wellFormedPC e
      rw [hSpecStack] at hSMP
      have hUniqBody := smp_uniqueScopeIds hSMP hUniq sf (List.Mem.head _)
      have hMem : thenId ∈ scopeIdsOf sf.body := mem_scopeIdsOf_of_getElem hSpecStmt (by simp [scopeIdsOf])
      cases hk : sf.kind with
      | top =>
        have hBodyEq : sf.body = spec.body := by
          cases hSMP with | base => rfl | loop => simp at hk | cond _ _ _ _ _ _ _ _ taken => cases taken <;> simp at hk
        have hGoEq : scopeParent.go sf.body thenId none = none :=
          scopeParent_go_of_direct_cond_then (container := none) hSpecStmt hUniqBody
        rw [scopeParent] at hP; rw [hBodyEq] at hGoEq; rw [hGoEq] at hP; simp at hP
      | loop plid =>
        have hGoEq : scopeParent.go sf.body thenId sf.kind.loopId? = some plid := by
          simp [hk]; exact scopeParent_go_of_direct_cond_then (container := some plid) hSpecStmt hUniqBody
        have hLift := smp_lift_scopeParent_go hSMP hUniq sf srest rfl hGoEq hMem
        rw [scopeParent] at hP; rw [hLift] at hP; simp at hP; subst hP
        simp [enclosingLoopsFromStack, hk]
      | cond cid =>
        have hGoEq : scopeParent.go sf.body thenId sf.kind.loopId? = some cid := by
          simp [hk]; exact scopeParent_go_of_direct_cond_then (container := some cid) hSpecStmt hUniqBody
        have hLift := smp_lift_scopeParent_go hSMP hUniq sf srest rfl hGoEq hMem
        rw [scopeParent] at hP; rw [hLift] at hP; simp at hP; subst hP
        simp [enclosingLoopsFromStack, hk]
    have hNSP : ∀ parent, scopeParent spec.body thenId = some parent → parent ≠ thenId :=
      fun _ hP => scopeParent_ne_self hUniq hP
    exact ForwardSim.case_condTrue spec impl ab SemaInv hSemaInvMono e ss is hSim hNARO hImplEngines hSpecInv hUniq sf srest thenId elseId specThen specElse hSpecStack hSpecStmt hSpecGuard hPIO hNSP
  | condFalse _ sf srest thenId elseId specThen specElse hSpecStack hSpecStmt hSpecGuard =>
    have hPIO : ∀ parent, scopeParent spec.body elseId = some parent →
        parent ∈ enclosingLoopsFromStack (sf :: srest) := by
      intro parent hP
      have hSMP := hSpecInv.wellFormedPC e
      rw [hSpecStack] at hSMP
      have hUniqBody := smp_uniqueScopeIds hSMP hUniq sf (List.Mem.head _)
      have hMem : elseId ∈ scopeIdsOf sf.body := mem_scopeIdsOf_of_getElem hSpecStmt (by simp [scopeIdsOf])
      cases hk : sf.kind with
      | top =>
        have hBodyEq : sf.body = spec.body := by
          cases hSMP with | base => rfl | loop => simp at hk | cond _ _ _ _ _ _ _ _ taken => cases taken <;> simp at hk
        have hGoEq : scopeParent.go sf.body elseId none = none :=
          scopeParent_go_of_direct_cond_else (container := none) hSpecStmt hUniqBody
        rw [scopeParent] at hP; rw [hBodyEq] at hGoEq; rw [hGoEq] at hP; simp at hP
      | loop plid =>
        have hGoEq : scopeParent.go sf.body elseId sf.kind.loopId? = some plid := by
          simp [hk]; exact scopeParent_go_of_direct_cond_else (container := some plid) hSpecStmt hUniqBody
        have hLift := smp_lift_scopeParent_go hSMP hUniq sf srest rfl hGoEq hMem
        rw [scopeParent] at hP; rw [hLift] at hP; simp at hP; subst hP
        simp [enclosingLoopsFromStack, hk]
      | cond cid =>
        have hGoEq : scopeParent.go sf.body elseId sf.kind.loopId? = some cid := by
          simp [hk]; exact scopeParent_go_of_direct_cond_else (container := some cid) hSpecStmt hUniqBody
        have hLift := smp_lift_scopeParent_go hSMP hUniq sf srest rfl hGoEq hMem
        rw [scopeParent] at hP; rw [hLift] at hP; simp at hP; subst hP
        simp [enclosingLoopsFromStack, hk]
    have hNSP : ∀ parent, scopeParent spec.body elseId = some parent → parent ≠ elseId :=
      fun _ hP => scopeParent_ne_self hUniq hP
    exact ForwardSim.case_condFalse spec impl ab SemaInv hSemaInvMono e ss is hSim hNARO hImplEngines hSpecInv hUniq sf srest thenId elseId specThen specElse hSpecStack hSpecStmt hSpecGuard hPIO hNSP
  | condDone _ sf sparent srest sid hSpecStack hSpecKind hSpecEnd =>
    exact ForwardSim.case_condDone spec impl ab SemaInv hSemaInvMono e ss is hSim hNARO hImplEngines sf sparent srest sid hSpecStack hSpecKind hSpecEnd
  | issue _ sf srest f instr hSpecStack hSpecStmt hSpecInstr hDeps =>
    exact ForwardSim.case_issue spec impl ab SemaInv hSemaInvMono innerOps hInnerOpsWf hRegOpsEq e ss is hSim hInv hNARO hWf hSpecInv hUniq hUniqueInstr hEngines sf srest f instr hSpecStack hSpecStmt hSpecInstr hDeps
      (fun is' hSI hSR hRR => hForwardIssueSemaGe e instr ss is' hSI hDeps (allocatableAt_of_block_instr spec ss e instr hWf hSpecInv hUniq hUniqueInstr hEngines sf srest f hSpecStack hSpecStmt hSpecInstr) hSpecInv hSR hRR)

theorem forward_sim_star (spec : Program) (impl : ImplProgram) (ab : AllocBase spec impl)
    (SemaInv : SpecState → ImplState → Prop)
    (hForwardIssueSemaGe : ForwardIssueSemaGe spec impl ab SemaInv)
    (hRetireSema : ∀ (e' : EngineId) (instr : DataPathInstrId) (rest : List (DataPathInstrId × Phase))
      (ss0 : SpecState) (is0 : ImplState),
      SemaInv ss0 is0 →
      ss0.inflight e' = (instr, Phase.committed) :: rest →
      let ss1 := specRetireUpdate ss0 e' instr rest
      let is1 := { is0 with inflight := funUpdate is0.inflight e' rest,
                            semaphores := funUpdate is0.semaphores (impl.updateOf instr) (is0.semaphores (impl.updateOf instr) + 1) }
      SemaInv ss1 is1)
    (hSemaInvMono : SemaInvMono SemaInv)
    (innerOps : EngineId → DataPathInstrId → List RegOp)
    (hInnerOpsWf : InnerRegOpsWf innerOps ab)
    (hRegOpsEq : ∀ e i, impl.regOps e i = wrapWithGate spec (ab.gateReg e) (ab.waitReg e) ab.tripReg e i (innerOps e i))
    (ss ss' : SpecState) (is : ImplState)
    (hSim : MatchStates spec impl ab SemaInv ss is)
    (hInv : ImplInv impl is)
    (hNARO : NotAtRegOp is)
    (hWf : Allocatable spec) (hSpecInv : SpecInv spec ss)
    (hUniq : UniqueScopeIds spec.body) (hUniqueInstr : UniqueInstrIds spec.engines spec.body)
    (hSteps : SpecStar spec ss ss')
    : ∃ is', ImplStarAny impl is is' ∧ MatchStates spec impl ab SemaInv ss' is' := by
  induction hSteps generalizing is with
  | refl => exact ⟨is, ImplStarAny.refl, hSim⟩
  | @step s s_mid s_final hStep hStar ih =>
    obtain ⟨e, hStep⟩ := hStep
    have hSpecInvMid := specInv_step spec e s s_mid hUniq hSpecInv hStep
    obtain ⟨is₁, hImplStar, hSim₁, hNARO₁⟩ := forward_sim spec impl ab SemaInv
      hForwardIssueSemaGe hRetireSema hSemaInvMono innerOps hInnerOpsWf hRegOpsEq e _ _ is hSim hInv hNARO
      hWf hSpecInv hUniq hUniqueInstr hStep.mem_engines hStep
    have hInv₁ := implInv_starAny impl is is₁ hInv hImplStar.to_star
    obtain ⟨is₂, hImplStar₂, hSim₂⟩ := ih is₁ hSim₁ hInv₁ hNARO₁ hSpecInvMid
    exact ⟨is₂, (hImplStar.to_star).trans hImplStar₂, hSim₂⟩

theorem perInstr_forward_issue_sema_ge (spec : Program) (impl : ImplProgram) (alloc : PerInstrAllocR spec impl)
    (e : EngineId) (instr : DataPathInstrId) (ss : SpecState) (is : ImplState)
    (hSema : perInstrSemaInv alloc ss is)
    (hDeps : depSatisfied spec (spec.depGraph instr) instr ss e = true)
    (hWf : AllocatableAt spec ss e instr)
    (_ : SpecInv spec ss)
    (hLoopRegs : ∀ plid, is.registers e (alloc.monotoneReg e plid) = totalEntries ss e plid)
    (hTripRegs : ∀ lid, is.registers e (alloc.tripReg e lid) = tripEntries ss e spec.body lid)
    : is.semaphores (impl.waitOf instr) ≥
        foldRegOps (impl.regOps e instr) (fun r => if r = alloc.waitReg e then 0 else is.registers e r) (alloc.waitReg e) := by
  rw [alloc.regOpsEq]
  let baseRegs := fun r => if r = alloc.waitReg e then 0 else is.registers e r
  have hInnerDst : ∀ op ∈ perInstrExpectedRegOps spec (alloc.waitReg e) alloc.monotoneReg e instr,
      op.1 = alloc.waitReg e := by
    intro ⟨d, s, tr⟩ hMem
    obtain ⟨idx, hGet⟩ := List.mem_iff_getElem?.mp hMem
    exact perInstr_innerRegOpsDstWaitReg spec impl alloc e instr idx d s tr hGet
  have hDecomp := foldRegOps_wrapWithGate_waitReg (spec := spec) (consumer := instr) (e := e)
    (alloc.noClob_gate_wait e) hInnerDst
    (perInstr_innerRegOpsSrcNeGate spec impl alloc e instr)
    (fun sid => Ne.symm (alloc.noClob_trip_wait e sid))
    (perInstr_innerRegOpsFirstSafe spec impl alloc e instr)
    (perInstrExpectedRegOps_nonEmpty spec (alloc.waitReg e) alloc.monotoneReg e instr)
    (regs := baseRegs)
  have hBaseLoop : ∀ plid, baseRegs (alloc.monotoneReg e plid) = totalEntries ss e plid := by
    intro plid; simp only [baseRegs]; rw [if_neg (Ne.symm (alloc.noClob e plid))]; exact hLoopRegs plid
  have hInnerEq := foldRegOps_perInstrExpectedRegOps_waitReg (ab := alloc.toAllocBase)
    (spec := spec) (ss := ss) (e := e) (instr := instr) baseRegs hBaseLoop
  simp only at hDecomp
  match hDep : spec.depGraph instr with
  | .none =>
    simp only [hDep] at hDecomp; rw [hDecomp, hInnerEq]; simp [expectedWaitVal, hDep]
  | .dep producer offset =>
    simp only [hDep] at hDecomp
    match hSS : innermostSharedScope spec.engines spec.body producer instr with
    | some sid =>
      simp only [hSS] at hDecomp
      have hBaseRes : baseRegs (alloc.tripReg e sid) = tripEntries ss e spec.body sid := by
        simp only [baseRegs]; rw [if_neg (Ne.symm (alloc.noClob_trip_wait e sid))]
        exact hTripRegs sid
      rw [hBaseRes] at hDecomp
      by_cases hVac : tripEntries ss e spec.body sid ≤ offset
      · -- gate = 0: result is 0
        simp only [show ¬(tripEntries ss e spec.body sid > offset) from by omega, ite_false, Nat.zero_mul] at hDecomp
        rw [hDecomp]; exact Nat.zero_le _
      · -- gate = 1: result = expectedWaitVal
        simp only [show tripEntries ss e spec.body sid > offset from by omega, ite_true, Nat.one_mul] at hDecomp
        rw [hDecomp, hInnerEq]
        exact mainCheck_implies_sema_ge spec alloc ss is e instr hSema
          (fun i => alloc.waitOfEq i) hWf (by
            simp only [depSatisfied, hDep, hSS] at hDeps
            simp only [hDep]
            match hPL : innermostParentScope spec.engines spec.body producer with
            | none => exact absurd hPL (by obtain ⟨_, h⟩ := innermostParentScope_of_sharedLoop hSS; simp [h])
            | some plid =>
              simp only [hPL, Bool.or_eq_true, decide_eq_true_eq] at hDeps
              simp only [hSS]
              rcases hDeps with hVacD | hRC
              · exact absurd hVacD hVac
              · exact hRC)
    | none =>
      simp only [hSS] at hDecomp; rw [hDecomp, hInnerEq]
      exact mainCheck_implies_sema_ge spec alloc ss is e instr hSema
        (fun i => alloc.waitOfEq i) hWf (by
          simp only [depSatisfied, hDep, hSS] at hDeps
          simp only [hDep]
          match hPL : innermostParentScope spec.engines spec.body producer with
          | none =>
            simp only [hPL, hSS, totalEntriesOpt, Bool.or_eq_true,
              decide_eq_true_eq] at hDeps ⊢
            rcases hDeps with hVac | hMain
            · omega
            · exact hMain
          | some plid =>
            simp only [hPL, Bool.or_eq_true, decide_eq_true_eq] at hDeps
            simp only [hSS]
            rcases hDeps with hVacD | hRC
            · -- vacuous: 1 ≤ offset, so totalEntriesOpt none - offset = 0, cumExecs ... 0 = 0
              simp only [totalEntriesOpt]
              have : 1 - offset = 0 := by omega
              rw [this]; simp [cumExecs]
            · exact hRC)

-- Convenience: forward simulation specialized to per-instruction allocation
theorem perInstr_forward_sim (spec : Program) (impl : ImplProgram) (alloc : PerInstrAllocR spec impl)
    (e : EngineId) (ss ss' : SpecState) (is : ImplState)
    (hSim : MatchStates spec impl alloc.toAllocBase (perInstrSemaInv alloc) ss is)
    (hInv : ImplInv impl is)
    (hNARO : NotAtRegOp is)
    (hWf : Allocatable spec) (hSpecInv : SpecInv spec ss)
    (hUniq : UniqueScopeIds spec.body) (hUniqueInstr : UniqueInstrIds spec.engines spec.body)
    (hEngines : e ∈ spec.engines)
    (hStep : SpecStep spec e ss ss')
    : ∃ is', ImplStarAny impl is is' ∧ MatchStates spec impl alloc.toAllocBase (perInstrSemaInv alloc) ss' is' ∧ NotAtRegOp is' := by
  obtain ⟨is', hPlus, hSim', hNARO'⟩ := forward_sim spec impl alloc.toAllocBase (perInstrSemaInv alloc)
    (perInstr_forward_issue_sema_ge spec impl alloc) (perInstr_retire_semaInv spec impl alloc)
    (perInstr_semaInv_mono spec impl alloc)
    (fun e i => perInstrExpectedRegOps spec (alloc.waitReg e) alloc.monotoneReg e i)
    ⟨perInstr_innerRegOpsFirstSafe spec impl alloc,
     fun e i => perInstrExpectedRegOps_nonEmpty spec (alloc.waitReg e) alloc.monotoneReg e i,
     perInstr_innerRegOpsDstWaitReg spec impl alloc⟩
    alloc.regOpsEq
    e ss ss' is hSim hInv hNARO hWf hSpecInv hUniq hUniqueInstr hEngines hStep
  exact ⟨is', hPlus.to_star, hSim', hNARO'⟩

-- Convenience: forward simulation star specialized to per-instruction allocation
theorem perInstr_forward_sim_star (spec : Program) (impl : ImplProgram) (alloc : PerInstrAllocR spec impl)
    (ss ss' : SpecState) (is : ImplState)
    (hSim : MatchStates spec impl alloc.toAllocBase (perInstrSemaInv alloc) ss is)
    (hInv : ImplInv impl is)
    (hNARO : NotAtRegOp is)
    (hWf : Allocatable spec) (hSpecInv : SpecInv spec ss)
    (hUniq : UniqueScopeIds spec.body) (hUniqueInstr : UniqueInstrIds spec.engines spec.body)
    (hSteps : SpecStar spec ss ss')
    : ∃ is', ImplStarAny impl is is' ∧ MatchStates spec impl alloc.toAllocBase (perInstrSemaInv alloc) ss' is' :=
  forward_sim_star spec impl alloc.toAllocBase (perInstrSemaInv alloc)
    (perInstr_forward_issue_sema_ge spec impl alloc) (perInstr_retire_semaInv spec impl alloc)
    (perInstr_semaInv_mono spec impl alloc)
    (fun e i => perInstrExpectedRegOps spec (alloc.waitReg e) alloc.monotoneReg e i)
    ⟨perInstr_innerRegOpsFirstSafe spec impl alloc,
     fun e i => perInstrExpectedRegOps_nonEmpty spec (alloc.waitReg e) alloc.monotoneReg e i,
     perInstr_innerRegOpsDstWaitReg spec impl alloc⟩
    alloc.regOpsEq
    ss ss' is hSim hInv hNARO hWf hSpecInv hUniq hUniqueInstr hSteps
