import SemaAlloc.MatchStates
import Aesop

-- shared MatchStates block for backward loop-enter cases (loopEnter, condTrue, condFalse).
-- Expects in loop: hSim, hSemaInvMono, ss, is, e, frame, rest, hStack, hNotRO, sf, srest,
-- hSpecStack, hFrameCorr, hRestCorr, hCovS, hCovI, hNoRegOp, hSpecStmt, hStmt,
-- hParentInOuter, hNotSelfParent (for tripRegInv_loop_entry).
set_option hygiene false in
macro "bwd_loop_enter_matchstates_loop " implBody:ident specBody:ident sid:ident
    implInner:ident hMatch:ident hBodyEq:ident : tactic => `(tactic|
  (have hControlOpEq : spec.controlOp = impl.controlOp := congrArg ProgramBase.controlOp ab.baseEq
   have hOldNotALS : ∀ lid', ¬ atLoopStart is e lid' := not_atLoopStart_of_not_atRegOp hStack hNotRO
   exact { dataPathEq := hSim.dataPathEq, inflightEq := hSim.inflightEq
           controlEq := by
             intro e'; simp only [funUpdate]; split
             · rw [hControlOpEq, ← hSim.controlEq]
             · exact hSim.controlEq e'
           semaInv := hSemaInvMono ss _ is _ rfl rfl hSim.semaInv
           monotoneRegInv := monotoneRegInv_loop_entry hSim hOldNotALS $implBody (.loop $sid) frame rest hStack (Or.inl rfl) _
           tripRegInv := tripRegInv_loop_entry hSim hOldNotALS $implBody (.loop $sid) frame rest hStack (Or.inl rfl) (enclosingLoopsFromStack (sf :: srest)) hParentInOuter hNotSelfParent
           pcCorr := by
             intro e'; by_cases he : e' = e
             · subst he; simp only [funUpdate, ite_true]
               have hNewFC : FrameCorr ab ⟨$specBody, 0, .loop $sid⟩ ⟨$implBody, 0, .loop $sid⟩ :=
                 ⟨by simp [frameKindCorr], ⟨$implInner, $hMatch, by simp [$hBodyEq:ident]⟩,
                  ⟨fun _ => ⟨rfl, rfl⟩, fun h => by simp [atRegOp] at h⟩⟩
               have hSC := StackCorr.cons sf frame srest rest hFrameCorr hRestCorr hCovS hCovI hNoRegOp
               have hSfLt : sf.stmtIdx < sf.body.length :=
                 Nat.lt_of_not_le (fun hle => by simp [List.getElem?_eq_none hle] at hSpecStmt)
               have hFrameLt : frame.stmtIdx < frame.body.length :=
                 Nat.lt_of_not_le (fun hle => by simp [List.getElem?_eq_none hle] at hStmt)
               refine ⟨StackCorr.cons _ _ (sf :: srest) (frame :: rest) hNewFC hSC ?_ ?_ ?_, rfl⟩
               · intro _ _ h; simp at h; obtain ⟨rfl, rfl⟩ := h; exact hSfLt
               · intro _ _ h; simp at h; obtain ⟨rfl, rfl⟩ := h; exact hFrameLt
               · intro _ _ h; simp at h; obtain ⟨rfl, rfl⟩ := h; exact hNotRO
             · simp only [funUpdate, if_neg he]; exact hSim.pcCorr e'
           regOpFold := by
             intro e' frame' rest' ops' hStack' hStmt'
             by_cases he : e' = e
             · subst he; simp only [funUpdate, ite_true] at hStack' hStmt' ⊢
               obtain ⟨rfl, rfl⟩ := List.cons.inj hStack'
               simp only [List.drop_zero]
               have hOpsEq : ops' = fun e' => scopeEntryOps ab.monotoneReg ab.tripReg $specBody e' $sid := by
                 rw [$hBodyEq:ident] at hStmt'; simp at hStmt'; exact hStmt'.symm
               rw [hOpsEq]
               constructor
               · intro lid'
                 rw [foldRegOps_scopeEntryOps_monotoneReg_bwd (ab.monotoneRegInj _) (fun l1 l2 => ab.noClob_trip_loop _ l1 l2)]
                 by_cases hEq : lid' = $sid
                 · rw [if_pos hEq, hEq, hSim.monotoneRegInv e' $sid (hOldNotALS $sid)]
                   exact incrScopeEntryHistory_totalEntries.symm
                 · rw [if_neg hEq, hSim.monotoneRegInv e' lid' (hOldNotALS lid')]
                   simp [totalEntries, incrScopeEntryHistory_ne_sid hEq]
               · -- tripReg fold at loop entry (uses hSidNotChild, hLoopBOf, hDirectChild from call site)
                 exact regOpFold_tripReg_loop_entry hSim hOldNotALS hSidNotChild hSpecInv hUniq hLoopBOf hDirectChild _ hParentInOuter hNotSelfParent
             · simp only [funUpdate, if_neg he] at hStack' ⊢
               have ⟨h1, h2⟩ := hSim.regOpFold e' frame' rest' ops' hStack' hStmt'
               exact ⟨fun lid => by simp [totalEntries, incrScopeEntryHistory_ne_engine he]; exact h1 lid,
                      fun lid => by simp [tripEntries, scopeParent, totalEntries, incrScopeEntryHistory_ne_engine he]; exact h2 lid⟩
           waitRegChain := by
             intro e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
             by_cases he : e' = e <;> simp_all
             exact hSim.waitRegChain e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
           gateRegChain := by
             intro e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
             by_cases he : e' = e <;> simp_all
             exact hSim.gateRegChain e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI }))

set_option hygiene false in
macro "bwd_loop_enter_matchstates_cond " implBody:ident specBody:ident sid:ident
    implInner:ident hMatch:ident hBodyEq:ident : tactic => `(tactic|
  (have hControlOpEq : spec.controlOp = impl.controlOp := congrArg ProgramBase.controlOp ab.baseEq
   have hOldNotALS : ∀ lid', ¬ atLoopStart is e lid' := not_atLoopStart_of_not_atRegOp hStack hNotRO
   exact { dataPathEq := hSim.dataPathEq, inflightEq := hSim.inflightEq
           controlEq := by
             intro e'; simp only [funUpdate]; split
             · rw [hControlOpEq, ← hSim.controlEq]
             · exact hSim.controlEq e'
           semaInv := hSemaInvMono ss _ is _ rfl rfl hSim.semaInv
           monotoneRegInv := monotoneRegInv_loop_entry hSim hOldNotALS $implBody (.cond $sid) frame rest hStack (Or.inr rfl) _
           tripRegInv := tripRegInv_loop_entry hSim hOldNotALS $implBody (.cond $sid) frame rest hStack (Or.inr rfl) (enclosingLoopsFromStack (sf :: srest)) hParentInOuter hNotSelfParent
           pcCorr := by
             intro e'; by_cases he : e' = e
             · subst he; simp only [funUpdate, ite_true]
               have hNewFC : FrameCorr ab ⟨$specBody, 0, .cond $sid⟩ ⟨$implBody, 0, .cond $sid⟩ :=
                 ⟨by simp [frameKindCorr], ⟨$implInner, $hMatch, by simp [$hBodyEq:ident]⟩,
                  ⟨fun _ => ⟨rfl, rfl⟩, fun h => by simp [atRegOp] at h⟩⟩
               have hSC := StackCorr.cons sf frame srest rest hFrameCorr hRestCorr hCovS hCovI hNoRegOp
               have hSfLt : sf.stmtIdx < sf.body.length :=
                 Nat.lt_of_not_le (fun hle => by simp [List.getElem?_eq_none hle] at hSpecStmt)
               have hFrameLt : frame.stmtIdx < frame.body.length :=
                 Nat.lt_of_not_le (fun hle => by simp [List.getElem?_eq_none hle] at hStmt)
               refine ⟨StackCorr.cons _ _ (sf :: srest) (frame :: rest) hNewFC hSC ?_ ?_ ?_, rfl⟩
               · intro _ _ h; simp at h; obtain ⟨rfl, rfl⟩ := h; exact hSfLt
               · intro _ _ h; simp at h; obtain ⟨rfl, rfl⟩ := h; exact hFrameLt
               · intro _ _ h; simp at h; obtain ⟨rfl, rfl⟩ := h; exact hNotRO
             · simp only [funUpdate, if_neg he]; exact hSim.pcCorr e'
           regOpFold := by
             intro e' frame' rest' ops' hStack' hStmt'
             by_cases he : e' = e
             · subst he; simp only [funUpdate, ite_true] at hStack' hStmt' ⊢
               obtain ⟨rfl, rfl⟩ := List.cons.inj hStack'
               simp only [List.drop_zero]
               have hOpsEq : ops' = fun e' => scopeEntryOps ab.monotoneReg ab.tripReg $specBody e' $sid := by
                 rw [$hBodyEq:ident] at hStmt'; simp at hStmt'; exact hStmt'.symm
               rw [hOpsEq]
               constructor
               · intro lid'
                 rw [foldRegOps_scopeEntryOps_monotoneReg_bwd (ab.monotoneRegInj _) (fun l1 l2 => ab.noClob_trip_loop _ l1 l2)]
                 by_cases hEq : lid' = $sid
                 · rw [if_pos hEq, hEq, hSim.monotoneRegInv e' $sid (hOldNotALS $sid)]
                   exact incrScopeEntryHistory_totalEntries.symm
                 · rw [if_neg hEq, hSim.monotoneRegInv e' lid' (hOldNotALS lid')]
                   simp [totalEntries, incrScopeEntryHistory_ne_sid hEq]
               · -- tripReg fold at loop entry (uses hSidNotChild, hLoopBOf, hDirectChild from call site)
                 exact regOpFold_tripReg_loop_entry hSim hOldNotALS hSidNotChild hSpecInv hUniq hLoopBOf hDirectChild _ hParentInOuter hNotSelfParent
             · simp only [funUpdate, if_neg he] at hStack' ⊢
               have ⟨h1, h2⟩ := hSim.regOpFold e' frame' rest' ops' hStack' hStmt'
               exact ⟨fun lid => by simp [totalEntries, incrScopeEntryHistory_ne_engine he]; exact h1 lid,
                      fun lid => by simp [tripEntries, scopeParent, totalEntries, incrScopeEntryHistory_ne_engine he]; exact h2 lid⟩
           waitRegChain := by
             intro e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
             by_cases he : e' = e <;> simp_all
             exact hSim.waitRegChain e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
           gateRegChain := by
             intro e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
             by_cases he : e' = e <;> simp_all
             exact hSim.gateRegChain e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI }))

/-! ### Loop parent membership in enclosing loops -/

-- scopeParent ∈ enclosingLoopsFromStack is proved separately for loop, cond-then, cond-else below.

/-- Overload for loop case -/
theorem scopeParent_in_enclosingLoops_loop
    {spec : Program} {impl : ImplProgram} {ab : AllocBase spec impl}
    {SemaInv : SpecState → ImplState → Prop}
    {ss : SpecState} {is : ImplState} {e : EngineId}
    (hSim : MatchStates spec impl ab SemaInv ss is) (hSpecInv : SpecInv spec ss)
    (hUniq : UniqueScopeIds spec.body) (_hEngines : e ∈ spec.engines)
    {frame : ImplFrame} {rest : List ImplFrame}
    (hStack : (is.pc e).stack = frame :: rest)
    {sid : ScopeId} {loopBody : List ImplStmt}
    (hStmt : frame.body[frame.stmtIdx]? = some (.loop sid loopBody))
    : ∀ parent, scopeParent spec.body sid = some parent →
      parent ∈ enclosingLoopsFromStack (ss.pc e).stack := by
  obtain ⟨sf, srest, hSpecStack, hFrameCorr, _⟩ := pcCorr_stack_cons (hSim.pcCorr e) hStack
  have hNotRO : ¬ atRegOp frame := by
    intro hAR; simp [atRegOp] at hAR
    cases hk : frame.kind <;> simp [hk] at hAR <;>
      (rw [hAR] at hStmt; obtain ⟨ib, hBM, hBE⟩ := hFrameCorr.bodyCorr; rw [hk] at hBE; rw [hBE] at hStmt; simp at hStmt)
  obtain ⟨specLoopBody, _, hSpecStmt, _, _⟩ := frameCorr_loop_stmt hFrameCorr hNotRO hStmt
  have hSMP := hSpecInv.wellFormedPC e
  rw [hSpecStack] at hSMP
  have hUniqBody := smp_uniqueScopeIds hSMP hUniq sf (List.Mem.head _)
  have hMem : sid ∈ scopeIdsOf sf.body := mem_scopeIdsOf_of_getElem hSpecStmt (by simp [scopeIdsOf])
  intro parent hP
  cases hk : sf.kind with
  | top =>
    have hBodyEq : sf.body = spec.body := by
      cases hSMP with | base => rfl | loop => simp at hk | cond _ _ _ _ _ _ _ _ taken => cases taken <;> simp at hk
    have hGoEq : scopeParent.go sf.body sid none = none :=
      scopeParent_go_of_direct_loop (container := none) hSpecStmt hUniqBody
    rw [scopeParent] at hP; rw [hBodyEq] at hGoEq; rw [hGoEq] at hP; simp at hP
  | loop lid =>
    have hGoEq : scopeParent.go sf.body sid sf.kind.loopId? = some lid := by
      simp [hk]; exact scopeParent_go_of_direct_loop (container := some lid) hSpecStmt hUniqBody
    have hLift := smp_lift_scopeParent_go hSMP hUniq sf srest rfl hGoEq hMem
    rw [scopeParent] at hP; rw [hLift] at hP; simp at hP; subst hP
    rw [hSpecStack]; simp [enclosingLoopsFromStack, hk]
  | cond cid =>
    have hGoEq : scopeParent.go sf.body sid sf.kind.loopId? = some cid := by
      simp [hk]; exact scopeParent_go_of_direct_loop (container := some cid) hSpecStmt hUniqBody
    have hLift := smp_lift_scopeParent_go hSMP hUniq sf srest rfl hGoEq hMem
    rw [scopeParent] at hP; rw [hLift] at hP; simp at hP; subst hP
    rw [hSpecStack]; simp [enclosingLoopsFromStack, hk]

/-- Overload for cond thenId case -/
theorem scopeParent_in_enclosingLoops_cond_then
    {spec : Program} {impl : ImplProgram} {ab : AllocBase spec impl}
    {SemaInv : SpecState → ImplState → Prop}
    {ss : SpecState} {is : ImplState} {e : EngineId}
    (hSim : MatchStates spec impl ab SemaInv ss is) (hSpecInv : SpecInv spec ss)
    (hUniq : UniqueScopeIds spec.body) (_hEngines : e ∈ spec.engines)
    {frame : ImplFrame} {rest : List ImplFrame}
    (hStack : (is.pc e).stack = frame :: rest)
    {thenId elseId : ScopeId} {thenBody elseBody : List ImplStmt}
    (hStmt : frame.body[frame.stmtIdx]? = some (.cond thenId elseId thenBody elseBody))
    : ∀ parent, scopeParent spec.body thenId = some parent →
      parent ∈ enclosingLoopsFromStack (ss.pc e).stack := by
  obtain ⟨sf, srest, hSpecStack, hFrameCorr, _⟩ := pcCorr_stack_cons (hSim.pcCorr e) hStack
  have hNotRO : ¬ atRegOp frame := by
    intro hAR; simp [atRegOp] at hAR
    cases hk : frame.kind <;> simp [hk] at hAR <;>
      (rw [hAR] at hStmt; obtain ⟨ib, hBM, hBE⟩ := hFrameCorr.bodyCorr; rw [hk] at hBE; rw [hBE] at hStmt; simp at hStmt)
  obtain ⟨_, _, _, _, hSpecStmt, _, _, _, _⟩ := frameCorr_cond_stmt hFrameCorr hNotRO hStmt
  have hSMP := hSpecInv.wellFormedPC e; rw [hSpecStack] at hSMP
  have hUniqBody := smp_uniqueScopeIds hSMP hUniq sf (List.Mem.head _)
  have hMem : thenId ∈ scopeIdsOf sf.body := mem_scopeIdsOf_of_getElem hSpecStmt (by simp [scopeIdsOf])
  intro parent hP
  cases hk : sf.kind with
  | top =>
    have hBodyEq : sf.body = spec.body := by
      cases hSMP with | base => rfl | loop => simp at hk | cond _ _ _ _ _ _ _ _ taken => cases taken <;> simp at hk
    have hGoEq : scopeParent.go sf.body thenId none = none :=
      scopeParent_go_of_direct_cond_then (container := none) hSpecStmt hUniqBody
    rw [scopeParent] at hP; rw [hBodyEq] at hGoEq; rw [hGoEq] at hP; simp at hP
  | loop lid =>
    have hGoEq : scopeParent.go sf.body thenId sf.kind.loopId? = some lid := by
      simp [hk]; exact scopeParent_go_of_direct_cond_then (container := some lid) hSpecStmt hUniqBody
    have hLift := smp_lift_scopeParent_go hSMP hUniq sf srest rfl hGoEq hMem
    rw [scopeParent] at hP; rw [hLift] at hP; simp at hP; subst hP
    rw [hSpecStack]; simp [enclosingLoopsFromStack, hk]
  | cond cid =>
    have hGoEq : scopeParent.go sf.body thenId sf.kind.loopId? = some cid := by
      simp [hk]; exact scopeParent_go_of_direct_cond_then (container := some cid) hSpecStmt hUniqBody
    have hLift := smp_lift_scopeParent_go hSMP hUniq sf srest rfl hGoEq hMem
    rw [scopeParent] at hP; rw [hLift] at hP; simp at hP; subst hP
    rw [hSpecStack]; simp [enclosingLoopsFromStack, hk]

/-- Overload for cond elseId case -/
theorem scopeParent_in_enclosingLoops_cond_else
    {spec : Program} {impl : ImplProgram} {ab : AllocBase spec impl}
    {SemaInv : SpecState → ImplState → Prop}
    {ss : SpecState} {is : ImplState} {e : EngineId}
    (hSim : MatchStates spec impl ab SemaInv ss is) (hSpecInv : SpecInv spec ss)
    (hUniq : UniqueScopeIds spec.body) (_hEngines : e ∈ spec.engines)
    {frame : ImplFrame} {rest : List ImplFrame}
    (hStack : (is.pc e).stack = frame :: rest)
    {thenId elseId : ScopeId} {thenBody elseBody : List ImplStmt}
    (hStmt : frame.body[frame.stmtIdx]? = some (.cond thenId elseId thenBody elseBody))
    : ∀ parent, scopeParent spec.body elseId = some parent →
      parent ∈ enclosingLoopsFromStack (ss.pc e).stack := by
  obtain ⟨sf, srest, hSpecStack, hFrameCorr, _⟩ := pcCorr_stack_cons (hSim.pcCorr e) hStack
  have hNotRO : ¬ atRegOp frame := by
    intro hAR; simp [atRegOp] at hAR
    cases hk : frame.kind <;> simp [hk] at hAR <;>
      (rw [hAR] at hStmt; obtain ⟨ib, hBM, hBE⟩ := hFrameCorr.bodyCorr; rw [hk] at hBE; rw [hBE] at hStmt; simp at hStmt)
  obtain ⟨_, _, _, _, hSpecStmt, _, _, _, _⟩ := frameCorr_cond_stmt hFrameCorr hNotRO hStmt
  have hSMP := hSpecInv.wellFormedPC e; rw [hSpecStack] at hSMP
  have hUniqBody := smp_uniqueScopeIds hSMP hUniq sf (List.Mem.head _)
  have hMem : elseId ∈ scopeIdsOf sf.body := mem_scopeIdsOf_of_getElem hSpecStmt (by simp [scopeIdsOf])
  intro parent hP
  cases hk : sf.kind with
  | top =>
    have hBodyEq : sf.body = spec.body := by
      cases hSMP with | base => rfl | loop => simp at hk | cond _ _ _ _ _ _ _ _ taken => cases taken <;> simp at hk
    have hGoEq : scopeParent.go sf.body elseId none = none :=
      scopeParent_go_of_direct_cond_else (container := none) hSpecStmt hUniqBody
    rw [scopeParent] at hP; rw [hBodyEq] at hGoEq; rw [hGoEq] at hP; simp at hP
  | loop lid =>
    have hGoEq : scopeParent.go sf.body elseId sf.kind.loopId? = some lid := by
      simp [hk]; exact scopeParent_go_of_direct_cond_else (container := some lid) hSpecStmt hUniqBody
    have hLift := smp_lift_scopeParent_go hSMP hUniq sf srest rfl hGoEq hMem
    rw [scopeParent] at hP; rw [hLift] at hP; simp at hP; subst hP
    rw [hSpecStack]; simp [enclosingLoopsFromStack, hk]
  | cond cid =>
    have hGoEq : scopeParent.go sf.body elseId sf.kind.loopId? = some cid := by
      simp [hk]; exact scopeParent_go_of_direct_cond_else (container := some cid) hSpecStmt hUniqBody
    have hLift := smp_lift_scopeParent_go hSMP hUniq sf srest rfl hGoEq hMem
    rw [scopeParent] at hP; rw [hLift] at hP; simp at hP; subst hP
    rw [hSpecStack]; simp [enclosingLoopsFromStack, hk]

private theorem foldRegOps_eq_foldl (ops : List RegOp) (regs : RegId → Nat) :
    foldRegOps ops regs = ops.foldl (fun regs x => funUpdate regs x.fst (applyRegOpKind x.2.snd (regs x.2.fst) (regs x.fst))) regs := by
  induction ops generalizing regs with
  | nil => simp [foldRegOps]
  | cons op rest ih =>
    obtain ⟨dst, src, t⟩ := op; simp only [foldRegOps, List.foldl_cons]; exact ih _

private theorem foldRegOps_scopeEntryOps_monotoneReg_bwd
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

namespace BackwardSim

/-! ### Shared helpers for repeated proof patterns -/

/-- The `hNotRO` proof for cases with a `.block f` statement: if the frame holds a block,
    it cannot be at the regOp position. Used in issue, blockDone, loopEnter, loopSkip,
    condTrue, condFalse, issue_depSat. -/
private theorem not_atRegOp_of_block {ab : AllocBase spec impl} {sf : Frame} {imf : ImplFrame}
    {f : EngineId → List DataPathInstrId}
    (hFrameCorr : FrameCorr ab sf imf)
    (hStmt : imf.body[imf.stmtIdx]? = some (.block f))
    : ¬ atRegOp imf := by
  intro hAR; simp [atRegOp] at hAR
  cases hk : imf.kind <;> simp [hk] at hAR <;>
    (rw [hAR] at hStmt; obtain ⟨ib, hBM, hBE⟩ := hFrameCorr.bodyCorr; rw [hk] at hBE; rw [hBE] at hStmt; simp at hStmt)


/-- The `hNotRO` proof for loop-end cases (loopBack, condDone) where stmtIdx = body.length.
    Works for any kind that is `.loop id` or `.cond id`. -/
private theorem not_atRegOp_of_loop_end {ab : AllocBase spec impl} {sf : Frame} {imf : ImplFrame}
    (hFrameCorr : FrameCorr ab sf imf)
    (hKind : (∃ id, imf.kind = .loop id) ∨ (∃ id, imf.kind = .cond id))
    (hEnd : imf.stmtIdx = imf.body.length)
    : ¬ atRegOp imf := by
  intro hRO
  rcases hKind with ⟨_, hK⟩ | ⟨_, hK⟩ <;> simp [atRegOp, hK] at hRO <;>
    (obtain ⟨_, ⟨implBody, _, hBE⟩, _⟩ := hFrameCorr
     rw [hK] at hBE; simp at hBE; rw [hBE] at hEnd; simp at hEnd; omega)

/-- Compute `sf.stmtIdx = sf.body.length` from frame correspondence at loop end. -/
private theorem specEnd_of_loop_end {ab : AllocBase spec impl} {sf : Frame} {imf : ImplFrame}
    (hFrameCorr : FrameCorr ab sf imf)
    (hKind : (∃ id, imf.kind = .loop id) ∨ (∃ id, imf.kind = .cond id))
    (hEnd : imf.stmtIdx = imf.body.length)
    (hNotRO : ¬ atRegOp imf)
    : sf.stmtIdx = sf.body.length := by
  obtain ⟨hKC, ⟨implBody, hBM, hBE⟩, hIC⟩ := hFrameCorr
  have hIC2 := hIC.2 hNotRO
  rcases hKind with ⟨_, hK⟩ | ⟨_, hK⟩ <;> rw [hK] at hBE hIC2 <;> simp at hBE hIC2 <;>
    (rw [hBE] at hEnd; simp at hEnd; have hBMLen := bodyMatch_length hBM; omega)


/-- The `atLoopStart` iff for advance-parent cases (blockDone, loopSkip).
    When the new top frame has stmtIdx + 1 (from advancing), atLoopStart is impossible for engine e. -/
private theorem atLoopStart_iff_advance_parent
    {is : ImplState} {e : EngineId}
    {frame : ImplFrame} {rest : List ImplFrame}
    (hStack : (is.pc e).stack = frame :: rest)
    (hNotRO : ¬ atRegOp frame)
    : ∀ e' lid, atLoopStart { is with
        pc := funUpdate is.pc e
          { stack := ⟨frame.body, frame.stmtIdx + 1, frame.kind⟩ :: rest,
            instrIdx := i, regOpIdx := r, stmtRegOpIdx := 0 } } e' lid ↔
      atLoopStart is e' lid := by
  intro e' lid; constructor
  · intro ⟨fr, rl, hS, hK, hI⟩; by_cases he : e' = e
    · subst he; simp only [funUpdate, ite_true] at hS
      obtain ⟨rfl, _⟩ := hS; simp at hI
    · exact ⟨fr, rl, by simp [funUpdate, he] at hS; exact hS, hK, hI⟩
  · intro h; by_cases he : e' = e
    · subst he; exact absurd h (not_atLoopStart_of_not_atRegOp hStack hNotRO lid)
    · obtain ⟨fr, rl, hS, hK, hI⟩ := h
      exact ⟨fr, rl, by simp [funUpdate, he]; exact hS, hK, hI⟩

/-- The `atLoopStart` iff for issue cases where only instrIdx/regOpIdx change. -/
private theorem atLoopStart_iff_instr_advance
    {is : ImplState} {e : EngineId}
    {frame : ImplFrame} {rest : List ImplFrame}
    (hStack : (is.pc e).stack = frame :: rest)
    (_hNotRO : ¬ atRegOp frame)
    : ∀ e' lid, atLoopStart { is with
        pc := funUpdate is.pc e
          { (is.pc e) with instrIdx := i, regOpIdx := r } } e' lid ↔
      atLoopStart is e' lid := by
  intro e' lid; constructor
  · intro ⟨fr, rl, hS, hK, hI⟩; by_cases he : e' = e
    · subst he; simp at hS; exact ⟨fr, rl, hS, hK, hI⟩
    · exact ⟨fr, rl, by simp [he] at hS; exact hS, hK, hI⟩
  · intro ⟨fr, rl, hS, hK, hI⟩; by_cases he : e' = e
    · subst he; exact ⟨fr, rl, by simp; exact hS, hK, hI⟩
    · exact ⟨fr, rl, by simp [he]; exact hS, hK, hI⟩

/-- Shared `monotoneRegInv` for loopBack: pop to parent :: rest where parent is not at regOp.  -/
private theorem monotoneRegInv_loop_pop_to_parent
    {is : ImplState} {e : EngineId}
    {frame parent : ImplFrame} {rest : List ImplFrame}
    (hStack : (is.pc e).stack = frame :: parent :: rest)
    (hNotRO : ¬ atRegOp frame)
    (hParentNotRO : ¬ atRegOp parent)
    : ∀ e' lid, atLoopStart { is with
        pc := funUpdate is.pc e
          { stack := parent :: rest, instrIdx := 0, regOpIdx := 0, stmtRegOpIdx := 0 } } e' lid ↔
      atLoopStart is e' lid := by
  intro e' lid; constructor
  · intro ⟨fr, r, hS, hK, hI⟩; by_cases he : e' = e
    · subst he; simp only [funUpdate, ite_true] at hS
      obtain ⟨rfl, rfl⟩ := hS
      exfalso; apply hParentNotRO; simp only [atRegOp]
      rcases hK with hK | hK <;> rw [hK] <;> exact hI
    · exact ⟨fr, r, by simp [funUpdate, he] at hS; exact hS, hK, hI⟩
  · intro h; by_cases he : e' = e
    · subst he; exact absurd h (not_atLoopStart_of_not_atRegOp hStack hNotRO lid)
    · obtain ⟨fr, r, hS, hK, hI⟩ := h
      exact ⟨fr, r, by simp [funUpdate, he]; exact hS, hK, hI⟩

private theorem innerOps_dst_waitReg {innerOps : List RegOp} {waitR : RegId}
    (hDst : ∀ (idx : Nat) (dst src : RegId) (t : RegOpKind), innerOps[idx]? = some (dst, src, t) → dst = waitR)
    : ∀ op ∈ innerOps, op.1 = waitR := by
  intro ⟨d, s, tr⟩ hMem
  obtain ⟨idx, hGet⟩ := List.mem_iff_getElem?.mp hMem
  exact hDst idx d s tr hGet

private theorem wrapWithGate_gateReg_idx {spec : Program} {gateR waitR : RegId}
    {tripReg : EngineId → ScopeId → RegId} {e : EngineId} {consumer : DataPathInstrId}
    {innerOps : List RegOp}
    (hGNeW : gateR ≠ waitR)
    (hInnerDst : ∀ op ∈ innerOps, op.1 = waitR)
    {n : Nat} {src : RegId} {t : RegOpKind}
    (hGet : (wrapWithGate spec gateR waitR tripReg e consumer innerOps)[n]? = some (gateR, src, t))
    : n = 1 := by
  unfold wrapWithGate at hGet
  match hDep : spec.depGraph consumer with
  | .none =>
    simp only [hDep] at hGet; exact absurd (hInnerDst _ (List.mem_of_getElem? hGet)) hGNeW
  | .dep producer offset =>
    simp only [hDep] at hGet
    match hSS : innermostSharedScope spec.engines spec.body producer consumer with
    | none =>
      simp only [hSS] at hGet; exact absurd (hInnerDst _ (List.mem_of_getElem? hGet)) hGNeW
    | some sid =>
      simp only [hSS, List.cons_append, List.nil_append] at hGet
      match n with
      | 0 => simp at hGet; exact absurd hGet.1 (Ne.symm hGNeW)
      | 1 => rfl
      | n + 2 =>
        simp at hGet
        rcases List.mem_append.mp (List.mem_of_getElem? hGet) with h | h
        · exact absurd (hInnerDst _ h) hGNeW
        · simp at h; exact absurd h.1 hGNeW

private theorem wrapWithGate_gateReg_op0 {spec : Program} {gateR waitR : RegId}
    {tripReg : EngineId → ScopeId → RegId} {e : EngineId} {consumer : DataPathInstrId}
    {innerOps : List RegOp}
    (hGNeW : gateR ≠ waitR)
    (hInnerDst : ∀ op ∈ innerOps, op.1 = waitR)
    {src : RegId} {t : RegOpKind}
    (hGet : (wrapWithGate spec gateR waitR tripReg e consumer innerOps)[1]? = some (gateR, src, t))
    : (wrapWithGate spec gateR waitR tripReg e consumer innerOps)[0]? = some (waitR, waitR, .const 0) := by
  unfold wrapWithGate at hGet ⊢
  match hDep : spec.depGraph consumer with
  | .none =>
    simp only [hDep] at hGet; exact absurd (hInnerDst _ (List.mem_of_getElem? hGet)) hGNeW
  | .dep producer offset =>
    simp only [hDep] at hGet ⊢
    match hSS : innermostSharedScope spec.engines spec.body producer consumer with
    | none =>
      simp only [hSS] at hGet; exact absurd (hInnerDst _ (List.mem_of_getElem? hGet)) hGNeW
    | some sid => rfl

private theorem wrapWithGate_gateReg_isGT {spec : Program} {gateR waitR : RegId}
    {tripReg : EngineId → ScopeId → RegId} {e : EngineId} {consumer : DataPathInstrId}
    {innerOps : List RegOp}
    (hGNeW : gateR ≠ waitR)
    (hInnerDst : ∀ op ∈ innerOps, op.1 = waitR)
    {src : RegId} {t : RegOpKind}
    (hGet : (wrapWithGate spec gateR waitR tripReg e consumer innerOps)[1]? = some (gateR, src, t))
    : ∃ off, t = .isGT off := by
  unfold wrapWithGate at hGet
  match hDep : spec.depGraph consumer with
  | .none =>
    simp only [hDep] at hGet; exact absurd (hInnerDst _ (List.mem_of_getElem? hGet)) hGNeW
  | .dep producer off =>
    simp only [hDep] at hGet
    match hSS : innermostSharedScope spec.engines spec.body producer consumer with
    | none =>
      simp only [hSS] at hGet; exact absurd (hInnerDst _ (List.mem_of_getElem? hGet)) hGNeW
    | some sid =>
      simp only [hSS, List.cons_append, List.nil_append] at hGet
      simp at hGet; exact ⟨off, hGet.2.symm⟩

private theorem wrapWithGate_gateReg_src_ne {spec : Program} {gateR waitR : RegId}
    {tripReg : EngineId → ScopeId → RegId} {e : EngineId} {consumer : DataPathInstrId}
    {innerOps : List RegOp}
    (hGNeW : gateR ≠ waitR)
    (hInnerDst : ∀ op ∈ innerOps, op.1 = waitR)
    (hResNeW : ∀ lid, tripReg e lid ≠ waitR)
    (hGNeR : ∀ lid, gateR ≠ tripReg e lid)
    {src : RegId} {t : RegOpKind}
    (hGet : (wrapWithGate spec gateR waitR tripReg e consumer innerOps)[1]? = some (gateR, src, t))
    : src ≠ waitR ∧ src ≠ gateR := by
  unfold wrapWithGate at hGet
  match hDep : spec.depGraph consumer with
  | .none =>
    simp only [hDep] at hGet; exact absurd (hInnerDst _ (List.mem_of_getElem? hGet)) hGNeW
  | .dep producer offset =>
    simp only [hDep] at hGet
    match hSS : innermostSharedScope spec.engines spec.body producer consumer with
    | none =>
      simp only [hSS] at hGet; exact absurd (hInnerDst _ (List.mem_of_getElem? hGet)) hGNeW
    | some sid =>
      simp only [hSS, List.cons_append, List.nil_append] at hGet
      simp at hGet; obtain ⟨rfl, rfl⟩ := hGet
      exact ⟨hResNeW sid, Ne.symm (hGNeR sid)⟩

theorem case_regOpStep (spec : Program) (impl : ImplProgram) (ab : AllocBase spec impl)
    (SemaInv : SpecState → ImplState → Prop)
    (hSemaInvMono : SemaInvMono SemaInv)
    (innerOps : EngineId → DataPathInstrId → List RegOp)
    (hInnerOpsWf : InnerRegOpsWf innerOps ab)
    (hRegOpsEq : ∀ e i, impl.regOps e i = wrapWithGate spec (ab.gateReg e) (ab.waitReg e) ab.tripReg e i (innerOps e i))
    (e : EngineId) (ss : SpecState) (is : ImplState)
    (hSim : MatchStates spec impl ab SemaInv ss is)
    (frame : ImplFrame) (rest : List ImplFrame)
    (f : EngineId → List DataPathInstrId) (instr : DataPathInstrId)
    (dst src : RegId) (t : RegOpKind)
    (hStack : (is.pc e).stack = frame :: rest)
    (hStmt : frame.body[frame.stmtIdx]? = some (.block f))
    (hInstr : (f e)[(is.pc e).instrIdx]? = some instr)
    (hRegOp : (impl.regOps e instr)[(is.pc e).regOpIdx]? = some (dst, src, t))
    : let is' := { is with
        registers := funUpdate is.registers e
          (funUpdate (is.registers e) dst (applyRegOpKind t (is.registers e src) (is.registers e dst)))
        pc := funUpdate is.pc e
          { (is.pc e) with regOpIdx := (is.pc e).regOpIdx + 1 } }
      (∃ ss', SpecStep spec e ss ss' ∧ MatchStates spec impl ab SemaInv ss' is')
    ∨ MatchStates spec impl ab SemaInv ss is' := by
    right
    have hDstOr : dst = ab.waitReg e ∨ dst = ab.gateReg e := by
      rw [hRegOpsEq] at hRegOp
      exact wrapWithGate_dst (fun op hMem => hInnerOpsWf.dstWaitReg e instr _ _ _ _ (List.mem_iff_getElem?.mp hMem |>.choose_spec)) hRegOp
    have hLoopNeDst : ∀ lid', ab.monotoneReg e lid' ≠ dst :=
      fun lid' => hDstOr.elim (fun h => h ▸ Ne.symm (ab.noClob e lid')) (fun h => h ▸ Ne.symm (ab.noClob_gate_loop e lid'))
    have hResNeDst : ∀ lid', ab.tripReg e lid' ≠ dst :=
      fun lid' => hDstOr.elim (fun h => h ▸ Ne.symm (ab.noClob_trip_wait e lid')) (fun h => h ▸ Ne.symm (ab.noClob_gate_trip e lid'))
    exact { dataPathEq := hSim.dataPathEq, inflightEq := hSim.inflightEq, controlEq := hSim.controlEq
            semaInv := hSemaInvMono ss ss is _ rfl rfl hSim.semaInv
            monotoneRegInv := by
              intro e' lid' hNALS_all
              by_cases he : e' = e
              · simp only [funUpdate, ite_true, he]
                have hNeR : ab.monotoneReg e lid' ≠ dst := hLoopNeDst lid'
                simp [hNeR]
                have hNALS' : ¬ atLoopStart is e lid' := by
                  intro h; apply hNALS_all; simp only [atLoopStart, funUpdate, ite_true, he] at h ⊢
                  obtain ⟨fr, r, hS, hK, hI⟩ := h; exact ⟨fr, r, hS, hK, hI⟩
                exact hSim.monotoneRegInv e lid' hNALS'
              · simp only [funUpdate, if_neg he]
                have hNALS' : ¬ atLoopStart is e' lid' := by
                  intro h; apply hNALS_all; simp only [atLoopStart, funUpdate, if_neg he] at h ⊢; exact h
                exact hSim.monotoneRegInv e' lid' hNALS'
            tripRegInv := by
              intro e' lid' hNALS_all
              by_cases he : e' = e
              · simp only [funUpdate, ite_true, he]
                have hNeR : ab.tripReg e lid' ≠ dst := hResNeDst lid'
                simp [hNeR]
                have hOldNALS : ∀ lid', ¬ atLoopStart is e lid' := by
                  intro lid' h; exact hNALS_all lid' (by simp only [atLoopStart, funUpdate, ite_true, he] at h ⊢; exact h)
                exact hSim.tripRegInv e lid' hOldNALS
              · simp only [funUpdate, if_neg he]
                have hOldNALS : ∀ lid', ¬ atLoopStart is e' lid' := by
                  intro lid' h; exact hNALS_all lid' (by simp only [atLoopStart, funUpdate, if_neg he] at h ⊢; exact h)
                exact hSim.tripRegInv e' lid' hOldNALS
            regOpFold := by
              intro e' frame' rest' ops' hStack' hStmt'
              by_cases he : e' = e
              · subst he; simp only [funUpdate_same] at hStack'
                rw [hStack] at hStack'; obtain ⟨rfl, rfl⟩ := List.cons.inj hStack'
                rw [hStmt] at hStmt'; simp at hStmt'
              · simp only [funUpdate, if_neg he] at hStack' ⊢
                exact hSim.regOpFold e' frame' rest' ops' hStack' hStmt'
            pcCorr := by
              intro e'; simp only [funUpdate]; split
              · next he => subst he; exact ⟨(hSim.pcCorr e').1, (hSim.pcCorr e').2⟩
              · exact hSim.pcCorr e'
            waitRegChain := by
              intro e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
              by_cases he : e' = e
              · -- e' = e case: waitRegChain extension after one regOp step
                subst he; simp only [funUpdate_same] at hStack' hInstr' hROI ⊢
                rw [hStack] at hStack'; obtain ⟨rfl, rfl⟩ := List.cons.inj hStack'
                rw [hStmt] at hStmt'; simp at hStmt'; subst hStmt'
                rw [hInstr] at hInstr'; simp at hInstr'; subst hInstr'
                have hGW := ab.noClob_gate_wait e'
                have hInnerDst : ∀ op ∈ innerOps e' instr, op.1 = ab.waitReg e' :=
                  fun _ hMem => hInnerOpsWf.dstWaitReg e' instr _ _ _ _ (List.mem_iff_getElem?.mp hMem |>.choose_spec)
                -- Decompose take (n+1) = take n ++ [op[n]]
                rw [List.take_add_one, hRegOp, Option.toList_some, foldRegOps_append]
                simp only [foldRegOps]
                rcases hDstOr with rfl | rfl
                · -- dst = waitReg: newBase = oldBase since funUpdate at w doesn't affect base
                  simp only [funUpdate_same]
                  have hBasesEq : ∀ r,
                      (fun r => if r = ab.waitReg e' then (0 : Nat) else
                        funUpdate (is.registers e') (ab.waitReg e')
                          (applyRegOpKind t (is.registers e' src) (is.registers e' (ab.waitReg e'))) r) r =
                      (fun r => if r = ab.waitReg e' then (0 : Nat) else is.registers e' r) r := by
                    intro r; simp [funUpdate]; split <;> simp [*]
                  simp only [foldRegOps_congr hBasesEq]
                  -- Need: applyRegOpKind t (regs src) (regs w) = applyRegOpKind t (fold src) (fold w)
                  -- where fold = foldRegOps (take n ops) oldBase
                  rcases Nat.eq_zero_or_pos (is.pc e').regOpIdx with h0 | hPos
                  · -- regOpIdx = 0: first op
                    rw [h0, List.take_zero]; simp [foldRegOps]
                    have hOp0 : (impl.regOps e' instr)[0]? = some (ab.waitReg e', src, t) := by rw [h0] at hRegOp; exact hRegOp
                    rw [hRegOpsEq] at hOp0; unfold wrapWithGate at hOp0
                    split at hOp0
                    · have ⟨hNM, hSW⟩ := hInnerOpsWf.firstSafe e' instr src t hOp0
                      by_cases hsrc : src = ab.waitReg e'
                      · obtain ⟨n, hn⟩ := hSW hsrc; subst hn; simp [applyRegOpKind]
                      · cases t <;> simp_all [RegOpKind.usesDst, applyRegOpKind]
                    · rename_i producer offset hDep
                      cases hSS : innermostSharedScope spec.engines spec.body producer instr with
                      | some sid =>
                        simp only [hSS] at hOp0; simp at hOp0; obtain ⟨rfl, rfl, rfl⟩ := hOp0
                        simp [applyRegOpKind]
                      | none =>
                        simp only [hSS] at hOp0
                        have ⟨hNM, hSW⟩ := hInnerOpsWf.firstSafe e' instr src t hOp0
                        by_cases hsrc : src = ab.waitReg e'
                        · obtain ⟨n, hn⟩ := hSW hsrc; subst hn; simp [applyRegOpKind]
                        · cases t <;> simp_all [RegOpKind.usesDst, applyRegOpKind]
                  · -- regOpIdx > 0: use waitRegChain + fold(src) = regs(src)
                    have hChain := (hSim.waitRegChain e' frame rest f instr hStack hStmt hInstr hPos).symm
                    have hFoldSrc : foldRegOps (List.take (is.pc e').regOpIdx (impl.regOps e' instr))
                        (fun r => if r = ab.waitReg e' then 0 else is.registers e' r) src =
                        is.registers e' src := by
                      by_cases hsW : src = ab.waitReg e'
                      · rw [hsW, ← hChain]
                      · by_cases hsG : src = ab.gateReg e'
                        · rw [hsG]; exact (hSim.gateRegChain e' frame rest f instr hStack hStmt hInstr hPos).symm
                        · rw [foldRegOps_other (fun op hMem => by
                            have hMemFull := List.mem_of_mem_take hMem
                            rw [hRegOpsEq] at hMemFull
                            have ⟨idx, hGet⟩ := List.mem_iff_getElem?.mp hMemFull
                            rcases wrapWithGate_dst hInnerDst hGet with h | h
                            · exact fun heq => hsW (heq.symm.trans h)
                            · exact fun heq => hsG (heq.symm.trans h))]
                          simp [hsW]
                    rw [hFoldSrc, hChain]
                · -- dst = gateReg: regOpIdx = 1, both sides = 0
                  have hOps := hRegOpsEq e' instr
                  rw [hOps] at hRegOp
                  have hn1 := wrapWithGate_gateReg_idx hGW
                    (innerOps_dst_waitReg (fun idx d s tr h => hInnerOpsWf.dstWaitReg e' instr idx d s tr h)) hRegOp
                  rw [hn1] at hRegOp
                  have hOp0 := wrapWithGate_gateReg_op0 hGW
                    (innerOps_dst_waitReg (fun idx d s tr h => hInnerOpsWf.dstWaitReg e' instr idx d s tr h)) hRegOp
                  -- LHS: funUpdate at gateReg evaluated at waitReg = regs(waitReg) since gateReg ≠ waitReg
                  -- RHS: foldRegOps of take 2 ops. First op (.const 0) sets w := 0,
                  --       second op writes gateReg (doesn't touch w). Result at w = 0.
                  -- regs(w) = 0 from old chain (regOpIdx = 1, first op = .const 0)
                  -- Show both sides = 0
                  have hRegsW0 : is.registers e' (ab.waitReg e') = 0 := by
                    rw [hSim.waitRegChain e' frame rest f instr hStack hStmt hInstr (hn1 ▸ Nat.one_pos)]
                    rw [hn1, hOps]; simp only [List.take_add_one, hOp0, Option.toList_some, List.take_zero, List.nil_append]
                    simp [foldRegOps, applyRegOpKind, funUpdate]
                  -- Both sides reduce to 0
                  simp only [funUpdate, hRegsW0, if_neg (Ne.symm hGW)]
                  rw [hn1, hOps]; simp only [List.take_add_one, hOp0, Option.toList_some, List.take_zero, List.nil_append]
                  simp only [foldRegOps, applyRegOpKind, funUpdate]
                  simp
              · simp [funUpdate, if_neg he] at hStack' hInstr' hROI ⊢
                exact hSim.waitRegChain e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
            gateRegChain := by
              intro e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
              by_cases he : e' = e
              · -- e' = e case: gateRegChain extension after one regOp step
                subst he; simp only [funUpdate_same] at hStack' hInstr' hROI ⊢
                rw [hStack] at hStack'; obtain ⟨rfl, rfl⟩ := List.cons.inj hStack'
                rw [hStmt] at hStmt'; simp at hStmt'; subst hStmt'
                rw [hInstr] at hInstr'; simp at hInstr'; subst hInstr'
                have hGW := ab.noClob_gate_wait e'
                have hInnerDst : ∀ op ∈ innerOps e' instr, op.1 = ab.waitReg e' :=
                  fun _ hMem => hInnerOpsWf.dstWaitReg e' instr _ _ _ _ (List.mem_iff_getElem?.mp hMem |>.choose_spec)
                -- For gateR ≠ waitR: the same proof approach as waitRegChain, but at gateR
                -- Both dst cases handled together
                rcases hDstOr with rfl | rfl
                · -- dst = waitR: LHS = regs gateR, RHS = fold(take(n+1))(newBase)(gateR)
                  -- newBase agrees with oldBase, and the step op writes waitR not gateR
                  have hBasesEq : (fun r => if r = ab.waitReg e' then (0 : Nat) else
                        funUpdate (is.registers e') (ab.waitReg e')
                          (applyRegOpKind t (is.registers e' src) (is.registers e' (ab.waitReg e'))) r) =
                      (fun r => if r = ab.waitReg e' then (0 : Nat) else is.registers e' r) :=
                    funext fun r => by simp [funUpdate]; split <;> simp [*]
                  -- Simplify LHS: funUpdate regs waitR v gateR = regs gateR
                  -- Simplify RHS: replace newBase with oldBase
                  rw [show funUpdate (is.registers e') (ab.waitReg e')
                      (applyRegOpKind t (is.registers e' src) (is.registers e' (ab.waitReg e')))
                      (ab.gateReg e') = is.registers e' (ab.gateReg e') from by
                    simp [funUpdate, hGW], hBasesEq]
                  rw [List.take_add_one, hRegOp, Option.toList_some, foldRegOps_append]
                  simp only [foldRegOps, funUpdate, if_neg hGW]
                  rcases Nat.eq_zero_or_pos (is.pc e').regOpIdx with h0 | hPos
                  · rw [h0, List.take_zero]; simp [foldRegOps]; simp [hGW]
                  · exact hSim.gateRegChain e' frame rest f instr hStack hStmt hInstr hPos
                · -- dst = gateR: regOpIdx must be 1 (only op[1] writes gateR in wrapWithGate)
                  -- Extract t = .isGT offset by unfolding wrapWithGate at hRegOp
                  have hOps := hRegOpsEq e' instr
                  rw [hOps] at hRegOp
                  have hInnerDstW := innerOps_dst_waitReg (fun idx d s tr h => hInnerOpsWf.dstWaitReg e' instr idx d s tr h)
                  have hn1 := wrapWithGate_gateReg_idx hGW hInnerDstW hRegOp
                  rw [hn1] at hRegOp
                  have hOp0 := wrapWithGate_gateReg_op0 hGW hInnerDstW hRegOp
                  -- Extract the actual transform t from op[1] in wrapWithGate
                  -- op[1] = (gateR, tripR sid, .isGT offset) so t = .isGT offset
                  -- and applyRegOpKind (.isGT offset) srcVal dstVal = if srcVal > offset then 1 else 0
                  -- which doesn't depend on dstVal
                  -- Extract t = .isGT offset from the wrapWithGate structure
                  obtain ⟨offset, rfl⟩ := wrapWithGate_gateReg_isGT hGW hInnerDstW hRegOp
                  -- Now t = .isGT offset
                  -- Rewrite goal: regOpIdx → 1, impl.regOps → wrapWithGate
                  rw [hn1, hOps]
                  simp only [List.take_add_one, hOp0, Option.toList_some, List.take_zero, List.nil_append,
                    show (wrapWithGate spec (ab.gateReg e') (ab.waitReg e') ab.tripReg e' instr (innerOps e' instr))[1]? =
                      some (ab.gateReg e', src, .isGT offset) from hRegOp]
                  -- applyRegOpKind (.isGT offset) srcVal dstVal = if srcVal > offset then 1 else 0
                  -- Both sides are `if regs(src) > offset then 1 else 0`
                  have ⟨hSrcNeW, hSrcNeG⟩ := wrapWithGate_gateReg_src_ne hGW hInnerDstW
                    (fun lid => Ne.symm (ab.noClob_trip_wait e' lid))
                    (fun lid => ab.noClob_gate_trip e' lid) hRegOp
                  simp [foldRegOps, applyRegOpKind, funUpdate, hSrcNeW, hSrcNeG]
              · simp [funUpdate, if_neg he] at hStack' hInstr' hROI ⊢
                exact hSim.gateRegChain e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI }

-- stmtRegOpStep: commit one register op, increment stmtRegOpIdx
theorem case_stmtRegOpStep (spec : Program) (impl : ImplProgram) (ab : AllocBase spec impl)
    (SemaInv : SpecState → ImplState → Prop)
    (hSemaInvMono : SemaInvMono SemaInv)
    (e : EngineId) (ss : SpecState) (is : ImplState)
    (hSim : MatchStates spec impl ab SemaInv ss is)
    (frame : ImplFrame) (rest : List ImplFrame)
    (ops : EngineId → List RegOp)
    (dst src : RegId) (t : RegOpKind)
    (hStack : (is.pc e).stack = frame :: rest)
    (hStmt : frame.body[frame.stmtIdx]? = some (.regOp ops))
    (hOp : (ops e)[(is.pc e).stmtRegOpIdx]? = some (dst, src, t))
    : let is' := { is with
        registers := funUpdate is.registers e
          (funUpdate (is.registers e) dst (applyRegOpKind t (is.registers e src) (is.registers e dst)))
        pc := funUpdate is.pc e
          { (is.pc e) with stmtRegOpIdx := (is.pc e).stmtRegOpIdx + 1 } }
      (∃ ss', SpecStep spec e ss ss' ∧ MatchStates spec impl ab SemaInv ss' is')
    ∨ MatchStates spec impl ab SemaInv ss is' := by
    right
    -- Extract frame correspondence to prove atRegOp
    obtain ⟨sf, srest, hSpecStack, hFrameCorr, hRestCorr, hCovS, hCovI, hNoRegOp⟩ :=
      pcCorr_stack_cons (hSim.pcCorr e) hStack
    -- Prove atRegOp frame: .regOp can only appear at stmtIdx=0 in loop/cond bodies
    have hRO : atRegOp frame := by
      simp only [atRegOp]
      obtain ⟨_, ⟨implBody, hBM, hBE⟩, _⟩ := hFrameCorr
      cases hk : frame.kind with
      | loop lid => rw [hk] at hBE; simp at hBE; rw [hBE] at hStmt
                    cases hsi : frame.stmtIdx with
                    | zero => simp
                    | succ n => rw [hsi] at hStmt; simp [List.getElem?_cons_succ] at hStmt
                                exact (bodyMatch_no_regOp hBM hStmt).elim
      | cond sid => rw [hk] at hBE; simp at hBE; rw [hBE] at hStmt
                    cases hsi : frame.stmtIdx with
                    | zero => simp
                    | succ n => rw [hsi] at hStmt; simp [List.getElem?_cons_succ] at hStmt
                                exact (bodyMatch_no_regOp hBM hStmt).elim
      | top => rw [hk] at hBE; rw [hBE] at hStmt; exact (bodyMatch_no_regOp hBM hStmt).elim
    -- atLoopStart holds in is for engine e, so monotoneRegInv/tripRegInv are vacuously true
    have hALS_e : ∃ lid, atLoopStart is e lid := by
      simp only [atRegOp] at hRO
      cases hk : frame.kind with
      | loop lid => exact ⟨lid, frame, rest, hStack, Or.inl hk, by rw [hk] at hRO; exact hRO⟩
      | cond sid => exact ⟨sid, frame, rest, hStack, Or.inr hk, by rw [hk] at hRO; exact hRO⟩
      | top => simp [hk] at hRO
    exact { dataPathEq := hSim.dataPathEq, inflightEq := hSim.inflightEq, controlEq := hSim.controlEq
            semaInv := hSemaInvMono ss ss is _ rfl rfl hSim.semaInv
            monotoneRegInv := by
              intro e' lid' hNALS_all
              by_cases he : e' = e
              · subst he
                -- atLoopStart holds in is' for engine e' for some lid
                obtain ⟨lid, fr, r, hS, hK, hI⟩ := hALS_e
                -- If lid = lid', then hNALS_all is contradicted
                by_cases hEq : lid = lid'
                · subst hEq
                  exact absurd (⟨fr, r, by simp [funUpdate]; exact hS, hK, hI⟩ : atLoopStart _ _ lid) (hNALS_all)
                · -- If lid ≠ lid', then ¬ atLoopStart for lid', use monotoneRegInv
                  have hNALS' : ¬ atLoopStart is e' lid' := by
                    intro ⟨fr', r', hS', hK', hI'⟩
                    apply hNALS_all
                    exact ⟨fr', r', by simp [funUpdate]; exact hS', hK', hI'⟩
                  -- Unify fr = frame
                  have hFrEq : fr = frame ∧ r = rest := by rw [hS] at hStack; exact List.cons.inj hStack
                  obtain ⟨rfl, rfl⟩ := hFrEq
                  -- Extract ops = scopeEntryOps via FrameCorr.bodyCorr
                  obtain ⟨implBody, hBM, hBE⟩ := hFrameCorr.bodyCorr
                  have hOpsEq : ops = fun e' => scopeEntryOps ab.monotoneReg ab.tripReg sf.body e' lid := by
                    rcases hK with hK | hK <;>
                      (rw [hK] at hBE; simp at hBE; rw [hBE, hI] at hStmt; simp at hStmt; exact hStmt.symm)
                  -- Get membership
                  have hMem : (dst, src, t) ∈ scopeEntryOps ab.monotoneReg ab.tripReg sf.body e' lid := by
                    rw [hOpsEq] at hOp; exact List.mem_of_getElem? hOp
                  -- All destinations ≠ monotoneReg e' lid' when lid ≠ lid'
                  have hDstNe : dst ≠ ab.monotoneReg e' lid' := by
                    unfold scopeEntryOps at hMem
                    simp [List.mem_cons, List.mem_map] at hMem
                    rcases hMem with ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ | ⟨child, -, rfl, -, -⟩
                    · exact fun h => hEq (ab.monotoneRegInj _ _ _ h)
                    · exact ab.noClob_trip_loop e' lid lid'
                    · exact ab.noClob_trip_loop e' child lid'
                  -- Registers at monotoneReg e' lid' are unchanged by the op
                  simp only [funUpdate, ite_true]
                  rw [if_neg (Ne.symm hDstNe)]
                  exact hSim.monotoneRegInv e' lid' hNALS'
              · simp only [funUpdate, if_neg he]
                exact hSim.monotoneRegInv e' lid' (fun ⟨fr, r, hS, hK, hI⟩ =>
                  hNALS_all ⟨fr, r, by simp [funUpdate, he]; exact hS, hK, hI⟩)
            tripRegInv := by
              intro e' lid' hNALS_all
              by_cases he : e' = e
              · subst he
                obtain ⟨lid, fr, r, hS, hK, hI⟩ := hALS_e
                exact absurd (⟨fr, r, by simp [funUpdate]; exact hS, hK, hI⟩ : atLoopStart _ _ lid) (hNALS_all lid)
              · simp only [funUpdate, if_neg he]
                exact hSim.tripRegInv e' lid' (fun lid'' ⟨fr, r, hS, hK, hI⟩ =>
                  hNALS_all lid'' ⟨fr, r, by simp [funUpdate, he]; exact hS, hK, hI⟩)
            regOpFold := by
              intro e' frame' rest' ops' hStack' hStmt'
              by_cases he : e' = e
              · subst he; simp only [funUpdate_same] at hStack' ⊢
                rw [hStack] at hStack'; obtain ⟨rfl, rfl⟩ := List.cons.inj hStack'
                rw [hStmt] at hStmt'; simp at hStmt'; subst hStmt'
                obtain ⟨h1, h2⟩ := hSim.regOpFold e' frame rest ops hStack hStmt
                have hLt : (is.pc e').stmtRegOpIdx < (ops e').length := by
                  by_contra hGe; simp only [Nat.not_lt] at hGe
                  exact absurd hOp (List.getElem?_eq_none hGe ▸ fun h => by simp at h)
                constructor
                · intro lid; have := h1 lid; rwa [foldRegOps_drop_step hLt hOp] at this
                · intro lid; have := h2 lid; rwa [foldRegOps_drop_step hLt hOp] at this
              · simp only [funUpdate, if_neg he] at hStack' ⊢
                exact hSim.regOpFold e' frame' rest' ops' hStack' hStmt'
            pcCorr := by
              intro e'; simp only [funUpdate]; split
              · next he => subst he; exact ⟨(hSim.pcCorr e').1, (hSim.pcCorr e').2⟩
              · exact hSim.pcCorr e'
            waitRegChain := by
              intro e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
              by_cases he : e' = e
              · subst he; simp only [funUpdate_same] at hStack'
                -- frame' = frame (same stack), but frame has .regOp not .block
                rw [hStack] at hStack'; obtain ⟨rfl, rfl⟩ := List.cons.inj hStack'
                rw [hStmt] at hStmt'; simp at hStmt'
              · simp [funUpdate, if_neg he] at hStack' hInstr' hROI ⊢
                exact hSim.waitRegChain e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
            gateRegChain := by
              intro e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
              by_cases he : e' = e
              · subst he; simp only [funUpdate_same] at hStack'
                rw [hStack] at hStack'; obtain ⟨rfl, rfl⟩ := List.cons.inj hStack'
                rw [hStmt] at hStmt'; simp at hStmt'
              · simp [funUpdate, if_neg he] at hStack' hInstr' hROI ⊢
                exact hSim.gateRegChain e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI }

-- stmtRegOpDone: all ops done, advance to next statement
theorem case_stmtRegOpDone (spec : Program) (impl : ImplProgram) (ab : AllocBase spec impl)
    (SemaInv : SpecState → ImplState → Prop)
    (hSemaInvMono : SemaInvMono SemaInv)
    (e : EngineId) (ss : SpecState) (is : ImplState)
    (hSim : MatchStates spec impl ab SemaInv ss is)
    (frame : ImplFrame) (rest : List ImplFrame)
    (ops : EngineId → List RegOp)
    (hStack : (is.pc e).stack = frame :: rest)
    (hStmt : frame.body[frame.stmtIdx]? = some (.regOp ops))
    (hDone : (is.pc e).stmtRegOpIdx = (ops e).length)
    (hLoopRegsE : ∀ lid, is.registers e (ab.monotoneReg e lid) = totalEntries ss e lid)
    (hTripRegsE : ∀ lid, is.registers e (ab.tripReg e lid) = tripEntries ss e spec.body lid)
    : let is' := { is with
        pc := funUpdate is.pc e
          { stack := ⟨frame.body, frame.stmtIdx + 1, frame.kind⟩ :: rest,
            instrIdx := (is.pc e).instrIdx, regOpIdx := 0, stmtRegOpIdx := 0 } }
      (∃ ss', SpecStep spec e ss ss' ∧ MatchStates spec impl ab SemaInv ss' is')
    ∨ MatchStates spec impl ab SemaInv ss is' := by
    right
    -- After stmtRegOpDone, the frame advances from stmtIdx=0 to stmtIdx=1.
    -- atLoopStart becomes false for engine e, so monotoneRegInv/tripRegInv need
    -- actual register values. These were set by preceding stmtRegOpStep calls
    -- (which applied scopeEntryOps), but the MatchStates tracked them vacuously.
    -- For e' ≠ e: unchanged, delegates to old invariant.
    -- For e' = e: requires knowing registers = foldRegOps(scopeEntryOps)(pre-entry-regs)
    -- where pre-entry-regs satisfied the old invariant. This information was lost when
    -- the loopEnter backward step matched the spec step (making atLoopStart true).
    -- A full proof requires either:
    -- (a) Strengthening MatchStates to track registers through the atRegOp phase, or
    -- (b) Combining loopEnter + stmtRegOpSteps + stmtRegOpDone into one atomic step.
    -- For now, we extract frame structure and handle what we can.
    obtain ⟨sf, srest, hSpecStack, hFrameCorr, hRestCorr, hCovS, hCovI, hNoRegOp⟩ :=
      pcCorr_stack_cons (hSim.pcCorr e) hStack
    have hRO : atRegOp frame := by
      simp only [atRegOp]
      obtain ⟨_, ⟨implBody, hBM, hBE⟩, _⟩ := hFrameCorr
      cases hk : frame.kind with
      | loop lid => rw [hk] at hBE; simp at hBE; rw [hBE] at hStmt
                    cases hsi : frame.stmtIdx with
                    | zero => simp
                    | succ n => rw [hsi] at hStmt; simp [List.getElem?_cons_succ] at hStmt
                                exact (bodyMatch_no_regOp hBM hStmt).elim
      | cond sid => rw [hk] at hBE; simp at hBE; rw [hBE] at hStmt
                    cases hsi : frame.stmtIdx with
                    | zero => simp
                    | succ n => rw [hsi] at hStmt; simp [List.getElem?_cons_succ] at hStmt
                                exact (bodyMatch_no_regOp hBM hStmt).elim
      | top => rw [hk] at hBE; rw [hBE] at hStmt; exact (bodyMatch_no_regOp hBM hStmt).elim
    have hALS_e : ∃ lid, atLoopStart is e lid := by
      simp only [atRegOp] at hRO
      cases hk : frame.kind with
      | loop lid => exact ⟨lid, frame, rest, hStack, Or.inl hk, by rw [hk] at hRO; exact hRO⟩
      | cond sid => exact ⟨sid, frame, rest, hStack, Or.inr hk, by rw [hk] at hRO; exact hRO⟩
      | top => simp [hk] at hRO
    exact { dataPathEq := hSim.dataPathEq, inflightEq := hSim.inflightEq, controlEq := hSim.controlEq
            semaInv := hSemaInvMono ss ss is _ rfl rfl hSim.semaInv
            monotoneRegInv := by
              intro e' lid' hNALS_all
              by_cases he : e' = e
              · subst he; exact hLoopRegsE lid'
              · exact hSim.monotoneRegInv e' lid' (fun ⟨fr, r, hS, hK, hI⟩ =>
                  hNALS_all ⟨fr, r, by simp [funUpdate, he]; exact hS, hK, hI⟩)
            tripRegInv := by
              intro e' lid' hNALS_all
              by_cases he : e' = e
              · subst he; exact hTripRegsE lid'
              · exact hSim.tripRegInv e' lid' (fun lid'' ⟨fr, r, hS, hK, hI⟩ =>
                  hNALS_all lid'' ⟨fr, r, by simp [funUpdate, he]; exact hS, hK, hI⟩)
            regOpFold := by
              intro e' frame' rest' ops' hStack' hStmt'
              by_cases he : e' = e
              · subst he; simp only [funUpdate, ite_true] at hStack'
                obtain ⟨rfl, rfl⟩ := List.cons.inj hStack'
                -- stmtIdx+1 is past the regOp at stmtIdx=0. body[1] is in the BodyMatch part.
                exfalso
                obtain ⟨_, ⟨implBody, hBM, hBE⟩, _⟩ := hFrameCorr
                have hSI0 : frame.stmtIdx = 0 := by simp only [atRegOp] at hRO; cases hk : frame.kind <;> simp [hk] at hRO <;> exact hRO
                cases hk : frame.kind with
                | loop lid => rw [hk] at hBE; simp at hBE; rw [hBE, hSI0] at hStmt'; simp [List.getElem?_cons_succ] at hStmt'; exact bodyMatch_no_regOp hBM hStmt'
                | cond sid => rw [hk] at hBE; simp at hBE; rw [hBE, hSI0] at hStmt'; simp [List.getElem?_cons_succ] at hStmt'; exact bodyMatch_no_regOp hBM hStmt'
                | top => simp [atRegOp, hk] at hRO
              · simp only [funUpdate, if_neg he] at hStack' ⊢
                exact hSim.regOpFold e' frame' rest' ops' hStack' hStmt'
            pcCorr := by
              intro e'; by_cases he : e' = e
              · subst he; simp only [funUpdate, ite_true]
                obtain ⟨hKC, ⟨ib, hBM, hBE⟩, hIC⟩ := hFrameCorr
                have ⟨hSfZ, hImfZ⟩ := hIC.1 hRO
                have hNewFC : FrameCorr ab sf ⟨frame.body, frame.stmtIdx + 1, frame.kind⟩ :=
                  ⟨hKC, ⟨ib, hBM, hBE⟩,
                   ⟨fun hRO' => by
                      simp only [atRegOp] at hRO'
                      cases hk : frame.kind <;> simp [hk] at hRO',
                    fun _ => by
                      rw [hImfZ]; cases hk : frame.kind with
                      | top => simp [atRegOp, hk] at hRO
                      | loop lid => simp; omega
                      | cond sid => simp; omega⟩⟩
                constructor
                · rw [hSpecStack]
                  exact StackCorr.cons _ _ srest rest hNewFC hRestCorr hCovS hCovI hNoRegOp
                · exact (hSim.pcCorr e').instrEq
              · simp only [funUpdate, if_neg he]; exact hSim.pcCorr e'
            waitRegChain := by
              intro e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
              by_cases he : e' = e
              · subst he; simp only [funUpdate_same] at hROI; omega
              · simp [funUpdate, if_neg he] at hStack' hInstr' hROI ⊢
                exact hSim.waitRegChain e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
            gateRegChain := by
              intro e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
              by_cases he : e' = e
              · subst he; simp only [funUpdate_same] at hROI; omega
              · simp [funUpdate, if_neg he] at hStack' hInstr' hROI ⊢
                exact hSim.gateRegChain e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI }


theorem case_issue (spec : Program) (impl : ImplProgram) (ab : AllocBase spec impl)
    (SemaInv : SpecState → ImplState → Prop)
    (hIssueDepSat : ∀ (e : EngineId) (instr : DataPathInstrId) (ss : SpecState) (is : ImplState),
      SemaInv ss is → SpecInv spec ss → AllocatableAt spec ss e instr →
      is.semaphores (impl.waitOf instr) ≥ is.registers e (ab.waitReg e) →
      is.registers e (ab.waitReg e) =
        foldRegOps (impl.regOps e instr) (fun r => if r = ab.waitReg e then 0 else is.registers e r) (ab.waitReg e) →
      (∀ plid,
        (fun r => if r = ab.waitReg e then 0 else is.registers e r) (ab.monotoneReg e plid) =
        totalEntries ss e plid) →
      (∀ lid, is.registers e (ab.tripReg e lid) = tripEntries ss e spec.body lid) →
      depSatisfied spec (spec.depGraph instr) instr ss e = true)
    (hSemaInvMono : SemaInvMono SemaInv)
    (innerOps : EngineId → DataPathInstrId → List RegOp)
    (hInnerOpsWf : InnerRegOpsWf innerOps ab)
    (hRegOpsEq : ∀ e i, impl.regOps e i = wrapWithGate spec (ab.gateReg e) (ab.waitReg e) ab.tripReg e i (innerOps e i))
    (e : EngineId) (ss : SpecState) (is : ImplState)
    (hSim : MatchStates spec impl ab SemaInv ss is)
    (hWf : Allocatable spec) (hSpecInv : SpecInv spec ss)
    (hUniq : UniqueScopeIds spec.body) (hUniqueInstr : UniqueInstrIds spec.engines spec.body)
    (hEngines : e ∈ spec.engines)
    (frame : ImplFrame) (imrest : List ImplFrame)
    (f : EngineId → List DataPathInstrId) (instr : DataPathInstrId)
    (hStack : (is.pc e).stack = frame :: imrest)
    (hStmt : frame.body[frame.stmtIdx]? = some (.block f))
    (hInstr : (f e)[(is.pc e).instrIdx]? = some instr)
    (hRegOpsDone : (is.pc e).regOpIdx = (impl.regOps e instr).length)
    (hWait : is.semaphores (impl.waitOf instr) ≥ is.registers e (impl.waitReg e instr))
    : let is' := { is with
        pc := funUpdate is.pc e
          { (is.pc e) with instrIdx := (is.pc e).instrIdx + 1, regOpIdx := 0 }
        inflight := funUpdate is.inflight e
          (is.inflight e ++ [(instr, Phase.issued)]) }
      (∃ ss', SpecStep spec e ss ss' ∧ MatchStates spec impl ab SemaInv ss' is')
    ∨ MatchStates spec impl ab SemaInv ss is' := by
    obtain ⟨sf, srest, hSpecStack, hFrameCorr, hRestCorr, hCovS, hCovI, hNoRegOp⟩ := pcCorr_stack_cons (hSim.pcCorr e) hStack
    have hNotRO := not_atRegOp_of_block hFrameCorr hStmt
    have hSpecStmt := frameCorr_block_stmt hFrameCorr hNotRO hStmt
    have hSpecInstr : (f e)[(ss.pc e).instrIdx]? = some instr := by rw [(hSim.pcCorr e).instrEq]; exact hInstr
    have hNotALS : ∀ lid, ¬ atLoopStart is e lid := not_atLoopStart_of_not_atRegOp hStack hNotRO
    have hWRE : impl.waitReg e instr = ab.waitReg e := ab.waitRegEq e instr
    have hROI : (is.pc e).regOpIdx > 0 := by
      rw [hRegOpsDone, hRegOpsEq]
      exact wrapWithGate_nonEmpty (hInnerOpsWf.nonEmpty e instr)
    have hChain := hSim.waitRegChain e frame imrest f instr hStack hStmt hInstr hROI
    have hWRV : is.registers e (ab.waitReg e) =
        foldRegOps (impl.regOps e instr) (fun r => if r = ab.waitReg e then 0 else is.registers e r) (ab.waitReg e) := by
      rw [hChain, hRegOpsDone, List.take_length]
    have hLoopRegs : ∀ plid,
        (fun r => if r = ab.waitReg e then 0 else is.registers e r) (ab.monotoneReg e plid) =
        totalEntries ss e plid := by
      intro plid; simp [Ne.symm (ab.noClob e plid)]; exact hSim.monotoneRegInv e plid (hNotALS plid)
    have hTripRegs : ∀ lid, is.registers e (ab.tripReg e lid) = tripEntries ss e spec.body lid :=
      fun lid => hSim.tripRegInv e lid hNotALS
    have hAllocatableInstr := allocatableAt_of_block_instr spec ss e instr hWf hSpecInv hUniq hUniqueInstr hEngines sf srest f hSpecStack hSpecStmt hSpecInstr
    have hDeps := hIssueDepSat e instr ss is hSim.semaInv hSpecInv hAllocatableInstr (hWRE ▸ hWait) (hWRE ▸ hWRV) hLoopRegs hTripRegs
    left; exact ⟨_, SpecStep.issue e ss hEngines sf srest f instr hSpecStack hSpecStmt hSpecInstr hDeps, {
      dataPathEq := hSim.dataPathEq
      inflightEq := by intro e'; simp only [funUpdate]; split <;> simp [hSim.inflightEq]
      controlEq := hSim.controlEq
      semaInv := hSemaInvMono ss _ is _ rfl rfl hSim.semaInv
      monotoneRegInv := monotoneRegInv_preserved_no_reg_no_hist (fun e plid hNotALS => hSim.monotoneRegInv e plid hNotALS) rfl (by simp)
        (atLoopStart_iff_instr_advance hStack hNotRO)
      tripRegInv := tripRegInv_preserved_no_reg_no_hist hSim.tripRegInv rfl (by simp)
        (atLoopStart_iff_instr_advance hStack hNotRO)
      regOpFold := by
        intro e' frame' rest' ops' hStack' hStmt'
        by_cases he : e' = e
        · subst he; simp only [funUpdate, ite_true] at hStack'
          rw [hStack] at hStack'; obtain ⟨rfl, rfl⟩ := List.cons.inj hStack'
          rw [hStmt] at hStmt'; simp at hStmt'
        · simp only [funUpdate, if_neg he] at hStack' ⊢
          exact hSim.regOpFold e' frame' rest' ops' hStack' hStmt'
      pcCorr := by
        intro e'; simp only [funUpdate]; split
        · next he => subst he; exact ⟨(hSim.pcCorr e').1, by simp [(hSim.pcCorr e').2]⟩
        · exact hSim.pcCorr e'
      waitRegChain := by
        intro e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
        by_cases he : e' = e <;> simp_all
        rw [← hRegOpsEq]
        exact hSim.waitRegChain e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
      gateRegChain := by
        intro e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
        by_cases he : e' = e <;> simp_all
        rw [← hRegOpsEq]
        exact hSim.gateRegChain e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
    }⟩

theorem case_commit (spec : Program) (impl : ImplProgram) (ab : AllocBase spec impl)
    (SemaInv : SpecState → ImplState → Prop)
    (hSemaInvMono : SemaInvMono SemaInv)
    (e : EngineId) (ss : SpecState) (is : ImplState)
    (hSim : MatchStates spec impl ab SemaInv ss is)
    (hEngines : e ∈ spec.engines)
    (idx : Nat) (instr : DataPathInstrId)
    (hIdx : (is.inflight e)[idx]? = some (instr, Phase.issued))
    : let is' := { is with
        dataPathState := impl.instrOp instr is.dataPathState
        inflight := funUpdate is.inflight e
          ((is.inflight e).set idx (instr, Phase.committed)) }
      (∃ ss', SpecStep spec e ss ss' ∧ MatchStates spec impl ab SemaInv ss' is')
    ∨ MatchStates spec impl ab SemaInv ss is' := by
    left
    have hSpecIdx : (ss.inflight e)[idx]? = some (instr, Phase.issued) := by rw [← hSim.inflightEq e]; exact hIdx
    exact ⟨_, SpecStep.commit e ss hEngines idx instr hSpecIdx, {
      dataPathEq := by rw [congrArg ProgramBase.instrOp ab.baseEq, hSim.dataPathEq]
      inflightEq := by intro e'; simp only [funUpdate]; split <;> [simp [hSim.inflightEq]; exact hSim.inflightEq e']
      controlEq := hSim.controlEq
      semaInv := hSemaInvMono ss _ is _ rfl rfl hSim.semaInv
      monotoneRegInv := hSim.monotoneRegInv
      tripRegInv := hSim.tripRegInv
      regOpFold := hSim.regOpFold
      pcCorr := hSim.pcCorr
      waitRegChain := hSim.waitRegChain
      gateRegChain := hSim.gateRegChain
    }⟩

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
    (hEngines : e ∈ spec.engines)
    (instr : DataPathInstrId) (inflightRest : List (DataPathInstrId × Phase))
    (hHead : is.inflight e = (instr, Phase.committed) :: inflightRest)
    : let is' := { is with
        inflight := funUpdate is.inflight e inflightRest
        semaphores := funUpdate is.semaphores (impl.updateOf instr)
          (is.semaphores (impl.updateOf instr) + 1) }
      (∃ ss', SpecStep spec e ss ss' ∧ MatchStates spec impl ab SemaInv ss' is')
    ∨ MatchStates spec impl ab SemaInv ss is' := by
    left
    have hSpecHead : ss.inflight e = (instr, Phase.committed) :: inflightRest := by rw [← hSim.inflightEq e]; exact hHead
    exact ⟨_, SpecStep.retire e ss hEngines instr inflightRest hSpecHead, {
      dataPathEq := hSim.dataPathEq
      inflightEq := by intro e'; simp only [funUpdate]; split <;> [simp; exact hSim.inflightEq e']
      controlEq := hSim.controlEq
      semaInv := hRetireSema e instr inflightRest ss is hSim.semaInv hSpecHead
      monotoneRegInv := hSim.monotoneRegInv
      tripRegInv := hSim.tripRegInv
      regOpFold := hSim.regOpFold
      pcCorr := hSim.pcCorr
      waitRegChain := hSim.waitRegChain
      gateRegChain := hSim.gateRegChain
    }⟩

theorem case_blockDone (spec : Program) (impl : ImplProgram) (ab : AllocBase spec impl)
    (SemaInv : SpecState → ImplState → Prop)
    (hSemaInvMono : SemaInvMono SemaInv)
    (e : EngineId) (ss : SpecState) (is : ImplState)
    (hSim : MatchStates spec impl ab SemaInv ss is)
    (hEngines : e ∈ spec.engines)
    (frame : ImplFrame) (rest : List ImplFrame)
    (f : EngineId → List DataPathInstrId)
    (hStack : (is.pc e).stack = frame :: rest)
    (hStmt : frame.body[frame.stmtIdx]? = some (.block f))
    (hDone : (is.pc e).instrIdx = (f e).length)
    : let is' := { is with
        pc := funUpdate is.pc e
          { stack := ⟨frame.body, frame.stmtIdx + 1, frame.kind⟩ :: rest,
            instrIdx := 0, regOpIdx := 0, stmtRegOpIdx := 0 } }
      (∃ ss', SpecStep spec e ss ss' ∧ MatchStates spec impl ab SemaInv ss' is')
    ∨ MatchStates spec impl ab SemaInv ss is' := by
    left
    obtain ⟨sf, srest, hSpecStack, hFrameCorr, hRestCorr, hCovS, hCovI, hNoRegOp⟩ := pcCorr_stack_cons (hSim.pcCorr e) hStack
    have hNotRO := not_atRegOp_of_block hFrameCorr hStmt
    have hSpecStmt := frameCorr_block_stmt hFrameCorr hNotRO hStmt
    have hSpecDone : (ss.pc e).instrIdx = (f e).length := by rw [(hSim.pcCorr e).instrEq]; exact hDone
    have hNewFC := frameCorr_advance_parent hFrameCorr hNotRO
      (Nat.lt_of_not_le (fun h => by simp [List.getElem?_eq_none h] at hSpecStmt))
      (Nat.lt_of_not_le (fun h => by simp [List.getElem?_eq_none h] at hStmt))
    exact ⟨_, SpecStep.blockDone e ss hEngines sf srest f hSpecStack hSpecStmt hSpecDone,
      MatchStates.of_funUpdate_pc hSim hSemaInvMono _ _
        ⟨StackCorr.cons _ _ srest rest hNewFC hRestCorr hCovS hCovI hNoRegOp, by simp⟩
        rfl (atLoopStart_iff_advance_parent hStack hNotRO)
        (fun _ _ _ hStack' hStmt' => by
          simp at hStack'; obtain ⟨rfl, rfl⟩ := hStack'
          exact frameCorr_no_regOp hFrameCorr hNotRO (Nat.le_succ _) hStmt')⟩

theorem case_loopEnter (spec : Program) (impl : ImplProgram) (ab : AllocBase spec impl)
    (SemaInv : SpecState → ImplState → Prop)
    (hSemaInvMono : SemaInvMono SemaInv)
    (e : EngineId) (ss : SpecState) (is : ImplState)
    (hSim : MatchStates spec impl ab SemaInv ss is)
    (hSpecInv : SpecInv spec ss) (hUniq : UniqueScopeIds spec.body)
    (hEngines : e ∈ spec.engines)
    (frame : ImplFrame) (rest : List ImplFrame)
    (lid : ScopeId) (loopBody : List ImplStmt)
    (hStack : (is.pc e).stack = frame :: rest)
    (hStmt : frame.body[frame.stmtIdx]? = some (.loop lid loopBody))
    (hGuard : impl.guard e lid (is.controlState e) = true)
    (hPIO : ∀ parent, scopeParent spec.body lid = some parent →
      parent ∈ enclosingLoopsFromStack (ss.pc e).stack)
    (hNSP : ∀ parent, scopeParent spec.body lid = some parent → parent ≠ lid)
    : let is' := { is with
        pc := funUpdate is.pc e
          { stack := ⟨loopBody, 0, .loop lid⟩ :: frame :: rest,
            instrIdx := 0, regOpIdx := 0, stmtRegOpIdx := 0 }
        controlState := funUpdate is.controlState e
          (impl.controlOp e lid (is.controlState e)) }
      (∃ ss', SpecStep spec e ss ss' ∧ MatchStates spec impl ab SemaInv ss' is')
    ∨ MatchStates spec impl ab SemaInv ss is' := by
    left
    obtain ⟨sf, srest, hSpecStack, hFrameCorr, hRestCorr, hCovS, hCovI, hNoRegOp⟩ := pcCorr_stack_cons (hSim.pcCorr e) hStack
    have hParentInOuter : ∀ parent, scopeParent spec.body lid = some parent →
        parent ∈ enclosingLoopsFromStack (sf :: srest) := hSpecStack ▸ hPIO
    have hNotSelfParent : ∀ parent, scopeParent spec.body lid = some parent → parent ≠ lid := hNSP
    have hNotRO : ¬ atRegOp frame := by
      intro hAR; simp [atRegOp] at hAR
      cases hk : frame.kind <;> simp [hk] at hAR <;>
        (rw [hAR] at hStmt; obtain ⟨ib, hBM, hBE⟩ := hFrameCorr.bodyCorr; rw [hk] at hBE; rw [hBE] at hStmt; simp at hStmt)
    obtain ⟨specLoopBody, implInner, hSpecStmt, hInnerMatch, hLoopBodyEq⟩ := frameCorr_loop_stmt hFrameCorr hNotRO hStmt
    have hSpecGuard := spec_guard_of_impl ab.baseEq (hSim.controlEq e) hGuard
    exact ⟨{ ss with
      pc := funUpdate ss.pc e { stack := ⟨specLoopBody, 0, .loop lid⟩ :: sf :: srest, instrIdx := 0 }
      controlState := funUpdate ss.controlState e (spec.controlOp e lid (ss.controlState e))
      scopeEntryHistory := incrScopeEntryHistory ss e lid (enclosingLoopsFromStack (sf :: srest))
    }, SpecStep.loopEnter e ss hEngines sf srest lid specLoopBody hSpecStack hSpecStmt hSpecGuard,
    by have hSMP := hSpecInv.wellFormedPC e; rw [hSpecStack] at hSMP
       have hUniqBody := smp_uniqueScopeIds hSMP hUniq sf (List.Mem.head _)
       have hSidNotChild : lid ∉ directChildScopes specLoopBody := by
         have h := uniqueScopeIds_of_getElem hSpecStmt hUniqBody
         cases h with | loop _ _ _ hNB _ _ _ _ => exact fun hC => hNB (directChildScopes_mem_scopeIdsOf _ _ hC)
       have hLoopBOf : scopeBodyOf spec.body lid = some specLoopBody := by
         have hLocal := scopeBodyOf_of_getElem hSpecStmt hUniqBody
         exact smp_scopeBodyOf_agree hSMP hUniq sf (List.Mem.head _) lid
           (mem_scopeIdsOf_of_getElem hSpecStmt (by simp [scopeIdsOf])) |>.symm ▸ hLocal
       have hDirectChild : ∀ lid', lid' ∈ directChildScopes specLoopBody → lid' ≠ lid → scopeParent spec.body lid' = some lid := by
         intro lid' hChild hNeLid
         have hLidInSB := directChildScopes_mem_scopeIdsOf _ _ hChild
         have hUniqSB : UniqueScopeIds specLoopBody := by
           have h := uniqueScopeIds_of_getElem hSpecStmt hUniqBody
           cases h with | loop _ _ _ _ _ _ hU _ => exact hU
         have hGoInner := directChild_scopeParent_go specLoopBody lid' lid hChild hUniqSB
         have hGoLocal := scopeParent_go_lift_loop (container := sf.kind.loopId?) hSpecStmt hUniqBody hGoInner hLidInSB
         have hMem := mem_scopeIdsOf_of_getElem hSpecStmt (by simp [scopeIdsOf]; right; exact hLidInSB)
         unfold scopeParent; exact smp_lift_scopeParent_go hSMP hUniq sf srest rfl hGoLocal hMem
       bwd_loop_enter_matchstates_loop loopBody specLoopBody lid implInner hInnerMatch hLoopBodyEq⟩

theorem case_loopSkip (spec : Program) (impl : ImplProgram) (ab : AllocBase spec impl)
    (SemaInv : SpecState → ImplState → Prop)
    (hSemaInvMono : SemaInvMono SemaInv)
    (e : EngineId) (ss : SpecState) (is : ImplState)
    (hSim : MatchStates spec impl ab SemaInv ss is)
    (hEngines : e ∈ spec.engines)
    (frame : ImplFrame) (rest : List ImplFrame)
    (lid : ScopeId) (loopBody : List ImplStmt)
    (hStack : (is.pc e).stack = frame :: rest)
    (hStmt : frame.body[frame.stmtIdx]? = some (.loop lid loopBody))
    (hGuard : impl.guard e lid (is.controlState e) = false)
    : let is' := { is with
        pc := funUpdate is.pc e
          { stack := ⟨frame.body, frame.stmtIdx + 1, frame.kind⟩ :: rest,
            instrIdx := 0, regOpIdx := 0, stmtRegOpIdx := 0 } }
      (∃ ss', SpecStep spec e ss ss' ∧ MatchStates spec impl ab SemaInv ss' is')
    ∨ MatchStates spec impl ab SemaInv ss is' := by
    left
    obtain ⟨sf, srest, hSpecStack, hFrameCorr, hRestCorr, hCovS, hCovI, hNoRegOp⟩ := pcCorr_stack_cons (hSim.pcCorr e) hStack
    have hNotRO : ¬ atRegOp frame := by
      intro hAR; simp [atRegOp] at hAR
      cases hk : frame.kind <;> simp [hk] at hAR <;>
        (rw [hAR] at hStmt; obtain ⟨ib, hBM, hBE⟩ := hFrameCorr.bodyCorr; rw [hk] at hBE; rw [hBE] at hStmt; simp at hStmt)
    obtain ⟨specLoopBody, _, hSpecStmt, _, _⟩ := frameCorr_loop_stmt hFrameCorr hNotRO hStmt
    have hSpecGuard := spec_guard_of_impl ab.baseEq (hSim.controlEq e) hGuard
    have hNewFC := frameCorr_advance_parent hFrameCorr hNotRO
      (Nat.lt_of_not_le (fun h => by simp [List.getElem?_eq_none h] at hSpecStmt))
      (Nat.lt_of_not_le (fun h => by simp [List.getElem?_eq_none h] at hStmt))
    exact ⟨_, SpecStep.loopSkip e ss hEngines sf srest lid specLoopBody hSpecStack hSpecStmt hSpecGuard,
      MatchStates.of_funUpdate_pc hSim hSemaInvMono _ _
        ⟨StackCorr.cons _ _ srest rest hNewFC hRestCorr hCovS hCovI hNoRegOp, by simp⟩
        rfl (atLoopStart_iff_advance_parent hStack hNotRO)
        (fun _ _ _ hStack' hStmt' => by
          simp at hStack'; obtain ⟨rfl, rfl⟩ := hStack'
          exact frameCorr_no_regOp hFrameCorr hNotRO (Nat.le_succ _) hStmt')⟩

theorem case_loopBack (spec : Program) (impl : ImplProgram) (ab : AllocBase spec impl)
    (SemaInv : SpecState → ImplState → Prop)
    (hSemaInvMono : SemaInvMono SemaInv)
    (e : EngineId) (ss : SpecState) (is : ImplState)
    (hSim : MatchStates spec impl ab SemaInv ss is)
    (hEngines : e ∈ spec.engines)
    (frame parent : ImplFrame) (rest : List ImplFrame)
    (lid : ScopeId)
    (hStack : (is.pc e).stack = frame :: parent :: rest)
    (hKind : frame.kind = .loop lid)
    (hEnd : frame.stmtIdx = frame.body.length)
    : let is' := { is with
        pc := funUpdate is.pc e
          { stack := parent :: rest, instrIdx := 0, regOpIdx := 0, stmtRegOpIdx := 0 } }
      (∃ ss', SpecStep spec e ss ss' ∧ MatchStates spec impl ab SemaInv ss' is')
    ∨ MatchStates spec impl ab SemaInv ss is' := by
    left
    obtain ⟨sf, srest', hSpecStack, hFrameCorr, hRestCorr', hCovS', hCovI', hNoRegOp'⟩ := pcCorr_stack_cons (hSim.pcCorr e) hStack
    obtain ⟨sparent, srest, hSrest', hParentCorr, hRestCorr, hCovS2, hCovI2, hNoRegOp2⟩ := stackCorr_cons_inv hRestCorr'
    have hSpecKind : sf.kind = .loop lid := by
      have hKC := hFrameCorr.kindCorr; rw [hKind] at hKC
      cases hsk : sf.kind <;> simp [frameKindCorr, hsk] at hKC; subst hKC; rfl
    have hNotRO := not_atRegOp_of_loop_end hFrameCorr (Or.inl ⟨_, hKind⟩) hEnd
    have hSpecEnd := specEnd_of_loop_end hFrameCorr (Or.inl ⟨_, hKind⟩) hEnd hNotRO
    have hParentNotRO := hNoRegOp' parent rest rfl
    exact ⟨{ ss with pc := funUpdate ss.pc e { stack := sparent :: srest, instrIdx := 0 }
    }, by rw [hSrest'] at hSpecStack; exact SpecStep.loopBack e ss hEngines sf sparent srest lid hSpecStack hSpecKind hSpecEnd,
      MatchStates.of_funUpdate_pc hSim hSemaInvMono _ _
        (by rw [hSrest'] at hRestCorr'; exact ⟨hRestCorr', by simp⟩)
        rfl (monotoneRegInv_loop_pop_to_parent hStack hNotRO hParentNotRO)
        (fun _ _ _ hStack' hStmt' => by
          simp at hStack'; obtain ⟨rfl, rfl⟩ := hStack'
          exact frameCorr_no_regOp hParentCorr hParentNotRO (Nat.le_refl _) hStmt')⟩

theorem case_condTrue (spec : Program) (impl : ImplProgram) (ab : AllocBase spec impl)
    (SemaInv : SpecState → ImplState → Prop)
    (hSemaInvMono : SemaInvMono SemaInv)
    (e : EngineId) (ss : SpecState) (is : ImplState)
    (hSim : MatchStates spec impl ab SemaInv ss is)
    (hSpecInv : SpecInv spec ss) (hUniq : UniqueScopeIds spec.body)
    (hEngines : e ∈ spec.engines)
    (frame : ImplFrame) (rest : List ImplFrame)
    (thenId elseId : ScopeId) (thenBody elseBody : List ImplStmt)
    (hStack : (is.pc e).stack = frame :: rest)
    (hStmt : frame.body[frame.stmtIdx]? = some (.cond thenId elseId thenBody elseBody))
    (hGuard : impl.guard e thenId (is.controlState e) = true)
    (hPIO : ∀ parent, scopeParent spec.body thenId = some parent →
      parent ∈ enclosingLoopsFromStack (ss.pc e).stack)
    (hNSP : ∀ parent, scopeParent spec.body thenId = some parent → parent ≠ thenId)
    : let is' := { is with
        pc := funUpdate is.pc e
          { stack := ⟨thenBody, 0, .cond thenId⟩ :: frame :: rest,
            instrIdx := 0, regOpIdx := 0, stmtRegOpIdx := 0 }
        controlState := funUpdate is.controlState e
          (impl.controlOp e thenId (is.controlState e)) }
      (∃ ss', SpecStep spec e ss ss' ∧ MatchStates spec impl ab SemaInv ss' is')
    ∨ MatchStates spec impl ab SemaInv ss is' := by
    left
    obtain ⟨sf, srest, hSpecStack, hFrameCorr, hRestCorr, hCovS, hCovI, hNoRegOp⟩ := pcCorr_stack_cons (hSim.pcCorr e) hStack
    have hParentInOuter : ∀ parent, scopeParent spec.body thenId = some parent →
        parent ∈ enclosingLoopsFromStack (sf :: srest) := hSpecStack ▸ hPIO
    have hNotSelfParent : ∀ parent, scopeParent spec.body thenId = some parent → parent ≠ thenId := hNSP
    have hNotRO : ¬ atRegOp frame := by
      intro hAR; simp [atRegOp] at hAR
      cases hk : frame.kind <;> simp [hk] at hAR <;>
        (rw [hAR] at hStmt; obtain ⟨ib, hBM, hBE⟩ := hFrameCorr.bodyCorr; rw [hk] at hBE; rw [hBE] at hStmt; simp at hStmt)
    obtain ⟨specThen, specElse, implThenInner, implElseInner, hSpecStmt, hThenMatch, hElseMatch, hThenBodyEq, hElseBodyEq⟩ := frameCorr_cond_stmt hFrameCorr hNotRO hStmt
    have hSpecGuard := spec_guard_of_impl ab.baseEq (hSim.controlEq e) hGuard
    exact ⟨{ ss with
      pc := funUpdate ss.pc e { stack := ⟨specThen, 0, .cond thenId⟩ :: sf :: srest, instrIdx := 0 }
      controlState := funUpdate ss.controlState e (spec.controlOp e thenId (ss.controlState e))
      scopeEntryHistory := incrScopeEntryHistory ss e thenId (enclosingLoopsFromStack (sf :: srest))
    }, SpecStep.condTrue e ss hEngines sf srest thenId elseId specThen specElse hSpecStack hSpecStmt hSpecGuard,
    by have hSMP := hSpecInv.wellFormedPC e; rw [hSpecStack] at hSMP
       have hUniqBody := smp_uniqueScopeIds hSMP hUniq sf (List.Mem.head _)
       have hSidNotChild : thenId ∉ directChildScopes specThen := by
         have h := uniqueScopeIds_of_getElem hSpecStmt hUniqBody
         cases h with | cond _ _ _ _ _ _ hTnTb _ _ _ _ _ _ _ _ _ _ => exact fun hC => hTnTb (directChildScopes_mem_scopeIdsOf _ _ hC)
       have hLoopBOf : scopeBodyOf spec.body thenId = some specThen := by
         have hLocal := scopeBodyOf_of_getElem_condTrue hSpecStmt hUniqBody
         exact smp_scopeBodyOf_agree hSMP hUniq sf (List.Mem.head _) thenId
           (mem_scopeIdsOf_of_getElem hSpecStmt (by simp [scopeIdsOf])) |>.symm ▸ hLocal
       have hDirectChild : ∀ lid', lid' ∈ directChildScopes specThen → lid' ≠ thenId → scopeParent spec.body lid' = some thenId := by
         intro lid' hChild hNeLid
         have hLidInSB := directChildScopes_mem_scopeIdsOf _ _ hChild
         have hUniqSB : UniqueScopeIds specThen := by
           have h := uniqueScopeIds_of_getElem hSpecStmt hUniqBody
           cases h with | cond _ _ _ _ _ _ _ _ _ _ _ _ _ _ hU _ _ => exact hU
         have hGoInner := directChild_scopeParent_go specThen lid' thenId hChild hUniqSB
         have hGoLocal := scopeParent_go_lift_cond_then (container := sf.kind.loopId?) hSpecStmt hUniqBody hGoInner hLidInSB
         have hMem := mem_scopeIdsOf_of_getElem hSpecStmt (by simp [scopeIdsOf]; right; right; left; exact hLidInSB)
         unfold scopeParent; exact smp_lift_scopeParent_go hSMP hUniq sf srest rfl hGoLocal hMem
       bwd_loop_enter_matchstates_cond thenBody specThen thenId implThenInner hThenMatch hThenBodyEq⟩

theorem case_condFalse (spec : Program) (impl : ImplProgram) (ab : AllocBase spec impl)
    (SemaInv : SpecState → ImplState → Prop)
    (hSemaInvMono : SemaInvMono SemaInv)
    (e : EngineId) (ss : SpecState) (is : ImplState)
    (hSim : MatchStates spec impl ab SemaInv ss is)
    (hSpecInv : SpecInv spec ss) (hUniq : UniqueScopeIds spec.body)
    (hEngines : e ∈ spec.engines)
    (frame : ImplFrame) (rest : List ImplFrame)
    (thenId elseId : ScopeId) (thenBody elseBody : List ImplStmt)
    (hStack : (is.pc e).stack = frame :: rest)
    (hStmt : frame.body[frame.stmtIdx]? = some (.cond thenId elseId thenBody elseBody))
    (hGuard : impl.guard e thenId (is.controlState e) = false)
    (hPIO : ∀ parent, scopeParent spec.body elseId = some parent →
      parent ∈ enclosingLoopsFromStack (ss.pc e).stack)
    (hNSP : ∀ parent, scopeParent spec.body elseId = some parent → parent ≠ elseId)
    : let is' := { is with
        pc := funUpdate is.pc e
          { stack := ⟨elseBody, 0, .cond elseId⟩ :: frame :: rest,
            instrIdx := 0, regOpIdx := 0, stmtRegOpIdx := 0 }
        controlState := funUpdate is.controlState e
          (impl.controlOp e elseId (is.controlState e)) }
      (∃ ss', SpecStep spec e ss ss' ∧ MatchStates spec impl ab SemaInv ss' is')
    ∨ MatchStates spec impl ab SemaInv ss is' := by
    left
    obtain ⟨sf, srest, hSpecStack, hFrameCorr, hRestCorr, hCovS, hCovI, hNoRegOp⟩ := pcCorr_stack_cons (hSim.pcCorr e) hStack
    have hParentInOuter : ∀ parent, scopeParent spec.body elseId = some parent →
        parent ∈ enclosingLoopsFromStack (sf :: srest) := hSpecStack ▸ hPIO
    have hNotSelfParent : ∀ parent, scopeParent spec.body elseId = some parent → parent ≠ elseId := hNSP
    have hNotRO : ¬ atRegOp frame := by
      intro hAR; simp [atRegOp] at hAR
      cases hk : frame.kind <;> simp [hk] at hAR <;>
        (rw [hAR] at hStmt; obtain ⟨ib, hBM, hBE⟩ := hFrameCorr.bodyCorr; rw [hk] at hBE; rw [hBE] at hStmt; simp at hStmt)
    obtain ⟨specThen, specElse, implThenInner, implElseInner, hSpecStmt, hThenMatch, hElseMatch, hThenBodyEq, hElseBodyEq⟩ := frameCorr_cond_stmt hFrameCorr hNotRO hStmt
    have hSpecGuard := spec_guard_of_impl ab.baseEq (hSim.controlEq e) hGuard
    exact ⟨{ ss with
      pc := funUpdate ss.pc e { stack := ⟨specElse, 0, .cond elseId⟩ :: sf :: srest, instrIdx := 0 }
      controlState := funUpdate ss.controlState e (spec.controlOp e elseId (ss.controlState e))
      scopeEntryHistory := incrScopeEntryHistory ss e elseId (enclosingLoopsFromStack (sf :: srest))
    }, SpecStep.condFalse e ss hEngines sf srest thenId elseId specThen specElse hSpecStack hSpecStmt hSpecGuard,
    by have hSMP := hSpecInv.wellFormedPC e; rw [hSpecStack] at hSMP
       have hUniqBody := smp_uniqueScopeIds hSMP hUniq sf (List.Mem.head _)
       have hSidNotChild : elseId ∉ directChildScopes specElse := by
         have h := uniqueScopeIds_of_getElem hSpecStmt hUniqBody
         cases h with | cond _ _ _ _ _ _ _ _ _ _ hEnEb _ _ _ _ _ _ => exact fun hC => hEnEb (directChildScopes_mem_scopeIdsOf _ _ hC)
       have hLoopBOf : scopeBodyOf spec.body elseId = some specElse := by
         have hLocal := scopeBodyOf_of_getElem_condFalse hSpecStmt hUniqBody
         have hElseInBody : elseId ∈ scopeIdsOf sf.body :=
           mem_scopeIdsOf_of_getElem hSpecStmt (by simp [scopeIdsOf])
         exact smp_scopeBodyOf_agree hSMP hUniq sf (List.Mem.head _) elseId hElseInBody |>.symm ▸ hLocal
       have hDirectChild : ∀ lid', lid' ∈ directChildScopes specElse → lid' ≠ elseId → scopeParent spec.body lid' = some elseId := by
         intro lid' hChild hNeLid
         have hLidInSB := directChildScopes_mem_scopeIdsOf _ _ hChild
         have hUniqSB : UniqueScopeIds specElse := by
           have h := uniqueScopeIds_of_getElem hSpecStmt hUniqBody
           cases h with | cond _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hU _ => exact hU
         have hGoInner := directChild_scopeParent_go specElse lid' elseId hChild hUniqSB
         have hGoLocal := scopeParent_go_lift_cond_else (container := sf.kind.loopId?) hSpecStmt hUniqBody hGoInner hLidInSB
         have hMem := mem_scopeIdsOf_of_getElem hSpecStmt (by simp [scopeIdsOf]; right; right; right; exact hLidInSB)
         unfold scopeParent; exact smp_lift_scopeParent_go hSMP hUniq sf srest rfl hGoLocal hMem
       bwd_loop_enter_matchstates_cond elseBody specElse elseId implElseInner hElseMatch hElseBodyEq⟩

theorem case_condDone (spec : Program) (impl : ImplProgram) (ab : AllocBase spec impl)
    (SemaInv : SpecState → ImplState → Prop)
    (hSemaInvMono : SemaInvMono SemaInv)
    (e : EngineId) (ss : SpecState) (is : ImplState)
    (hSim : MatchStates spec impl ab SemaInv ss is)
    (hEngines : e ∈ spec.engines)
    (frame parent : ImplFrame) (rest : List ImplFrame)
    (sid : ScopeId)
    (hStack : (is.pc e).stack = frame :: parent :: rest)
    (hKind : frame.kind = .cond sid)
    (hEnd : frame.stmtIdx = frame.body.length)
    : let is' := { is with
        pc := funUpdate is.pc e
          { stack := ⟨parent.body, parent.stmtIdx + 1, parent.kind⟩ :: rest,
            instrIdx := 0, regOpIdx := 0, stmtRegOpIdx := 0 } }
      (∃ ss', SpecStep spec e ss ss' ∧ MatchStates spec impl ab SemaInv ss' is')
    ∨ MatchStates spec impl ab SemaInv ss is' := by
    left
    obtain ⟨sf, srest', hSpecStack, hFrameCorr, hRestCorr', hCovS', hCovI', hNoRegOp'⟩ := pcCorr_stack_cons (hSim.pcCorr e) hStack
    obtain ⟨sparent, srest, hSrest', hParentCorr, hRestCorr, hCovS2, hCovI2, hNoRegOp2⟩ := stackCorr_cons_inv hRestCorr'
    have hSpecKind : sf.kind = .cond sid := by
      have hKC := hFrameCorr.kindCorr; rw [hKind] at hKC
      cases hsk : sf.kind <;> simp [frameKindCorr, hsk] at hKC; subst hKC; rfl
    have hNotRO := not_atRegOp_of_loop_end hFrameCorr (Or.inr ⟨_, hKind⟩) hEnd
    have hSpecEnd := specEnd_of_loop_end hFrameCorr (Or.inr ⟨_, hKind⟩) hEnd hNotRO
    have hParentNotRO := hNoRegOp' parent rest rfl
    have hNewFC := frameCorr_advance_parent hParentCorr hParentNotRO
      (hCovS' sparent srest hSrest') (hCovI' parent rest rfl)
    exact ⟨_, by rw [hSrest'] at hSpecStack; exact SpecStep.condDone e ss hEngines sf sparent srest sid hSpecStack hSpecKind hSpecEnd,
      MatchStates.of_funUpdate_pc hSim hSemaInvMono _ _
        ⟨StackCorr.cons _ _ srest rest hNewFC hRestCorr hCovS2 hCovI2 hNoRegOp2, by simp⟩
        rfl (by
          intro e' lid'; constructor
          · intro ⟨fr, r, hS, hK, hI⟩; by_cases he : e' = e
            · subst he; simp only [funUpdate, ite_true] at hS; obtain ⟨rfl, rfl⟩ := hS; simp at hI
            · exact ⟨fr, r, by simp [funUpdate, he] at hS; exact hS, hK, hI⟩
          · intro h; by_cases he : e' = e
            · subst he; exact absurd h (not_atLoopStart_of_not_atRegOp hStack hNotRO lid')
            · obtain ⟨fr, r, hS, hK, hI⟩ := h
              exact ⟨fr, r, by simp [funUpdate, he]; exact hS, hK, hI⟩)
        (fun _ _ _ hStack' hStmt' => by
          simp at hStack'; obtain ⟨rfl, rfl⟩ := hStack'
          exact frameCorr_no_regOp hParentCorr hParentNotRO (Nat.le_succ _) hStmt')⟩

theorem case_issue_depSat (spec : Program) (impl : ImplProgram) (ab : AllocBase spec impl)
    (SemaInv : SpecState → ImplState → Prop)
    (hSemaInvMono : SemaInvMono SemaInv)
    (e : EngineId) (ss : SpecState) (is : ImplState)
    (hSim : MatchStates spec impl ab SemaInv ss is)
    (_hSpecInv : SpecInv spec ss)
    (_hUniq : UniqueScopeIds spec.body) (_hUniqueInstr : UniqueInstrIds spec.engines spec.body)
    (hEngines : e ∈ spec.engines)
    (frame : ImplFrame) (imrest : List ImplFrame)
    (f : EngineId → List DataPathInstrId) (instr : DataPathInstrId)
    (hStack : (is.pc e).stack = frame :: imrest)
    (hStmt : frame.body[frame.stmtIdx]? = some (.block f))
    (hInstr : (f e)[(is.pc e).instrIdx]? = some instr)
    (hRegOpsDone : (is.pc e).regOpIdx = (impl.regOps e instr).length)
    (hWait : is.semaphores (impl.waitOf instr) ≥ is.registers e (impl.waitReg e instr))
    (hDeps : depSatisfied spec (spec.depGraph instr) instr ss e = true)
    : let is' := { is with
        pc := funUpdate is.pc e
          { (is.pc e) with instrIdx := (is.pc e).instrIdx + 1, regOpIdx := 0 }
        inflight := funUpdate is.inflight e
          (is.inflight e ++ [(instr, Phase.issued)]) }
      (∃ ss', SpecStep spec e ss ss' ∧ MatchStates spec impl ab SemaInv ss' is')
    ∨ MatchStates spec impl ab SemaInv ss is' := by
    left
    obtain ⟨sf, srest, hSpecStack, hFrameCorr, hRestCorr, hCovS, hCovI, hNoRegOp⟩ := pcCorr_stack_cons (hSim.pcCorr e) hStack
    have hNotRO := not_atRegOp_of_block hFrameCorr hStmt
    have hSpecStmt := frameCorr_block_stmt hFrameCorr hNotRO hStmt
    have hSpecInstr : (f e)[(ss.pc e).instrIdx]? = some instr := by rw [(hSim.pcCorr e).instrEq]; exact hInstr
    exact ⟨_, SpecStep.issue e ss hEngines sf srest f instr hSpecStack hSpecStmt hSpecInstr hDeps, {
      dataPathEq := hSim.dataPathEq
      inflightEq := by intro e'; simp only [funUpdate]; split <;> simp [hSim.inflightEq]
      controlEq := hSim.controlEq
      semaInv := hSemaInvMono ss _ is _ rfl rfl hSim.semaInv
      monotoneRegInv := monotoneRegInv_preserved_no_reg_no_hist (fun e plid hNotALS => hSim.monotoneRegInv e plid hNotALS) rfl (by simp)
        (atLoopStart_iff_instr_advance hStack hNotRO)
      tripRegInv := tripRegInv_preserved_no_reg_no_hist hSim.tripRegInv rfl (by simp)
        (atLoopStart_iff_instr_advance hStack hNotRO)
      regOpFold := by
        intro e' frame' rest' ops' hStack' hStmt'
        by_cases he : e' = e
        · subst he; simp only [funUpdate, ite_true] at hStack'
          rw [hStack] at hStack'; obtain ⟨rfl, rfl⟩ := List.cons.inj hStack'
          rw [hStmt] at hStmt'; simp at hStmt'
        · simp only [funUpdate, if_neg he] at hStack' ⊢
          exact hSim.regOpFold e' frame' rest' ops' hStack' hStmt'
      pcCorr := by
        intro e'; simp only [funUpdate]; split
        · next he => subst he; exact ⟨(hSim.pcCorr e').1, by simp [(hSim.pcCorr e').2]⟩
        · exact hSim.pcCorr e'
      waitRegChain := by
        intro e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
        by_cases he : e' = e <;> simp_all
        exact hSim.waitRegChain e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
      gateRegChain := by
        intro e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
        by_cases he : e' = e <;> simp_all
        exact hSim.gateRegChain e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
    }⟩

theorem case_retire_semaInv (spec : Program) (impl : ImplProgram) (ab : AllocBase spec impl)
    (SemaInv : SpecState → ImplState → Prop)
    (e : EngineId) (ss : SpecState) (is : ImplState)
    (hSim : MatchStates spec impl ab SemaInv ss is)
    (hEngines : e ∈ spec.engines)
    (instr : DataPathInstrId) (inflightRest : List (DataPathInstrId × Phase))
    (hHead : is.inflight e = (instr, Phase.committed) :: inflightRest)
    (hSemaPost : SemaInv
      (specRetireUpdate ss e instr inflightRest)
      { is with inflight := funUpdate is.inflight e inflightRest,
                semaphores := funUpdate is.semaphores (impl.updateOf instr) (is.semaphores (impl.updateOf instr) + 1) })
    : let is' := { is with
        inflight := funUpdate is.inflight e inflightRest
        semaphores := funUpdate is.semaphores (impl.updateOf instr)
          (is.semaphores (impl.updateOf instr) + 1) }
      (∃ ss', SpecStep spec e ss ss' ∧ MatchStates spec impl ab SemaInv ss' is')
    ∨ MatchStates spec impl ab SemaInv ss is' := by
    left
    have hSpecHead : ss.inflight e = (instr, Phase.committed) :: inflightRest := by rw [← hSim.inflightEq e]; exact hHead
    exact ⟨_, SpecStep.retire e ss hEngines instr inflightRest hSpecHead, {
      dataPathEq := hSim.dataPathEq
      inflightEq := by intro e'; simp only [funUpdate]; split <;> [simp; exact hSim.inflightEq e']
      controlEq := hSim.controlEq
      semaInv := hSemaPost
      monotoneRegInv := hSim.monotoneRegInv
      tripRegInv := hSim.tripRegInv
      regOpFold := hSim.regOpFold
      pcCorr := hSim.pcCorr
      waitRegChain := hSim.waitRegChain
      gateRegChain := hSim.gateRegChain
    }⟩

end BackwardSim

theorem backward_sim (spec : Program) (impl : ImplProgram) (ab : AllocBase spec impl)
    (SemaInv : SpecState → ImplState → Prop)
    (hIssueDepSat : ∀ (e : EngineId) (instr : DataPathInstrId) (ss : SpecState) (is : ImplState),
      SemaInv ss is → SpecInv spec ss → AllocatableAt spec ss e instr →
      is.semaphores (impl.waitOf instr) ≥ is.registers e (ab.waitReg e) →
      is.registers e (ab.waitReg e) =
        foldRegOps (impl.regOps e instr) (fun r => if r = ab.waitReg e then 0 else is.registers e r) (ab.waitReg e) →
      (∀ plid,
        (fun r => if r = ab.waitReg e then 0 else is.registers e r) (ab.monotoneReg e plid) =
        totalEntries ss e plid) →
      (∀ lid, is.registers e (ab.tripReg e lid) = tripEntries ss e spec.body lid) →
      depSatisfied spec (spec.depGraph instr) instr ss e = true)
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
    (e : EngineId) (ss : SpecState) (is is' : ImplState)
    (hSim : MatchStates spec impl ab SemaInv ss is)
    (hStep : ImplStep impl e is is')
    (hWf : Allocatable spec) (hSpecInv : SpecInv spec ss)
    (hUniq : UniqueScopeIds spec.body) (hUniqueInstr : UniqueInstrIds spec.engines spec.body)
    (hEngines : e ∈ spec.engines)
    : ∃ ss', SpecStar spec ss ss' ∧ MatchStates spec impl ab SemaInv ss' is' := by
  have wrap : (∃ ss', SpecStep spec e ss ss' ∧ MatchStates spec impl ab SemaInv ss' is')
      ∨ MatchStates spec impl ab SemaInv ss is' →
      ∃ ss', SpecStar spec ss ss' ∧ MatchStates spec impl ab SemaInv ss' is'
    | .inl ⟨ss', hStep, hSim'⟩ => ⟨ss', .step ⟨e, hStep⟩ .refl, hSim'⟩
    | .inr hSim' => ⟨ss, .refl, hSim'⟩
  apply wrap; cases hStep with
  | regOpStep hE frame rest f instr dst src t hStack hStmt hInstr hRegOp =>
    refine BackwardSim.case_regOpStep spec impl ab SemaInv hSemaInvMono innerOps hInnerOpsWf hRegOpsEq e ss is hSim frame rest f instr dst src t ?_ ?_ ?_ ?_
    all_goals assumption
  | stmtRegOpStep hE frame rest ops dst src t hStack hStmt hOp => apply BackwardSim.case_stmtRegOpStep <;> assumption
  | stmtRegOpDone hE frame rest ops hStack hStmt hDone =>
    have ⟨hLoop, hTrip⟩ := hSim.regOpFold e frame rest ops hStack hStmt
    have hDrop : List.drop ((is.pc e).stmtRegOpIdx) (ops e) = [] := by
      rw [hDone]; simp
    exact BackwardSim.case_stmtRegOpDone spec impl ab SemaInv hSemaInvMono e ss is hSim
      frame rest ops hStack hStmt hDone
      (fun lid => by have := hLoop lid; rwa [hDrop] at this)
      (fun lid => by have := hTrip lid; rwa [hDrop] at this)
  | issue hE frame imrest f instr hStack hStmt hInstr hRegOpsDone hWait =>
    apply BackwardSim.case_issue spec impl ab SemaInv hIssueDepSat hSemaInvMono innerOps hInnerOpsWf hRegOpsEq e ss is hSim hWf hSpecInv hUniq hUniqueInstr hEngines <;> assumption
  | commit hE idx instr hIdx => apply BackwardSim.case_commit <;> assumption
  | retire hE instr inflightRest hHead => apply BackwardSim.case_retire <;> assumption
  | blockDone hE frame rest f hStack hStmt hDone => apply BackwardSim.case_blockDone <;> assumption
  | loopEnter hE frame rest lid loopBody hStack hStmt hGuard =>
    have hPIO := scopeParent_in_enclosingLoops_loop hSim hSpecInv hUniq hEngines hStack hStmt
    have hNSP : ∀ parent, scopeParent spec.body lid = some parent → parent ≠ lid :=
      fun _ hP => scopeParent_ne_self hUniq hP
    exact BackwardSim.case_loopEnter spec impl ab SemaInv hSemaInvMono e ss is hSim hSpecInv hUniq hEngines
      frame rest lid loopBody hStack hStmt hGuard hPIO hNSP
  | loopSkip hE frame rest lid loopBody hStack hStmt hGuard =>
    apply BackwardSim.case_loopSkip <;> assumption
  | loopBack hE frame parent rest lid hStack hKind hEnd =>
    apply BackwardSim.case_loopBack <;> assumption
  | condTrue hE frame rest thenId elseId thenBody elseBody hStack hStmt hGuard =>
    have hPIO := scopeParent_in_enclosingLoops_cond_then hSim hSpecInv hUniq hEngines hStack hStmt
    have hNSP : ∀ parent, scopeParent spec.body thenId = some parent → parent ≠ thenId :=
      fun _ hP => scopeParent_ne_self hUniq hP
    exact BackwardSim.case_condTrue spec impl ab SemaInv hSemaInvMono e ss is hSim hSpecInv hUniq hEngines
      frame rest thenId elseId thenBody elseBody hStack hStmt hGuard hPIO hNSP
  | condFalse hE frame rest thenId elseId thenBody elseBody hStack hStmt hGuard =>
    have hPIO := scopeParent_in_enclosingLoops_cond_else hSim hSpecInv hUniq hEngines hStack hStmt
    have hNSP : ∀ parent, scopeParent spec.body elseId = some parent → parent ≠ elseId :=
      fun _ hP => scopeParent_ne_self hUniq hP
    exact BackwardSim.case_condFalse spec impl ab SemaInv hSemaInvMono e ss is hSim hSpecInv hUniq hEngines
      frame rest thenId elseId thenBody elseBody hStack hStmt hGuard hPIO hNSP
  | condDone hE frame parent rest sid hStack hKind hEnd =>
    apply BackwardSim.case_condDone <;> assumption

theorem backward_sim_star (spec : Program) (impl : ImplProgram) (ab : AllocBase spec impl)
    (SemaInv : SpecState → ImplState → Prop)
    (hIssueDepSat : ∀ (e : EngineId) (instr : DataPathInstrId) (ss : SpecState) (is : ImplState),
      SemaInv ss is → SpecInv spec ss → AllocatableAt spec ss e instr →
      is.semaphores (impl.waitOf instr) ≥ is.registers e (ab.waitReg e) →
      is.registers e (ab.waitReg e) =
        foldRegOps (impl.regOps e instr) (fun r => if r = ab.waitReg e then 0 else is.registers e r) (ab.waitReg e) →
      (∀ plid,
        (fun r => if r = ab.waitReg e then 0 else is.registers e r) (ab.monotoneReg e plid) =
        totalEntries ss e plid) →
      (∀ lid, is.registers e (ab.tripReg e lid) = tripEntries ss e spec.body lid) →
      depSatisfied spec (spec.depGraph instr) instr ss e = true)
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
    (ss : SpecState) (is is' : ImplState)
    (hSim : MatchStates spec impl ab SemaInv ss is)
    (hStar : ImplStarAny impl is is')
    (hWf : Allocatable spec) (hSpecInv : SpecInv spec ss)
    (hUniq : UniqueScopeIds spec.body) (hUniqueInstr : UniqueInstrIds spec.engines spec.body)
    : ∃ ss', SpecStar spec ss ss' ∧ MatchStates spec impl ab SemaInv ss' is' := by
  induction hStar generalizing ss with
  | refl => exact ⟨ss, SpecStar.refl, hSim⟩
  | step hStep _ ih =>
    obtain ⟨e, hStep⟩ := hStep
    have hEngines : e ∈ spec.engines := congrArg ProgramBase.engines ab.baseEq ▸ hStep.mem_engines
    obtain ⟨ss_mid, hSpecStar, hSim'⟩ := backward_sim spec impl ab SemaInv hIssueDepSat hRetireSema hSemaInvMono innerOps hInnerOpsWf hRegOpsEq e ss _ _ hSim hStep hWf hSpecInv hUniq hUniqueInstr hEngines
    have hSpecInv' := specInv_star spec ss ss_mid hUniq hUniqueInstr hSpecInv hSpecStar
    obtain ⟨ss', hStar', hSim''⟩ := ih ss_mid hSim' hSpecInv'
    exact ⟨ss', hSpecStar.trans hStar', hSim''⟩

-- Per-instruction allocation: issue hypothesis instantiation
theorem perInstr_issue_depSat (spec : Program) (impl : ImplProgram) (alloc : PerInstrAllocR spec impl)
    (e : EngineId) (instr : DataPathInstrId) (ss : SpecState) (is : ImplState)
    (hSema : perInstrSemaInv alloc ss is) (_ : SpecInv spec ss) (hWf : AllocatableAt spec ss e instr)
    (hWait : is.semaphores (impl.waitOf instr) ≥ is.registers e (alloc.waitReg e))
    (hRegVal : is.registers e (alloc.waitReg e) =
      foldRegOps (impl.regOps e instr) (fun r => if r = alloc.waitReg e then 0 else is.registers e r) (alloc.waitReg e))
    (hLoopRegs : ∀ plid,
      (fun r => if r = alloc.waitReg e then 0 else is.registers e r) (alloc.monotoneReg e plid) =
      totalEntries ss e plid)
    (hTripRegs : ∀ lid, is.registers e (alloc.tripReg e lid) = tripEntries ss e spec.body lid)
    : depSatisfied spec (spec.depGraph instr) instr ss e = true := by
  rw [alloc.regOpsEq] at hRegVal
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
  have hInnerEq := foldRegOps_perInstrExpectedRegOps_waitReg (ab := alloc.toAllocBase)
    (spec := spec) (ss := ss) (e := e) (instr := instr) baseRegs hLoopRegs
  simp only at hDecomp
  match hDep : spec.depGraph instr with
  | .none => simp [depSatisfied]
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
      · -- gate = 0: vacuous case
        unfold depSatisfied; simp only [hSS]
        match hPL : innermostParentScope spec.engines spec.body producer with
        | none => exact absurd hPL (by obtain ⟨_, h⟩ := innermostParentScope_of_sharedLoop hSS; simp [h])
        | some plid => simp only [Bool.or_eq_true, decide_eq_true_eq]; left; exact hVac
      · -- gate = 1: non-vacuous
        simp only [show tripEntries ss e spec.body sid > offset from by omega, ite_true, Nat.one_mul] at hDecomp
        rw [hDecomp, hInnerEq] at hRegVal
        have hWRV : is.registers e (impl.waitReg e instr) = expectedWaitVal spec ss e instr := by
          rw [alloc.waitRegEq]; exact hRegVal
        have h := sema_wait_implies_depSatisfied (hSema := hSema) (alloc.waitRegEq e instr ▸ hWait) hWRV hWf
        rw [hDep] at h; exact h
    | none =>
      simp only [hSS] at hDecomp; rw [hDecomp, hInnerEq] at hRegVal
      have hWRV : is.registers e (impl.waitReg e instr) = expectedWaitVal spec ss e instr := by
        rw [alloc.waitRegEq]; exact hRegVal
      have h := sema_wait_implies_depSatisfied (hSema := hSema) (alloc.waitRegEq e instr ▸ hWait) hWRV hWf
      rw [hDep] at h; exact h

-- Convenience: backward simulation specialized to per-instruction allocation
theorem perInstr_backward_sim (spec : Program) (impl : ImplProgram) (alloc : PerInstrAllocR spec impl)
    (e : EngineId) (ss : SpecState) (is is' : ImplState)
    (hSim : MatchStates spec impl alloc.toAllocBase (perInstrSemaInv alloc) ss is)
    (hStep : ImplStep impl e is is')
    (hWf : Allocatable spec) (hSpecInv : SpecInv spec ss)
    (hUniq : UniqueScopeIds spec.body) (hUniqueInstr : UniqueInstrIds spec.engines spec.body)
    (hEngines : e ∈ spec.engines)
    : ∃ ss', SpecStar spec ss ss' ∧ MatchStates spec impl alloc.toAllocBase (perInstrSemaInv alloc) ss' is' :=
  backward_sim spec impl alloc.toAllocBase (perInstrSemaInv alloc)
    (perInstr_issue_depSat spec impl alloc) (perInstr_retire_semaInv spec impl alloc)
    (perInstr_semaInv_mono spec impl alloc)
    (fun e i => perInstrExpectedRegOps spec (alloc.waitReg e) alloc.monotoneReg e i)
    ⟨perInstr_innerRegOpsFirstSafe spec impl alloc,
     fun e i => perInstrExpectedRegOps_nonEmpty spec (alloc.waitReg e) alloc.monotoneReg e i,
     perInstr_innerRegOpsDstWaitReg spec impl alloc⟩
    alloc.regOpsEq
    e ss is is' hSim hStep hWf hSpecInv hUniq hUniqueInstr hEngines

-- Convenience: backward simulation star specialized to per-instruction allocation
theorem perInstr_backward_sim_star (spec : Program) (impl : ImplProgram) (alloc : PerInstrAllocR spec impl)
    (ss : SpecState) (is is' : ImplState)
    (hSim : MatchStates spec impl alloc.toAllocBase (perInstrSemaInv alloc) ss is)
    (hStar : ImplStarAny impl is is')
    (hWf : Allocatable spec) (hSpecInv : SpecInv spec ss)
    (hUniq : UniqueScopeIds spec.body) (hUniqueInstr : UniqueInstrIds spec.engines spec.body)
    : ∃ ss', SpecStar spec ss ss' ∧ MatchStates spec impl alloc.toAllocBase (perInstrSemaInv alloc) ss' is' :=
  backward_sim_star spec impl alloc.toAllocBase (perInstrSemaInv alloc)
    (perInstr_issue_depSat spec impl alloc) (perInstr_retire_semaInv spec impl alloc)
    (perInstr_semaInv_mono spec impl alloc)
    (fun e i => perInstrExpectedRegOps spec (alloc.waitReg e) alloc.monotoneReg e i)
    ⟨perInstr_innerRegOpsFirstSafe spec impl alloc,
     fun e i => perInstrExpectedRegOps_nonEmpty spec (alloc.waitReg e) alloc.monotoneReg e i,
     perInstr_innerRegOpsDstWaitReg spec impl alloc⟩
    alloc.regOpsEq
    ss is is' hSim hStar hWf hSpecInv hUniq hUniqueInstr
