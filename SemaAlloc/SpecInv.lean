import SemaAlloc.Utilities

-- Extract stmtIdx for a specific loop's frame on the stack
def stmtIdxInLoop : List Frame → ScopeId → Option Nat
  | [], _ => none
  | f :: rest, loop =>
    match f.kind with
    | .loop lid => if lid = loop then some f.stmtIdx else stmtIdxInLoop rest loop
    | .cond sid => if sid = loop then some f.stmtIdx else stmtIdxInLoop rest loop
    | _ => stmtIdxInLoop rest loop

-- Extract stmtIdx for the top-level (base) frame
def stmtIdxAtTop : List Frame → Option Nat
  | [] => none
  | f :: rest =>
    match f.kind with
    | .top => some f.stmtIdx
    | _ => stmtIdxAtTop rest

inductive StackMatchesProgram (progBody : List Stmt) : List Frame → Prop where
  | base (stmtIdx instrIdx : Nat) :
      StackMatchesProgram progBody [⟨progBody, stmtIdx, .top⟩]
  | loop (loopBody : List Stmt) (stmtIdx instrIdx : Nat)
      (lid : ScopeId) (parentFrame : Frame) (rest : List Frame)
      (hStmt : parentFrame.body[parentFrame.stmtIdx]? = some (Stmt.loop lid loopBody))
      (hMatch : StackMatchesProgram progBody (parentFrame :: rest)) :
      StackMatchesProgram progBody
        (⟨loopBody, stmtIdx, .loop lid⟩ :: parentFrame :: rest)
  | cond (thenBody elseBody : List Stmt) (stmtIdx instrIdx : Nat)
      (thenId elseId : ScopeId) (parentFrame : Frame) (rest : List Frame)
      (taken : Bool)
      (hStmt : parentFrame.body[parentFrame.stmtIdx]? = some (Stmt.cond thenId elseId thenBody elseBody))
      (hMatch : StackMatchesProgram progBody (parentFrame :: rest)) :
      StackMatchesProgram progBody
        (⟨if taken then thenBody else elseBody, stmtIdx,
          .cond (if taken then thenId else elseId)⟩ :: parentFrame :: rest)

private theorem smp_change_top_stmtIdx {progBody : List Stmt} {f : Frame} {rest : List Frame}
    (h : StackMatchesProgram progBody (f :: rest)) (newSi newIi : Nat)
    : StackMatchesProgram progBody (⟨f.body, newSi, f.kind⟩ :: rest) := by
  cases h with
  | base si ii => exact .base newSi newIi
  | loop lb si ii lid pf rest' hStmt hMatch => exact .loop lb newSi newIi lid pf rest' hStmt hMatch
  | cond tb eb si ii tid eid pf rest' taken hStmt hMatch => exact .cond tb eb newSi newIi tid eid pf rest' taken hStmt hMatch

structure SpecInv (spec : Program) (ss : SpecState) : Prop where
  selfHistory : ∀ (e : EngineId) (lid : ScopeId) (k : Nat),
    1 ≤ k → k ≤ totalEntries ss e lid → ss.scopeEntryHistory e lid (some lid) k = 1
  cumulative : ∀ (e : EngineId) (lid : ScopeId) (olid : ScopeId),
    lid ∈ scopeIdsOf ((scopeBodyOf spec.body olid).getD []) →
    cumExecs ss e lid (some olid) (totalEntries ss e olid) = totalEntries ss e lid
  zeroFuture : ∀ (e : EngineId) (lid : ScopeId) (outerLoop : Option ScopeId) (k : Nat),
    k > totalEntriesOpt ss e outerLoop → ss.scopeEntryHistory e lid outerLoop k = 0
  activeLoopPos : ∀ (e : EngineId) (lid : ScopeId),
    lid ∈ loopsOnStack ss e → totalEntries ss e lid ≥ 1
  ancestorsActive : ∀ (e : EngineId) (lid : ScopeId) (loop : ScopeId),
    lid ∈ loopsOnStack ss e →
    lid ∈ scopeIdsOf ((scopeBodyOf spec.body loop).getD []) →
    loop ∈ loopsOnStack ss e
  zeroBeforeEntry : ∀ (e : EngineId) (lid : ScopeId) (loop : ScopeId) (si j : Nat) (stmt : Stmt),
    loop ∈ loopsOnStack ss e →
    stmtIdxInLoop (ss.pc e).stack loop = some si →
    ((scopeBodyOf spec.body loop).getD [])[j]? = some stmt →
    lid ∈ scopeIdsOf [stmt] →
    si < j →
    ss.scopeEntryHistory e lid (some loop) (totalEntries ss e loop) = 0
  zeroBeforeEntryTop : ∀ (e : EngineId) (lid : ScopeId) (si j : Nat) (stmt : Stmt),
    stmtIdxAtTop (ss.pc e).stack = some si →
    spec.body[j]? = some stmt →
    lid ∈ scopeIdsOf [stmt] →
    si < j →
    totalEntries ss e lid = 0
  wellFormedPC : ∀ (e : EngineId), StackMatchesProgram spec.body (ss.pc e).stack
  inflightInBody : ∀ (e : EngineId) (instr : DataPathInstrId) (phase : Phase),
    (instr, phase) ∈ ss.inflight e → instrInBody spec.engines spec.body instr = true
  inflightEngineEq : ∀ (e : EngineId) (instr : DataPathInstrId) (phase : Phase),
    (instr, phase) ∈ ss.inflight e → instrEngine spec.engines spec.body instr = some e

theorem specInv_init (spec : Program) (ss : SpecState)
    (hHist : ∀ e lid (ol : Option ScopeId) k, ss.scopeEntryHistory e lid ol k = 0)
    (hIters : ∀ e lid, totalEntries ss e lid = 0)
    (hNoLoops : ∀ e, loopsOnStack ss e = [])
    (hWFPC : ∀ e, StackMatchesProgram spec.body (ss.pc e).stack)
    (hInflight : ∀ e, ss.inflight e = [])
    : SpecInv spec ss where
  selfHistory := by intro e lid k hk1 hk2; rw [hIters] at hk2; omega
  cumulative := by
    intro e lid olid _; simp [cumExecs, totalEntries, hHist]
  zeroFuture := by intro e lid ol k _; exact hHist e lid ol k
  activeLoopPos := by intro e lid hm; simp [hNoLoops] at hm
  ancestorsActive := by intro e lid loop hm; simp [hNoLoops] at hm
  zeroBeforeEntry := by intro e lid loop si j stmt hm; simp [hNoLoops] at hm
  zeroBeforeEntryTop := by intro e lid; intros; exact hIters e lid
  wellFormedPC := hWFPC
  inflightInBody := by intro e instr phase h; simp [hInflight] at h
  inflightEngineEq := by intro e instr phase h; simp [hInflight] at h

-- Transfer when history and PC unchanged (commit, retire)
theorem specInv_of_same_history {spec : Program} {ss ss' : SpecState}
    (hInv : SpecInv spec ss)
    (hHist : ss'.scopeEntryHistory = ss.scopeEntryHistory)
    (hPC : ss'.pc = ss.pc)
    (hInflight : ∀ e instr phase, (instr, phase) ∈ ss'.inflight e →
      ∃ phase', (instr, phase') ∈ ss.inflight e)
    : SpecInv spec ss' where
  selfHistory := by intro e lid k hk1 hk2; rw [hHist]; simp [totalEntries, hHist] at hk2; exact hInv.selfHistory e lid k hk1 hk2
  cumulative := by
    intro e lid olid hEnc; simp [cumExecs, totalEntries, hHist]
    exact hInv.cumulative e lid olid hEnc
  zeroFuture := by
    intro e lid ol k hk; rw [hHist]; simp [totalEntries, totalEntriesOpt, hHist] at hk
    exact hInv.zeroFuture e lid ol k (by cases ol <;> simp_all [totalEntriesOpt, totalEntries])
  activeLoopPos := by
    intro e lid hm; simp [totalEntries, hHist]
    exact hInv.activeLoopPos e lid (by simp [loopsOnStack] at hm ⊢; rwa [← hPC])
  ancestorsActive := by
    intro e lid loop hm hEnc
    have hm' : lid ∈ loopsOnStack ss e := by
      simp [loopsOnStack] at hm ⊢; rwa [← hPC]
    have := hInv.ancestorsActive e lid loop hm' hEnc
    simp [loopsOnStack] at this ⊢; rwa [hPC]
  zeroBeforeEntry := by
    intro e lid loop si j stmt hLoop hSi hJ hMem hLt
    rw [hHist]; simp [totalEntries, hHist]
    have hLoop' : loop ∈ loopsOnStack ss e := by simp [loopsOnStack]; rw [← hPC]; simp [loopsOnStack] at hLoop; exact hLoop
    exact hInv.zeroBeforeEntry e lid loop si j stmt hLoop' (hPC ▸ hSi) hJ hMem hLt
  zeroBeforeEntryTop := by
    intro e lid si j stmt hSi hJ hMem hLt
    simp [totalEntries, hHist]
    exact hInv.zeroBeforeEntryTop e lid si j stmt (hPC ▸ hSi) hJ hMem hLt
  wellFormedPC := fun e => hPC ▸ hInv.wellFormedPC e
  inflightInBody := fun e instr phase h =>
    let ⟨phase', h'⟩ := hInflight e instr phase h; hInv.inflightInBody e instr phase' h'
  inflightEngineEq := fun e instr phase h =>
    let ⟨phase', h'⟩ := hInflight e instr phase h; hInv.inflightEngineEq e instr phase' h'

-- Helper: enclosingLoopsFromStack is invariant under stmtIdx changes
private theorem enclosing_change_stmtIdx {f : Frame} {rest : List Frame} {newSi : Nat}
    : enclosingLoopsFromStack (⟨f.body, newSi, f.kind⟩ :: rest) = enclosingLoopsFromStack (f :: rest) := by
  unfold enclosingLoopsFromStack; cases f.kind <;> simp
private theorem stmtIdxAtTop_change_nontop {f : Frame} {rest : List Frame} {newSi : Nat}
    (hNe : f.kind ≠ .top)
    : stmtIdxAtTop (⟨f.body, newSi, f.kind⟩ :: rest) = stmtIdxAtTop (f :: rest) := by
  unfold stmtIdxAtTop; cases hk : f.kind <;> aesop

-- NOTE: With loop unification, pushing a cond frame DOES change enclosingLoopsFromStack
-- (cond frames now contribute their ScopeId). These lemmas are no longer true as stated.
-- The condTrue/condFalse cases in specInv_step need to mirror loopEnter instead.
private theorem enclosing_push_cond {body : List Stmt} {si : Nat} {sid : ScopeId} {rest : List Frame}
    : enclosingLoopsFromStack (⟨body, si, .cond sid⟩ :: rest) = sid :: enclosingLoopsFromStack rest := by
  simp [enclosingLoopsFromStack]
private theorem stmtIdxInLoop_push_cond {body : List Stmt} {si : Nat} {sid : ScopeId} {rest : List Frame} {loop : ScopeId}
    (hNe : sid ≠ loop)
    : stmtIdxInLoop (⟨body, si, .cond sid⟩ :: rest) loop = stmtIdxInLoop rest loop := by
  simp [stmtIdxInLoop, hNe]

-- Helper: pushing a cond frame doesn't change stmtIdxAtTop
private theorem stmtIdxAtTop_push_cond {body : List Stmt} {si : Nat} {sid : ScopeId} {rest : List Frame}
    : stmtIdxAtTop (⟨body, si, .cond sid⟩ :: rest) = stmtIdxAtTop rest := by
  simp [stmtIdxAtTop]
theorem smp_loopIds_subset {progBody : List Stmt} :
    ∀ {stack : List Frame},
    StackMatchesProgram progBody stack →
    ∀ frame, frame ∈ stack → ∀ lid, lid ∈ scopeIdsOf frame.body → lid ∈ scopeIdsOf progBody
  | _, .base si ii, frame, hMem, lid, hlid => by simp at hMem; subst hMem; exact hlid
  | _, .loop lb si ii lid' pf rest hStmt hMatch, frame, hMem, lid, hlid => by
    rcases List.mem_cons.mp hMem with rfl | hMem'
    · exact smp_loopIds_subset hMatch pf (List.Mem.head _) lid
        (mem_scopeIdsOf_of_getElem hStmt (by simp [scopeIdsOf]; right; exact hlid))
    · exact smp_loopIds_subset hMatch frame hMem' lid hlid
  | _, .cond tb eb si ii tid eid pf rest taken hStmt hMatch, frame, hMem, lid, hlid => by
    rcases List.mem_cons.mp hMem with rfl | hMem'
    · exact smp_loopIds_subset hMatch pf (List.Mem.head _) lid
        (mem_scopeIdsOf_of_getElem hStmt (by cases taken <;> simp only [scopeIdsOf, List.mem_cons, List.mem_append, List.mem_nil_iff, or_false] <;> aesop))
    · exact smp_loopIds_subset hMatch frame hMem' lid hlid

-- All these follow from the general uniqueScopeIds_of_getElem in ASTLemmas.
-- UniqueScopeIds propagates through sub-bodies
private theorem uniqueScopeIds_of_getElem_loop {body : List Stmt} {idx : Nat} {lid : ScopeId} {lb : List Stmt}
    (hIdx : body[idx]? = some (Stmt.loop lid lb)) (hUniq : UniqueScopeIds body) : UniqueScopeIds lb := by
  have h := uniqueScopeIds_of_getElem hIdx hUniq
  match h with | .loop _ _ _ _ _ _ hBody _ => exact hBody

private theorem uniqueScopeIds_of_getElem_condTrue {body : List Stmt} {idx : Nat} {thenId elseId : ScopeId} {tb eb : List Stmt}
    (hIdx : body[idx]? = some (Stmt.cond thenId elseId tb eb)) (hUniq : UniqueScopeIds body) : UniqueScopeIds tb := by
  have h := uniqueScopeIds_of_getElem hIdx hUniq
  -- .cond thenId elseId tb eb rest hNe hTnTb hTnEb hTnR hEnTb hEnEb hEnR hTbDisj hEbDisj hTb hEb hR
  match h with | .cond _ _ _ _ _ _ _ _ _ _ _ _ _ _ hTb _ _ => exact hTb

private theorem uniqueScopeIds_of_getElem_condFalse {body : List Stmt} {idx : Nat} {thenId elseId : ScopeId} {tb eb : List Stmt}
    (hIdx : body[idx]? = some (Stmt.cond thenId elseId tb eb)) (hUniq : UniqueScopeIds body) : UniqueScopeIds eb := by
  have h := uniqueScopeIds_of_getElem hIdx hUniq
  match h with | .cond _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hEb _ => exact hEb

private theorem lid_not_in_own_body {body : List Stmt} {idx : Nat} {lid : ScopeId} {lb : List Stmt}
    (hIdx : body[idx]? = some (Stmt.loop lid lb)) (hUniq : UniqueScopeIds body) : lid ∉ scopeIdsOf lb := by
  have h := uniqueScopeIds_of_getElem hIdx hUniq
  -- .loop lid body rest hNB hNR hDisj hBody hRest  (3 type + 5 proof = 8)
  match h with | .loop _ _ _ hNB _ _ _ _ => exact hNB

theorem smp_uniqueScopeIds {progBody : List Stmt} {stack : List Frame}
    (hSMP : StackMatchesProgram progBody stack) (hUniq : UniqueScopeIds progBody)
    : ∀ f, f ∈ stack → UniqueScopeIds f.body := by
  induction hSMP with
  | base si ii => intro f hf; simp at hf; subst hf; exact hUniq
  | loop lb si ii lid pf rest hStmt hMatch ih =>
    intro f hf; rcases List.mem_cons.mp hf with rfl | hf
    · exact uniqueScopeIds_of_getElem_loop hStmt (ih pf (List.Mem.head _))
    · exact ih f hf
  | cond tb eb si ii tid eid pf rest taken hStmt hMatch ih =>
    intro f hf; rcases List.mem_cons.mp hf with rfl | hf
    · cases taken with
      | false => simp at hf ⊢; exact uniqueScopeIds_of_getElem_condFalse hStmt (ih pf (List.Mem.head _))
      | true => simp at hf ⊢; exact uniqueScopeIds_of_getElem_condTrue hStmt (ih pf (List.Mem.head _))
    · exact ih f hf

-- stmtIdxInLoop returns some only if lid is on the stack as a loop frame
private theorem stmtIdxInLoop_mem_enclosing {stack : List Frame} {lid : ScopeId} {si : Nat}
    (h : stmtIdxInLoop stack lid = some si) : lid ∈ enclosingLoopsFromStack stack := by
  induction stack with
  | nil => simp [stmtIdxInLoop] at h
  | cons f rest ih =>
    cases hk : f.kind <;> simp [stmtIdxInLoop, enclosingLoopsFromStack, hk] at h ⊢ <;> aesop

-- Enclosing loop IDs are disjoint from the top frame's body loopIds
-- For all frames on the stack, scopeBodyOf agrees with progBody
theorem smp_scopeBodyOf_agree {progBody : List Stmt} {stack : List Frame}
    (hSMP : StackMatchesProgram progBody stack) (hUniq : UniqueScopeIds progBody)
    : ∀ f, f ∈ stack → ∀ lid, lid ∈ scopeIdsOf f.body → scopeBodyOf progBody lid = scopeBodyOf f.body lid := by
  induction hSMP with
  | base si ii => intro f hf; simp at hf; subst hf; intro lid _; rfl
  | loop lb si ii lid' pf rest hStmt hMatch ih =>
    intro f hf lid hlid; rcases List.mem_cons.mp hf with rfl | hf
    · -- f is the top loop frame, f.body = lb
      have hPfUniq := smp_uniqueScopeIds hMatch hUniq pf (List.Mem.head _)
      rw [ih pf (List.Mem.head _) lid (mem_scopeIdsOf_of_getElem hStmt (by simp [scopeIdsOf]; right; exact hlid))]
      exact scopeBodyOf_descend_loop hStmt hlid hPfUniq
    · exact ih f hf lid hlid
  | cond tb eb si ii tid eid pf rest taken hStmt hMatch ih =>
    intro f hf lid hlid; rcases List.mem_cons.mp hf with rfl | hf
    · have hPfUniq := smp_uniqueScopeIds hMatch hUniq pf (List.Mem.head _)
      cases taken with
      | false =>
        simp at hlid ⊢
        rw [ih pf (List.Mem.head _) lid (mem_scopeIdsOf_of_getElem hStmt (by simp only [scopeIdsOf, List.mem_cons, List.mem_append, List.mem_nil_iff, or_false]; aesop))]
        exact scopeBodyOf_descend_condFalse hStmt hlid hPfUniq
      | true =>
        simp at hlid ⊢
        rw [ih pf (List.Mem.head _) lid (mem_scopeIdsOf_of_getElem hStmt (by simp [scopeIdsOf]; right; right; left; exact hlid))]
        exact scopeBodyOf_descend_condTrue hStmt hlid hPfUniq
    · exact ih f hf lid hlid

-- For loop frames on the stack, scopeBodyOf progBody lid = some f.body
theorem smp_scopeBodyOf {progBody : List Stmt} {stack : List Frame} {lid : ScopeId}
    (hSMP : StackMatchesProgram progBody stack) (hUniq : UniqueScopeIds progBody)
    (f : Frame) (hf : f ∈ stack) (hk : f.kind = .loop lid)
    : scopeBodyOf progBody lid = some f.body := by
  induction hSMP generalizing lid f with
  | base si ii => simp at hf; subst hf; simp at hk
  | loop lb si ii lid' pf rest hStmt hMatch ih =>
    rcases List.mem_cons.mp hf with rfl | hf
    · simp at hk; subst hk
      have hPfUniq := smp_uniqueScopeIds hMatch hUniq pf (List.Mem.head _)
      rw [smp_scopeBodyOf_agree hMatch hUniq pf (List.Mem.head _) lid'
        (mem_scopeIdsOf_of_getElem hStmt (by simp [scopeIdsOf]))]
      exact scopeBodyOf_of_getElem hStmt hPfUniq
    · exact ih f hf hk
  | cond _ _ _ _ _ _ _ _ _ _ _ ih =>
    rcases List.mem_cons.mp hf with rfl | hf
    · simp at hk
    · exact ih f hf hk

-- Generalized: any loop frame (loop or cond) has scopeBodyOf agreeing with its body
theorem smp_scopeBodyOf_loop {progBody : List Stmt} {stack : List Frame} {sid : ScopeId}
    (hSMP : StackMatchesProgram progBody stack) (hUniq : UniqueScopeIds progBody)
    (f : Frame) (hf : f ∈ stack) (hk : f.kind.loopId? = some sid)
    : scopeBodyOf progBody sid = some f.body := by
  induction hSMP generalizing sid f with
  | base si ii => simp at hf; subst hf; simp [FrameKind.loopId?] at hk
  | loop lb si ii lid' pf rest hStmt hMatch ih =>
    rcases List.mem_cons.mp hf with rfl | hf
    · simp [FrameKind.loopId?] at hk; subst hk
      have hPfUniq := smp_uniqueScopeIds hMatch hUniq pf (List.Mem.head _)
      rw [smp_scopeBodyOf_agree hMatch hUniq pf (List.Mem.head _) lid'
        (mem_scopeIdsOf_of_getElem hStmt (by simp [scopeIdsOf]))]
      exact scopeBodyOf_of_getElem hStmt hPfUniq
    · exact ih f hf hk
  | cond tb eb si ii tid eid pf rest taken hStmt hMatch ih =>
    rcases List.mem_cons.mp hf with rfl | hf
    · cases taken with
      | false =>
        simp [FrameKind.loopId?] at hk; subst hk
        have hPfUniq := smp_uniqueScopeIds hMatch hUniq pf (List.Mem.head _)
        rw [smp_scopeBodyOf_agree hMatch hUniq pf (List.Mem.head _) eid
          (mem_scopeIdsOf_of_getElem hStmt (by simp only [scopeIdsOf, List.mem_cons, List.mem_append, List.mem_nil_iff, or_false]; aesop))]
        exact scopeBodyOf_of_getElem_condFalse hStmt hPfUniq
      | true =>
        simp [FrameKind.loopId?] at hk; subst hk
        have hPfUniq := smp_uniqueScopeIds hMatch hUniq pf (List.Mem.head _)
        rw [smp_scopeBodyOf_agree hMatch hUniq pf (List.Mem.head _) tid
          (mem_scopeIdsOf_of_getElem hStmt (by simp [scopeIdsOf]))]
        exact scopeBodyOf_of_getElem_condTrue hStmt hPfUniq
    · exact ih f hf hk

-- All cond disjointness lemmas derived from uniqueScopeIds_of_getElem
private theorem thenId_not_in_then_body {body : List Stmt} {idx : Nat} {thenId elseId : ScopeId} {tb eb : List Stmt}
    (hIdx : body[idx]? = some (Stmt.cond thenId elseId tb eb)) (hUniq : UniqueScopeIds body) : thenId ∉ scopeIdsOf tb := by
  match uniqueScopeIds_of_getElem hIdx hUniq with | .cond _ _ _ _ _ _ hTnTb _ _ _ _ _ _ _ _ _ _ => exact hTnTb

private theorem elseId_not_in_else_body {body : List Stmt} {idx : Nat} {thenId elseId : ScopeId} {tb eb : List Stmt}
    (hIdx : body[idx]? = some (Stmt.cond thenId elseId tb eb)) (hUniq : UniqueScopeIds body) : elseId ∉ scopeIdsOf eb := by
  match uniqueScopeIds_of_getElem hIdx hUniq with | .cond _ _ _ _ _ _ _ _ _ _ hEnEb _ _ _ _ _ _ => exact hEnEb

private theorem thenId_not_in_else_body {body : List Stmt} {idx : Nat} {thenId elseId : ScopeId} {tb eb : List Stmt}
    (hIdx : body[idx]? = some (Stmt.cond thenId elseId tb eb)) (hUniq : UniqueScopeIds body) : thenId ∉ scopeIdsOf eb := by
  match uniqueScopeIds_of_getElem hIdx hUniq with | .cond _ _ _ _ _ _ _ hTnEb _ _ _ _ _ _ _ _ _ => exact hTnEb

private theorem thenId_ne_elseId_of_getElem {body : List Stmt} {idx : Nat} {thenId elseId : ScopeId} {tb eb : List Stmt}
    (hIdx : body[idx]? = some (Stmt.cond thenId elseId tb eb)) (hUniq : UniqueScopeIds body) : thenId ≠ elseId := by
  match uniqueScopeIds_of_getElem hIdx hUniq with | .cond _ _ _ _ _ hNe _ _ _ _ _ _ _ _ _ _ _ => exact hNe

private theorem tb_disjoint_eb_of_getElem {body : List Stmt} {idx : Nat} {thenId elseId : ScopeId} {tb eb : List Stmt}
    (hIdx : body[idx]? = some (Stmt.cond thenId elseId tb eb)) (hUniq : UniqueScopeIds body)
    : ∀ x, x ∈ scopeIdsOf tb → x ∉ scopeIdsOf eb := by
  match uniqueScopeIds_of_getElem hIdx hUniq with
  | .cond _ _ _ _ _ _ _ _ _ _ _ _ hTbDisj _ _ _ _ => intro x hx; exact (hTbDisj x hx).1

private theorem elseId_not_in_then_body {body : List Stmt} {idx : Nat} {thenId elseId : ScopeId} {tb eb : List Stmt}
    (hIdx : body[idx]? = some (Stmt.cond thenId elseId tb eb)) (hUniq : UniqueScopeIds body) : elseId ∉ scopeIdsOf tb := by
  match uniqueScopeIds_of_getElem hIdx hUniq with | .cond _ _ _ _ _ _ _ _ _ hEnTb _ _ _ _ _ _ _ => exact hEnTb

theorem enclosing_disjoint_top {progBody : List Stmt} {frame : Frame} {rest : List Frame}
    (hSMP : StackMatchesProgram progBody (frame :: rest))
    (hUniq : UniqueScopeIds progBody)
    : ∀ lid, lid ∈ enclosingLoopsFromStack (frame :: rest) → lid ∉ scopeIdsOf frame.body := by
  intro lid hEnc
  cases hSMP with
  | base si ii => simp [enclosingLoopsFromStack] at hEnc
  | loop loopBody si ii lid' parentFrame rest' hStmt hMatch =>
    simp [enclosingLoopsFromStack] at hEnc
    rcases hEnc with rfl | hEnc
    · exact lid_not_in_own_body hStmt (smp_uniqueScopeIds hMatch hUniq parentFrame (List.Mem.head _))
    · intro hIn
      exact enclosing_disjoint_top hMatch hUniq lid hEnc (mem_scopeIdsOf_of_getElem hStmt (by simp [scopeIdsOf]; right; exact hIn))
  | cond _ _ _ _ _ _ parentFrame _ taken hStmt hMatch =>
    cases taken with
    | false =>
      simp [enclosingLoopsFromStack] at hEnc
      rcases hEnc with rfl | hEnc
      · exact elseId_not_in_else_body hStmt (smp_uniqueScopeIds hMatch hUniq parentFrame (List.Mem.head _))
      · intro hIn; exact enclosing_disjoint_top hMatch hUniq lid hEnc
          (mem_scopeIdsOf_of_getElem hStmt (by simp only [scopeIdsOf, List.mem_cons, List.mem_append, List.mem_nil_iff, or_false]; aesop))
    | true =>
      simp [enclosingLoopsFromStack] at hEnc
      rcases hEnc with rfl | hEnc
      · exact thenId_not_in_then_body hStmt (smp_uniqueScopeIds hMatch hUniq parentFrame (List.Mem.head _))
      · intro hIn; exact enclosing_disjoint_top hMatch hUniq lid hEnc
          (mem_scopeIdsOf_of_getElem hStmt (by simp only [scopeIdsOf, List.mem_cons, List.mem_append, List.mem_nil_iff, or_false]; aesop))

-- Enclosing loops are unique on a well-formed stack.
private theorem enclosing_no_dup {progBody : List Stmt} {stack : List Frame}
    (hSMP : StackMatchesProgram progBody stack) (hUniq : UniqueScopeIds progBody)
    : List.Nodup (enclosingLoopsFromStack stack) := by
  induction hSMP with
  | base si ii => simp [enclosingLoopsFromStack]
  | loop _ _ _ _ pf _ hStmt hMatch ih =>
    simp [enclosingLoopsFromStack]
    exact ⟨fun hIn => enclosing_disjoint_top hMatch hUniq _ hIn
      (mem_scopeIdsOf_of_getElem hStmt (by simp [scopeIdsOf])), ih⟩
  | cond tb eb si ii tid eid pf rest taken hStmt hMatch ih =>
    cases taken with
    | false =>
      simp [enclosingLoopsFromStack]
      exact ⟨fun hIn => enclosing_disjoint_top hMatch hUniq eid hIn
        (mem_scopeIdsOf_of_getElem hStmt (by simp only [scopeIdsOf, List.mem_cons, List.mem_append, List.mem_nil_iff, or_false]; aesop)), ih⟩
    | true =>
      simp [enclosingLoopsFromStack]
      exact ⟨fun hIn => enclosing_disjoint_top hMatch hUniq _ hIn
        (mem_scopeIdsOf_of_getElem hStmt (by simp [scopeIdsOf])), ih⟩

-- A loop that appears on the top frame can't also appear in deeper frames' enclosing
theorem sid_not_in_rest_enclosing {progBody : List Stmt} {frame parent : Frame} {rest : List Frame}
    {sid : ScopeId}
    (hSMP : StackMatchesProgram progBody (frame :: parent :: rest))
    (hUniq : UniqueScopeIds progBody)
    (hKind : frame.kind = .cond sid ∨ frame.kind = .loop sid)
    : sid ∉ enclosingLoopsFromStack (parent :: rest) := by
  have hND := enclosing_no_dup hSMP hUniq
  rcases hKind with hK | hK <;> (simp [enclosingLoopsFromStack, hK] at hND; exact hND.1)

private theorem stmtIdxInLoop_none_of_popped {progBody : List Stmt} {frame parent : Frame} {rest : List Frame}
    {sid : ScopeId}
    (hSMP : StackMatchesProgram progBody (frame :: parent :: rest))
    (hUniq : UniqueScopeIds progBody)
    (hKind : frame.kind = .cond sid ∨ frame.kind = .loop sid)
    : stmtIdxInLoop (parent :: rest) sid = none := by
  cases h : stmtIdxInLoop (parent :: rest) sid with
  | none => rfl
  | some si =>
    exfalso
    have hEnc := stmtIdxInLoop_mem_enclosing h
    exact sid_not_in_rest_enclosing hSMP hUniq hKind hEnc

-- If sid ∈ scopeIdsOf frame.body and the stack has SMP with UniqueScopeIds,
-- then sid is NOT already on the stack (as an enclosing loop).
theorem sid_not_on_stack_at_entry {spec : Program} {ss : SpecState} {e : EngineId}
    {frame : Frame} {rest : List Frame} {sid : ScopeId}
    (hStack : (ss.pc e).stack = frame :: rest)
    (hSidInBody : sid ∈ scopeIdsOf frame.body)
    (hSMP : StackMatchesProgram spec.body (ss.pc e).stack)
    (hUniq : UniqueScopeIds spec.body)
    : sid ∉ loopsOnStack ss e := by
  simp [loopsOnStack, hStack]
  have hSMP' := hStack ▸ hSMP
  intro hEnc
  exact enclosing_disjoint_top hSMP' hUniq sid hEnc hSidInBody

-- Convenience aliases for backward compatibility at call sites
theorem lid_not_on_stack_at_entry {spec : Program} {ss : SpecState} {e : EngineId}
    {frame : Frame} {rest : List Frame} {lid : ScopeId} {loopBody : List Stmt}
    (hStack : (ss.pc e).stack = frame :: rest)
    (hStmt : frame.body[frame.stmtIdx]? = some (Stmt.loop lid loopBody))
    (hSMP : StackMatchesProgram spec.body (ss.pc e).stack)
    (hUniq : UniqueScopeIds spec.body)
    : lid ∉ loopsOnStack ss e :=
  sid_not_on_stack_at_entry hStack
    (mem_scopeIdsOf_of_getElem hStmt (by simp [scopeIdsOf])) hSMP hUniq

theorem elseId_not_on_stack_at_entry {spec : Program} {ss : SpecState} {e : EngineId}
    {frame : Frame} {rest : List Frame} {thenId elseId : ScopeId} {thenBody elseBody : List Stmt}
    (hStack : (ss.pc e).stack = frame :: rest)
    (hStmt : frame.body[frame.stmtIdx]? = some (Stmt.cond thenId elseId thenBody elseBody))
    (hSMP : StackMatchesProgram spec.body (ss.pc e).stack)
    (hUniq : UniqueScopeIds spec.body)
    : elseId ∉ loopsOnStack ss e :=
  sid_not_on_stack_at_entry hStack
    (mem_scopeIdsOf_of_getElem hStmt (by simp [scopeIdsOf])) hSMP hUniq

-- If lid ∈ scopeIdsOf of the top frame's body, and loop is on rest (below top frame)
-- with stmtIdxInLoop rest loop = some si, then lid is inside loopBody[si].
theorem smp_lid_in_loop_stmt {progBody : List Stmt}
    {stack : List Frame}
    (hSMP : StackMatchesProgram progBody stack) (hUniq : UniqueScopeIds progBody)
    {frame : Frame} {rest : List Frame} (hEq : stack = frame :: rest)
    {lid : ScopeId} (hLid : lid ∈ scopeIdsOf frame.body)
    {loop : ScopeId} {si : Nat} (hSi : stmtIdxInLoop rest loop = some si)
    : ∃ stmt, ((scopeBodyOf progBody loop).getD [])[si]? = some stmt ∧ lid ∈ scopeIdsOf [stmt] := by
  induction hSMP generalizing frame rest lid loop si with
  | base si' ii =>
    have ⟨_, rfl⟩ := List.cons.inj hEq; simp [stmtIdxInLoop] at hSi
  | loop lb si' ii lid' parentFrame rest' hStmt' hMatch ih =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hEq
    have hLidP := mem_scopeIdsOf_of_getElem hStmt' (by simp [scopeIdsOf]; right; exact hLid)
    cases hpk : parentFrame.kind with
    | top => simp [stmtIdxInLoop, hpk] at hSi; exact ih rfl hLidP hSi
    | cond sid =>
      simp [stmtIdxInLoop, hpk] at hSi
      by_cases heq : sid = loop
      · subst heq; simp at hSi; subst hSi
        have hLBOf := smp_scopeBodyOf_loop hMatch hUniq parentFrame (List.Mem.head _) (by rw [hpk]; rfl)
        simp [hLBOf]
        exact ⟨Stmt.loop lid' lb, hStmt', by simp [scopeIdsOf]; right; exact hLid⟩
      · simp [heq] at hSi; exact ih rfl hLidP hSi
    | loop plid =>
      simp [stmtIdxInLoop, hpk] at hSi
      by_cases heq : plid = loop
      · subst heq; simp at hSi; subst hSi
        have hLBOf := smp_scopeBodyOf hMatch hUniq parentFrame (List.Mem.head _) hpk
        simp [hLBOf]
        exact ⟨Stmt.loop lid' lb, hStmt', by simp [scopeIdsOf]; right; exact hLid⟩
      · simp [heq] at hSi; exact ih rfl hLidP hSi
  | cond tb eb si' ii tid eid parentFrame rest' taken hStmt' hMatch ih =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hEq
    have hLidP := mem_scopeIdsOf_of_getElem hStmt' (by cases taken with | false => change lid ∈ scopeIdsOf [Stmt.cond tid eid tb eb]; simp only [scopeIdsOf, List.mem_cons, List.mem_append, List.mem_nil_iff, or_false]; aesop | true => change lid ∈ scopeIdsOf [Stmt.cond tid eid tb eb]; simp only [scopeIdsOf, List.mem_cons, List.mem_append, List.mem_nil_iff, or_false]; aesop)
    cases hpk : parentFrame.kind with
    | top => simp [stmtIdxInLoop, hpk] at hSi; exact ih rfl hLidP hSi
    | cond sid =>
      simp [stmtIdxInLoop, hpk] at hSi
      by_cases heq : sid = loop
      · subst heq; simp at hSi; subst hSi
        have hLBOf := smp_scopeBodyOf_loop hMatch hUniq parentFrame (List.Mem.head _) (by rw [hpk]; rfl)
        simp [hLBOf]
        exact ⟨Stmt.cond tid eid tb eb, hStmt', by cases taken with | false => change lid ∈ scopeIdsOf [Stmt.cond tid eid tb eb]; simp only [scopeIdsOf, List.mem_cons, List.mem_append, List.mem_nil_iff, or_false]; aesop | true => change lid ∈ scopeIdsOf [Stmt.cond tid eid tb eb]; simp only [scopeIdsOf, List.mem_cons, List.mem_append, List.mem_nil_iff, or_false]; aesop⟩
      · simp [heq] at hSi; exact ih rfl hLidP hSi
    | loop plid =>
      simp [stmtIdxInLoop, hpk] at hSi
      by_cases heq : plid = loop
      · subst heq; simp at hSi; subst hSi
        have hLBOf := smp_scopeBodyOf hMatch hUniq parentFrame (List.Mem.head _) hpk
        simp [hLBOf]
        exact ⟨Stmt.cond tid eid tb eb, hStmt', by cases taken with | false => change lid ∈ scopeIdsOf [Stmt.cond tid eid tb eb]; simp only [scopeIdsOf, List.mem_cons, List.mem_append, List.mem_nil_iff, or_false]; aesop | true => change lid ∈ scopeIdsOf [Stmt.cond tid eid tb eb]; simp only [scopeIdsOf, List.mem_cons, List.mem_append, List.mem_nil_iff, or_false]; aesop⟩
      · simp [heq] at hSi; exact ih rfl hLidP hSi

-- Top-level version: lid in top frame's body is inside progBody[si] where si = stmtIdxAtTop
theorem smp_lid_in_top_stmt {progBody : List Stmt}
    {stack : List Frame}
    (hSMP : StackMatchesProgram progBody stack) (_ : UniqueScopeIds progBody)
    {frame : Frame} {rest : List Frame} (hEq : stack = frame :: rest)
    {lid : ScopeId} (hLid : lid ∈ scopeIdsOf frame.body)
    {si : Nat} (hSi : stmtIdxAtTop rest = some si)
    : ∃ stmt, progBody[si]? = some stmt ∧ lid ∈ scopeIdsOf [stmt] := by
  induction hSMP generalizing frame rest lid si with
  | base si' ii =>
    have ⟨_, rfl⟩ := List.cons.inj hEq; simp [stmtIdxAtTop] at hSi
  | loop lb si' ii lid' parentFrame rest' hStmt' hMatch ih =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hEq
    have hLidP := mem_scopeIdsOf_of_getElem hStmt' (by simp [scopeIdsOf]; right; exact hLid)
    cases hpk : parentFrame.kind with
    | top => simp [stmtIdxAtTop, hpk] at hSi; subst hSi
             -- parentFrame.kind = .top, so by SMP, parentFrame.body = progBody
             have hBodyEq : parentFrame.body = progBody := by
               cases hMatch with | base _ _ => rfl | _ => simp at *
             rw [← hBodyEq]
             exact ⟨Stmt.loop lid' lb, hStmt', by simp [scopeIdsOf]; right; exact hLid⟩
    | cond _ | loop _ => simp [stmtIdxAtTop, hpk] at hSi; exact ih rfl hLidP hSi
  | cond tb eb si' ii tid eid parentFrame rest' taken hStmt' hMatch ih =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hEq
    have hLidP : lid ∈ scopeIdsOf parentFrame.body :=
      mem_scopeIdsOf_of_getElem hStmt' (by cases taken <;> (simp [scopeIdsOf, List.mem_append]; aesop))
    cases hpk : parentFrame.kind with
    | top => simp [stmtIdxAtTop, hpk] at hSi; subst hSi
             have hBodyEq : parentFrame.body = progBody := by
               cases hMatch with | base _ _ => rfl | _ => simp at *
             rw [← hBodyEq]
             exact ⟨Stmt.cond tid eid tb eb, hStmt', by cases taken <;> (simp [scopeIdsOf, List.mem_append]; aesop)⟩
    | cond _ | loop _ => simp [stmtIdxAtTop, hpk] at hSi; exact ih rfl hLidP hSi

-- If lid ∈ scopeIdsOf frame.body and lid ∈ scopeIdsOf(scopeBodyOf progBody olid),

-- If lid ∈ scopeIdsOf frame.body and lid ∈ scopeIdsOf(scopeBodyOf progBody olid),
-- then olid ∈ enclosingLoopsFromStack (frame :: rest).
-- (olid can't be in frame.body because that would create a cycle with UniqueScopeIds
-- when combined with the fact that lid is a loop header at frame.body[frame.stmtIdx].)
-- A loop ID is not in its own body (generalized from lid_not_in_own_body)
private theorem scopeBodyOf_not_self_mem {body : List Stmt} (hUniq : UniqueScopeIds body)
    {lid : ScopeId} {lb : List Stmt} (h : scopeBodyOf body lid = some lb)
    : lid ∉ scopeIdsOf lb := by
  induction hUniq with
  | nil => simp [scopeBodyOf] at h
  | block _ _ _ ih => simp [scopeBodyOf] at h; exact ih h
  | loop lid' body' rest' hNotBody hNotRest hDisj hBody hRest ih_body ih_rest =>
    simp [scopeBodyOf] at h
    by_cases heq : lid' = lid
    · subst heq; simp at h; subst h; exact hNotBody
    · simp [heq] at h
      cases hb : scopeBodyOf body' lid with
      | some v => simp [hb] at h; subst h; exact ih_body hb
      | none => simp [hb] at h; exact ih_rest h
  | cond thenId' elseId' tb eb rest _ hTnTb _ _ _ hEnEb _ hTbDisj hEbDisj hTb hEb hRest ih_tb ih_eb ih_rest =>
    simp [scopeBodyOf] at h
    by_cases ht : thenId' = lid
    · subst ht; simp at h; subst h; exact hTnTb
    · simp [ht] at h
      by_cases he : elseId' = lid
      · subst he; simp at h; subst h; exact hEnEb
      · simp [he] at h
        cases hb1 : scopeBodyOf tb lid with
        | some v => simp [hb1] at h; subst h; exact ih_tb hb1
        | none =>
          simp [hb1] at h
          cases hb2 : scopeBodyOf eb lid with
          | some v => simp [hb2] at h; subst h; exact ih_eb hb2
          | none => simp [hb2] at h; exact ih_rest h

theorem scopeIdsOf_disjoint_stmts {body : List Stmt} (hUniq : UniqueScopeIds body)
    {i j : Nat} {s1 s2 : Stmt} (hi : body[i]? = some s1) (hj : body[j]? = some s2) (hne : i ≠ j)
    {lid : ScopeId} (h1 : lid ∈ scopeIdsOf [s1]) (h2 : lid ∈ scopeIdsOf [s2]) : False := by
  induction hUniq generalizing i j with
  | nil => simp at hi
  | block _ _ _ ih =>
    cases i with
    | zero => simp at hi; subst hi; simp [scopeIdsOf] at h1
    | succ n => cases j with
      | zero => simp at hj; subst hj; simp [scopeIdsOf] at h2
      | succ m => simp at hi hj hne; exact ih hi hj hne
  | loop lid' body' rest' hNotBody hNotRest hDisj hBody hRest ih_body ih_rest =>
    cases i with
    | zero => cases j with
      | zero => exact hne rfl
      | succ m =>
        simp at hi hj; obtain ⟨rfl, rfl⟩ := hi
        -- lid ∈ scopeIdsOf [Stmt.loop lid' body'] and lid ∈ scopeIdsOf [rest'[m]]
        have hInRest := mem_scopeIdsOf_of_getElem hj h2
        simp [scopeIdsOf] at h1; rcases h1 with rfl | h1
        · exact hNotRest hInRest
        · exact hDisj lid h1 hInRest
    | succ n => cases j with
      | zero =>
        simp at hi hj; obtain ⟨rfl, rfl⟩ := hj
        have hInRest := mem_scopeIdsOf_of_getElem hi h1
        simp [scopeIdsOf] at h2; rcases h2 with rfl | h2
        · exact hNotRest hInRest
        · exact hDisj lid h2 hInRest
      | succ m => simp at hi hj hne; exact ih_rest hi hj hne
  | cond thenId' elseId' tb eb rest _ _ _ hTnR _ _ hEnR hTbDisj hEbDisj hTb hEb hRest ih_tb ih_eb ih_rest =>
    cases i with
    | zero => cases j with
      | zero => exact hne rfl
      | succ m =>
        simp at hi; obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        simp at hj
        have hInRest := mem_scopeIdsOf_of_getElem hj h2
        simp only [scopeIdsOf, List.mem_cons, List.mem_append, List.mem_nil_iff, or_false] at h1
        rcases h1 with (rfl | rfl | h1) | h1
        · exact hTnR hInRest
        · exact hEnR hInRest
        · exact (hTbDisj lid h1).2 hInRest
        · exact hEbDisj lid h1 hInRest
    | succ n => cases j with
      | zero =>
        simp at hj; obtain ⟨rfl, rfl, rfl, rfl⟩ := hj
        simp at hi
        have hInRest := mem_scopeIdsOf_of_getElem hi h1
        simp only [scopeIdsOf, List.mem_cons, List.mem_append, List.mem_nil_iff, or_false] at h2
        rcases h2 with (rfl | rfl | h2) | h2
        · exact hTnR hInRest
        · exact hEnR hInRest
        · exact (hTbDisj lid h2).2 hInRest
        · exact hEbDisj lid h2 hInRest
      | succ m => simp at hi hj hne; exact ih_rest hi hj hne

private theorem uniqueScopeIds_cond_disjoint {body : List Stmt} (hUniq : UniqueScopeIds body)
    {i : Nat} {thenId elseId : ScopeId} {tb eb : List Stmt}
    (hi : body[i]? = some (Stmt.cond thenId elseId tb eb))
    : ∀ x, x ∈ scopeIdsOf tb → x ∉ scopeIdsOf eb := by
  induction hUniq generalizing i with
  | nil => simp at hi
  | block _ _ _ ih => cases i <;> aesop
  | loop _ _ _ _ _ _ _ _ _ ih_rest => cases i <;> aesop
  | cond _ _ _ _ _ _ _ _ _ _ _ _ hTbDisj _ _ _ _ _ _ ih_rest =>
    cases i with
    | zero => simp at hi; obtain ⟨rfl, rfl, rfl, rfl⟩ := hi; intro x hx; exact (hTbDisj x hx).1
    | succ n => simp at hi; exact ih_rest hi

private theorem scopeBodyOf_at_same_stmt {body : List Stmt}
    (hUniq : UniqueScopeIds body)
    {olid : ScopeId} {ob : List Stmt} (hOB : scopeBodyOf body olid = some ob)
    {lid : ScopeId} (hLidOb : lid ∈ scopeIdsOf ob)
    {i : Nat} {s : Stmt} (hi : body[i]? = some s) (hLidS : lid ∈ scopeIdsOf [s])
    (hOlidNotS : olid ∉ scopeIdsOf [s])
    : False := by
  induction hUniq generalizing i olid ob with
  | nil => simp [scopeBodyOf] at hOB
  | block _ rest _ ih =>
    cases i with
    | zero => simp at hi; subst hi; simp [scopeIdsOf] at hLidS
    | succ n => simp at hi; simp [scopeBodyOf] at hOB; exact ih hOB hLidOb hi hOlidNotS
  | loop lid' body' rest' hNotBody hNotRest hDisj hBody hRest ih_body ih_rest =>
    simp [scopeBodyOf] at hOB
    by_cases heq : lid' = olid
    · subst heq; simp at hOB; subst hOB
      cases i with
      | zero => simp at hi; obtain ⟨rfl, rfl⟩ := hi; exact hOlidNotS (by simp [scopeIdsOf])
      | succ n => simp at hi; exact hDisj lid hLidOb (mem_scopeIdsOf_of_getElem hi hLidS)
    · simp [heq] at hOB
      cases hb : scopeBodyOf body' olid with
      | some val =>
        simp [hb] at hOB; subst hOB
        cases i with
        | zero =>
          simp at hi; obtain ⟨rfl, rfl⟩ := hi
          exact hOlidNotS (by simp [scopeIdsOf]; right; exact scopeBodyOf_mem_scopeIdsOf hb)
        | succ n =>
          simp at hi; exact hDisj lid (scopeBodyOf_subset hb lid hLidOb) (mem_scopeIdsOf_of_getElem hi hLidS)
      | none =>
        simp [hb] at hOB
        cases i with
        | zero =>
          simp at hi; obtain ⟨rfl, rfl⟩ := hi; simp [scopeIdsOf] at hLidS
          rcases hLidS with rfl | hLidS
          · exact hNotRest (scopeBodyOf_subset hOB lid hLidOb)
          · exact hDisj lid hLidS (scopeBodyOf_subset hOB lid hLidOb)
        | succ n => simp at hi; exact ih_rest hOB hLidOb hi hOlidNotS
  | cond thenId' elseId' tb eb rest hNe' hTnTb hTnEb hTnR hEnTb hEnEb hEnR hTbDisj hEbDisj hTb hEb hRest ih_tb ih_eb ih_rest =>
    simp [scopeBodyOf] at hOB
    by_cases htEq : thenId' = olid
    · subst htEq; simp at hOB; subst hOB
      cases i with
      | zero =>
        simp at hi; obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        exact hOlidNotS (by simp [scopeIdsOf])
      | succ n =>
        simp at hi
        have hInRest := mem_scopeIdsOf_of_getElem hi hLidS
        exact (hTbDisj lid hLidOb).2 hInRest
    · simp [htEq] at hOB
      by_cases heEq : elseId' = olid
      · subst heEq; simp at hOB; subst hOB
        cases i with
        | zero =>
          simp at hi; obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
          exact hOlidNotS (by simp [scopeIdsOf])
        | succ n =>
          simp at hi
          have hInRest := mem_scopeIdsOf_of_getElem hi hLidS
          exact hEbDisj lid hLidOb hInRest
      · simp [heEq] at hOB
        cases hb1 : scopeBodyOf tb olid with
        | some val =>
          simp [hb1] at hOB; subst hOB
          cases i with
          | zero =>
            simp at hi; obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
            exact hOlidNotS (show olid ∈ scopeIdsOf [Stmt.cond thenId' elseId' tb eb] from by
              unfold scopeIdsOf; apply List.mem_append_left; apply List.mem_cons_of_mem
              apply List.mem_cons_of_mem; apply List.mem_append_left
              exact scopeBodyOf_mem_scopeIdsOf hb1)
          | succ n =>
            simp at hi
            exact (hTbDisj lid (scopeBodyOf_subset hb1 lid hLidOb)).2 (mem_scopeIdsOf_of_getElem hi hLidS)
        | none =>
          simp [hb1] at hOB
          cases hb2 : scopeBodyOf eb olid with
          | some val =>
            simp [hb2] at hOB; subst hOB
            cases i with
            | zero =>
              simp at hi; obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
              exact hOlidNotS (show olid ∈ scopeIdsOf [Stmt.cond thenId' elseId' tb eb] from by
                unfold scopeIdsOf; apply List.mem_append_left; apply List.mem_cons_of_mem
                apply List.mem_cons_of_mem; apply List.mem_append_right
                exact scopeBodyOf_mem_scopeIdsOf hb2)
            | succ n =>
              simp at hi
              exact hEbDisj lid (scopeBodyOf_subset hb2 lid hLidOb) (mem_scopeIdsOf_of_getElem hi hLidS)
          | none =>
            simp [hb2] at hOB
            cases i with
            | zero =>
              simp at hi; obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
              simp only [scopeIdsOf, List.mem_cons, List.mem_append, List.mem_nil_iff, or_false] at hLidS
              rcases hLidS with (rfl | rfl | hLidS) | hLidS
              · exact hTnR (scopeBodyOf_subset hOB lid hLidOb)
              · exact hEnR (scopeBodyOf_subset hOB lid hLidOb)
              · exact (hTbDisj lid hLidS).2 (scopeBodyOf_subset hOB lid hLidOb)
              · exact hEbDisj lid hLidS (scopeBodyOf_subset hOB lid hLidOb)
            | succ n => simp at hi; exact ih_rest hOB hLidOb hi hOlidNotS

private theorem smp_not_in_frame_enclosing {progBody : List Stmt}
    {stack : List Frame}
    (hSMP : StackMatchesProgram progBody stack) (hUniq : UniqueScopeIds progBody)
    {frame : Frame} {rest : List Frame} (hEq : stack = frame :: rest)
    {lid : ScopeId} (hLidIn : lid ∈ scopeIdsOf frame.body)
    {olid : ScopeId} (hEnc : lid ∈ scopeIdsOf ((scopeBodyOf progBody olid).getD []))
    (hOlidNotIn : olid ∉ scopeIdsOf frame.body)
    : olid ∈ enclosingLoopsFromStack stack := by
  induction hSMP generalizing frame rest lid olid with
  | base si ii =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hEq
    exfalso; apply hOlidNotIn
    cases hOB : scopeBodyOf progBody olid with
    | none => exact absurd hEnc (by simp [hOB, scopeIdsOf])
    | some olBody => exact scopeBodyOf_mem_scopeIdsOf hOB
  | loop lb si ii lid2 pf rest2 hStmt2 hMatch ih =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hEq
    have hLidPf : lid ∈ scopeIdsOf pf.body :=
      mem_scopeIdsOf_of_getElem hStmt2 (by simp [scopeIdsOf]; right; exact hLidIn)
    by_cases heq : olid = lid2
    · subst heq; simp [enclosingLoopsFromStack]
    · by_cases hPf : olid ∈ scopeIdsOf pf.body
      · exfalso
        have hNotAtStmt : olid ∉ scopeIdsOf [Stmt.loop lid2 lb] := by
          simp [scopeIdsOf]; exact ⟨heq, hOlidNotIn⟩
        have hPfUniq := smp_uniqueScopeIds hMatch hUniq pf (List.Mem.head _)
        have hAgree := smp_scopeBodyOf_agree hMatch hUniq pf (List.Mem.head _) olid hPf
        cases hOB : scopeBodyOf progBody olid with
        | none => exact absurd hEnc (by simp [hOB, scopeIdsOf])
        | some ob =>
          have hOBpf : scopeBodyOf pf.body olid = some ob := by rwa [hAgree] at hOB
          have hLidOb : lid ∈ scopeIdsOf ob := by simp [hOB] at hEnc; exact hEnc
          exact scopeBodyOf_at_same_stmt hPfUniq hOBpf hLidOb hStmt2
            (by simp [scopeIdsOf]; right; exact hLidIn) hNotAtStmt
      · have hmem := ih rfl hLidPf hEnc hPf
        simp only [enclosingLoopsFromStack] at hmem ⊢
        exact List.mem_cons_of_mem _ hmem
  | cond tb eb si ii tid eid pf rest2 taken hStmt2 hMatch ih =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hEq
    cases taken with
    | true =>
      simp at hLidIn hOlidNotIn ⊢
      have hLidPf : lid ∈ scopeIdsOf pf.body :=
        mem_scopeIdsOf_of_getElem hStmt2 (by simp [scopeIdsOf, List.mem_append]; right; right; left; exact hLidIn)
      by_cases heq : olid = tid
      · subst heq; simp [enclosingLoopsFromStack]
      · by_cases hPf : olid ∈ scopeIdsOf pf.body
        · exfalso
          have hPfUniq := smp_uniqueScopeIds hMatch hUniq pf (List.Mem.head _)
          have hAgree := smp_scopeBodyOf_agree hMatch hUniq pf (List.Mem.head _) olid hPf
          cases hOB : scopeBodyOf progBody olid with
          | none => exact absurd hEnc (by simp [hOB, scopeIdsOf])
          | some ob =>
            have hOBpf : scopeBodyOf pf.body olid = some ob := by rwa [hAgree] at hOB
            have hLidOb : lid ∈ scopeIdsOf ob := by simp [hOB] at hEnc; exact hEnc
            by_cases hAtStmt : olid ∈ scopeIdsOf [Stmt.cond tid eid tb eb]
            · simp only [scopeIdsOf, List.mem_cons, List.mem_append, List.mem_nil_iff, or_false] at hAtStmt
              rcases hAtStmt with (rfl | rfl | hAtStmt) | hAtStmt
              · exact absurd rfl heq
              · -- olid = eid: scopeBodyOf pf.body eid = some eb, lid ∈ eb contradicts lid ∈ tb
                have hEBOf := scopeBodyOf_of_getElem_condFalse hStmt2 hPfUniq
                rw [hEBOf] at hOBpf; cases hOBpf
                exact (uniqueScopeIds_cond_disjoint hPfUniq hStmt2) lid hLidIn hLidOb
              · -- olid ∈ scopeIdsOf tb = frame.body
                exact hOlidNotIn hAtStmt
              · -- olid ∈ scopeIdsOf eb
                have hCondDisj := uniqueScopeIds_cond_disjoint hPfUniq hStmt2
                have hDesc := scopeBodyOf_descend_condFalse hStmt2 hAtStmt hPfUniq
                rw [hDesc] at hOBpf
                exact hCondDisj lid hLidIn (scopeBodyOf_subset hOBpf lid hLidOb)
            · exact scopeBodyOf_at_same_stmt hPfUniq hOBpf hLidOb hStmt2
                (show lid ∈ scopeIdsOf [Stmt.cond tid eid tb eb] from by
                  unfold scopeIdsOf; apply List.mem_append_left; apply List.mem_cons_of_mem
                  apply List.mem_cons_of_mem; apply List.mem_append_left; exact hLidIn) hAtStmt
        · have hmem := ih rfl hLidPf hEnc hPf
          simp only [enclosingLoopsFromStack] at hmem ⊢
          exact List.mem_cons_of_mem _ hmem
    | false =>
      simp at hLidIn hOlidNotIn ⊢
      have hLidPf : lid ∈ scopeIdsOf pf.body :=
        mem_scopeIdsOf_of_getElem hStmt2 (show lid ∈ scopeIdsOf [Stmt.cond tid eid tb eb] from by
          unfold scopeIdsOf; apply List.mem_append_left; apply List.mem_cons_of_mem
          apply List.mem_cons_of_mem; apply List.mem_append_right; exact hLidIn)
      by_cases heq : olid = eid
      · subst heq; simp [enclosingLoopsFromStack]
      · by_cases hPf : olid ∈ scopeIdsOf pf.body
        · exfalso
          have hPfUniq := smp_uniqueScopeIds hMatch hUniq pf (List.Mem.head _)
          have hAgree := smp_scopeBodyOf_agree hMatch hUniq pf (List.Mem.head _) olid hPf
          cases hOB : scopeBodyOf progBody olid with
          | none => exact absurd hEnc (by simp [hOB, scopeIdsOf])
          | some ob =>
            have hOBpf : scopeBodyOf pf.body olid = some ob := by rwa [hAgree] at hOB
            have hLidOb : lid ∈ scopeIdsOf ob := by simp [hOB] at hEnc; exact hEnc
            by_cases hAtStmt : olid ∈ scopeIdsOf [Stmt.cond tid eid tb eb]
            · simp only [scopeIdsOf, List.mem_cons, List.mem_append, List.mem_nil_iff, or_false] at hAtStmt
              rcases hAtStmt with (rfl | rfl | hAtStmt) | hAtStmt
              · -- olid = tid: scopeBodyOf pf.body tid = some tb, lid ∈ tb contradicts lid ∈ eb
                have hTBOf := scopeBodyOf_of_getElem_condTrue hStmt2 hPfUniq
                rw [hTBOf] at hOBpf; cases hOBpf
                exact (uniqueScopeIds_cond_disjoint hPfUniq hStmt2) lid hLidOb hLidIn
              · exact absurd rfl heq
              · have hCondDisj := uniqueScopeIds_cond_disjoint hPfUniq hStmt2
                have hDesc := scopeBodyOf_descend_condTrue hStmt2 hAtStmt hPfUniq
                rw [hDesc] at hOBpf
                exact hCondDisj lid (scopeBodyOf_subset hOBpf lid hLidOb) hLidIn
              · exact hOlidNotIn hAtStmt
            · exact scopeBodyOf_at_same_stmt hPfUniq hOBpf hLidOb hStmt2
                (show lid ∈ scopeIdsOf [Stmt.cond tid eid tb eb] from by
                  unfold scopeIdsOf; apply List.mem_append_left; apply List.mem_cons_of_mem
                  apply List.mem_cons_of_mem; apply List.mem_append_right; exact hLidIn) hAtStmt
        · have hmem := ih rfl hLidPf hEnc hPf
          simp only [enclosingLoopsFromStack] at hmem ⊢
          exact List.mem_cons_of_mem _ hmem
theorem smp_ancestor_on_stack {progBody : List Stmt}
    {stack : List Frame}
    (hSMP : StackMatchesProgram progBody stack) (hUniq : UniqueScopeIds progBody)
    {frame : Frame} {rest : List Frame} (hEq : stack = frame :: rest)
    {lid : ScopeId} (hLidIn : lid ∈ scopeIdsOf frame.body)
    {loopBody : List Stmt} (hStmt : frame.body[frame.stmtIdx]? = some (Stmt.loop lid loopBody))
    {olid : ScopeId} (hEnc : lid ∈ scopeIdsOf ((scopeBodyOf progBody olid).getD []))
    (hNe : olid ≠ lid)
    : olid ∈ enclosingLoopsFromStack stack := by
  have hFUniq := smp_uniqueScopeIds hSMP hUniq frame (hEq ▸ List.Mem.head _)
  have hOlidNotIn : olid ∉ scopeIdsOf frame.body := by
    intro hOlIn
    have hAgree := smp_scopeBodyOf_agree hSMP hUniq frame (hEq ▸ List.Mem.head _) olid hOlIn
    cases hOB : scopeBodyOf progBody olid with
    | none => exact absurd hEnc (by simp [hOB, scopeIdsOf])
    | some ob =>
      have hOBf : scopeBodyOf frame.body olid = some ob := by rwa [hAgree] at hOB
      have hLidOb : lid ∈ scopeIdsOf ob := by simp [hOB] at hEnc; exact hEnc
      have hNotSelf := scopeBodyOf_not_self_mem hFUniq (scopeBodyOf_of_getElem hStmt hFUniq)
      exact scopeBodyOf_at_same_stmt hFUniq hOBf hLidOb hStmt
        (by simp [scopeIdsOf]) (by
          simp [scopeIdsOf]; exact ⟨hNe, fun h =>
            have hDesc := scopeBodyOf_descend_loop hStmt h hFUniq
            have hOBlb : scopeBodyOf loopBody olid = some ob := by rw [hDesc] at hOBf; exact hOBf
            hNotSelf (scopeBodyOf_subset hOBlb lid hLidOb)⟩)
  exact smp_not_in_frame_enclosing hSMP hUniq hEq hLidIn hEnc hOlidNotIn

-- condFalse variant: elseId enters elseBody
theorem smp_ancestor_on_stack_condFalse {progBody : List Stmt}
    {stack : List Frame}
    (hSMP : StackMatchesProgram progBody stack) (hUniq : UniqueScopeIds progBody)
    {frame : Frame} {rest : List Frame} (hEq : stack = frame :: rest)
    {elseId : ScopeId} (hElseIdIn : elseId ∈ scopeIdsOf frame.body)
    {thenId : ScopeId} {thenBody elseBody : List Stmt}
    (hStmt : frame.body[frame.stmtIdx]? = some (Stmt.cond thenId elseId thenBody elseBody))
    {olid : ScopeId} (hEnc : elseId ∈ scopeIdsOf ((scopeBodyOf progBody olid).getD []))
    (hNe : olid ≠ elseId)
    : olid ∈ enclosingLoopsFromStack stack := by
  have hFUniq := smp_uniqueScopeIds hSMP hUniq frame (hEq ▸ List.Mem.head _)
  have hOlidNotIn : olid ∉ scopeIdsOf frame.body := by
    intro hOlIn
    have hAgree := smp_scopeBodyOf_agree hSMP hUniq frame (hEq ▸ List.Mem.head _) olid hOlIn
    cases hOB : scopeBodyOf progBody olid with
    | none => exact absurd hEnc (by simp [hOB, scopeIdsOf])
    | some ob =>
      have hOBf : scopeBodyOf frame.body olid = some ob := by rwa [hAgree] at hOB
      have hElseIdOb : elseId ∈ scopeIdsOf ob := by simp [hOB] at hEnc; exact hEnc
      have hNotSelf := scopeBodyOf_not_self_mem hFUniq (scopeBodyOf_of_getElem_condFalse hStmt hFUniq)
      exact scopeBodyOf_at_same_stmt hFUniq hOBf hElseIdOb hStmt
        (by simp [scopeIdsOf]) (by
          simp [scopeIdsOf]
          have hElseNotThen := elseId_not_in_then_body hStmt hFUniq
          refine ⟨fun h => ?_, hNe, fun h => ?_, fun h => ?_⟩
          · -- olid = thenId: scopeBodyOf thenId = some thenBody, so elseId ∈ thenBody, contradiction
            subst h
            have hTBOf := scopeBodyOf_of_getElem_condTrue hStmt hFUniq
            rw [hTBOf] at hOBf; cases hOBf
            exact hElseNotThen hElseIdOb
          · -- olid ∈ scopeIdsOf thenBody: descend, get elseId ∈ thenBody, contradiction
            have hDesc := scopeBodyOf_descend_condTrue hStmt h hFUniq
            have hOBtb : scopeBodyOf thenBody olid = some ob := by rw [hDesc] at hOBf; exact hOBf
            exact hElseNotThen (scopeBodyOf_subset hOBtb elseId hElseIdOb)
          · -- olid ∈ scopeIdsOf elseBody: descend, get elseId ∈ elseBody, contradicts scopeBodyOf_not_self_mem
            have hDesc := scopeBodyOf_descend_condFalse hStmt h hFUniq
            have hOBeb : scopeBodyOf elseBody olid = some ob := by rw [hDesc] at hOBf; exact hOBf
            exact hNotSelf (scopeBodyOf_subset hOBeb elseId hElseIdOb))
  exact smp_not_in_frame_enclosing hSMP hUniq hEq hElseIdIn hEnc hOlidNotIn

private theorem uniqueScopeIds_of_loop_on_stack {progBody : List Stmt} {stack : List Frame}
    (hSMP : StackMatchesProgram progBody stack) (hUniq : UniqueScopeIds progBody)
    {loop : ScopeId} {si : Nat} (hSi : stmtIdxInLoop stack loop = some si)
    : UniqueScopeIds ((scopeBodyOf progBody loop).getD []) := by
  induction stack with
  | nil => simp [stmtIdxInLoop] at hSi
  | cons f rest ih =>
    cases hk : f.kind with
    | top => simp [stmtIdxInLoop, hk] at hSi; exact ih (by cases hSMP with | base => simp [stmtIdxInLoop] at hSi | _ => assumption) hSi
    | cond csid =>
      simp [stmtIdxInLoop, hk] at hSi
      by_cases heq : csid = loop
      · subst heq
        have hLBOf := smp_scopeBodyOf_loop hSMP hUniq f (List.Mem.head _) (by rw [hk]; rfl)
        simp [hLBOf]
        exact smp_uniqueScopeIds hSMP hUniq f (List.Mem.head _)
      · simp [heq] at hSi
        exact ih (by cases hSMP with | base => simp at hk | _ => assumption) hSi
    | loop flid =>
      simp [stmtIdxInLoop, hk] at hSi
      by_cases heq : flid = loop
      · subst heq
        have hLBOf := smp_scopeBodyOf hSMP hUniq f (List.Mem.head _) hk
        simp [hLBOf]
        exact smp_uniqueScopeIds hSMP hUniq f (List.Mem.head _)
      · simp [heq] at hSi
        exact ih (by cases hSMP with | base => simp at hk | _ => assumption) hSi

private theorem enclosing_subset_scopeIdsOf {progBody : List Stmt} {stack : List Frame}
    (hSMP : StackMatchesProgram progBody stack)
    : ∀ s, s ∈ enclosingLoopsFromStack stack → s ∈ scopeIdsOf progBody := by
  induction hSMP with
  | base si ii => intro s; simp [enclosingLoopsFromStack]
  | loop _ _ _ _ pf _ hStmt' hMatch ih =>
    intro s; simp [enclosingLoopsFromStack]
    intro h; rcases h with rfl | h
    · exact smp_loopIds_subset hMatch pf (List.Mem.head _) s
        (mem_scopeIdsOf_of_getElem hStmt' (by simp [scopeIdsOf]))
    · exact ih s h
  | cond tb eb si ii tid eid pf rest' taken hStmt' hMatch ih =>
    intro s; cases taken with
    | false =>
      simp [enclosingLoopsFromStack]
      intro h; rcases h with rfl | h
      · exact smp_loopIds_subset hMatch pf (List.Mem.head _) s
          (mem_scopeIdsOf_of_getElem hStmt' (by simp only [scopeIdsOf, List.mem_cons, List.mem_append, List.mem_nil_iff, or_false]; aesop))
      · exact ih s h
    | true =>
      simp [enclosingLoopsFromStack]
      intro h; rcases h with rfl | h
      · exact smp_loopIds_subset hMatch pf (List.Mem.head _) s
          (mem_scopeIdsOf_of_getElem hStmt' (by simp [scopeIdsOf]))
      · exact ih s h

private theorem stmtIdxInLoop_push_loop {loopBody : List Stmt} {si : Nat} {lid : ScopeId}
    {frame : Frame} {rest : List Frame} {loop : ScopeId} {val : Nat}
    (hNe : lid ≠ loop)
    (h : stmtIdxInLoop (⟨loopBody, si, .loop lid⟩ :: frame :: rest) loop = some val)
    : stmtIdxInLoop (frame :: rest) loop = some val := by
  simp [stmtIdxInLoop, hNe] at h; exact h

private theorem stmtIdxInLoop_push_frame {body : List Stmt} {si : Nat} {fk : FrameKind}
    {rest : List Frame} {loop : ScopeId} {val : Nat} {sid : ScopeId}
    (hFk : fk.loopId? = some sid) (hNe : sid ≠ loop)
    (h : stmtIdxInLoop (⟨body, si, fk⟩ :: rest) loop = some val)
    : stmtIdxInLoop rest loop = some val := by
  cases fk with
  | top => simp [FrameKind.loopId?] at hFk
  | loop lid => simp [FrameKind.loopId?] at hFk; subst hFk; simp [stmtIdxInLoop, hNe] at h; exact h
  | cond sid' => simp [FrameKind.loopId?] at hFk; subst hFk; simp [stmtIdxInLoop, hNe] at h; exact h

-- Factored lemma for loop entry (loopEnter, condTrue, condFalse)
private theorem specInv_loopEntry (spec : Program) (e : EngineId) (ss : SpecState)
    (hUniq : UniqueScopeIds spec.body) (hInv : SpecInv spec ss)
    (frame : Frame) (rest : List Frame) (sid : ScopeId) (loopBody : List Stmt)
    (newKind : FrameKind)
    (hStack : (ss.pc e).stack = frame :: rest)
    (hSidInBody : sid ∈ scopeIdsOf frame.body)
    (hSidNotOn : sid ∉ loopsOnStack ss e)
    (hSBOf : scopeBodyOf spec.body sid = some loopBody)
    (hSidNotInOwnBody : sid ∉ scopeIdsOf loopBody)
    (hAncestor : ∀ olid, sid ∈ scopeIdsOf ((scopeBodyOf spec.body olid).getD []) →
        olid ≠ sid → olid ∈ enclosingLoopsFromStack (frame :: rest))
    (hStmtAtIdx : ∃ s, frame.body[frame.stmtIdx]? = some s ∧ sid ∈ scopeIdsOf [s])
    (hNewKindSid : newKind.loopId? = some sid)
    (hSMP_new : StackMatchesProgram spec.body (⟨loopBody, 0, newKind⟩ :: frame :: rest))
    : SpecInv spec
        { ss with
          pc := funUpdate ss.pc e { stack := ⟨loopBody, 0, newKind⟩ :: frame :: rest, instrIdx := 0 }
          controlState := funUpdate ss.controlState e (spec.controlOp e sid (ss.controlState e))
          scopeEntryHistory := incrScopeEntryHistory ss e sid (enclosingLoopsFromStack (frame :: rest)) } := by
    have hSidNotOnStack : sid ∉ enclosingLoopsFromStack (frame :: rest) := by
      simp [loopsOnStack, hStack] at hSidNotOn; exact hSidNotOn
    -- Helper: enclosingLoopsFromStack for the new stack
    have hEncNew : enclosingLoopsFromStack (⟨loopBody, 0, newKind⟩ :: frame :: rest) =
        sid :: enclosingLoopsFromStack (frame :: rest) := by
      cases newKind <;> simp [FrameKind.loopId?] at hNewKindSid <;> subst hNewKindSid <;>
        simp [enclosingLoopsFromStack]
    -- Helper: stmtIdxInLoop for the new frame when sid = loop
    have hSiNew : stmtIdxInLoop (⟨loopBody, 0, newKind⟩ :: frame :: rest) sid = some 0 := by
      cases newKind <;> simp [FrameKind.loopId?] at hNewKindSid <;> subst hNewKindSid <;>
        simp [stmtIdxInLoop]
    -- Helper: stmtIdxInLoop push for sid ≠ loop
    have hSiPush : ∀ loop, sid ≠ loop →
        stmtIdxInLoop (⟨loopBody, 0, newKind⟩ :: frame :: rest) loop =
        stmtIdxInLoop (frame :: rest) loop := by
      intro loop hne
      cases newKind <;> simp [FrameKind.loopId?] at hNewKindSid <;> subst hNewKindSid <;>
        simp [stmtIdxInLoop, hne]
    -- Helper: stmtIdxAtTop push
    have hAtTopPush : stmtIdxAtTop (⟨loopBody, 0, newKind⟩ :: frame :: rest) =
        stmtIdxAtTop (frame :: rest) := by
      cases newKind <;> simp [FrameKind.loopId?] at hNewKindSid <;> subst hNewKindSid <;>
        simp [stmtIdxAtTop]
    constructor
    · -- selfHistory
      intro e'' lid' k hk1 hk2
      simp at hk2 ⊢
      by_cases he : e'' = e
      · by_cases hl : lid' = sid
        · subst he; subst hl
          simp [totalEntries, incrScopeEntryHistory_totalEntries] at hk2
          by_cases hk3 : k ≤ totalEntries ss e'' lid'
          · rw [incrScopeEntryHistory_self_ne (by simp [totalEntries] at hk3 ⊢; omega)
              (by simp [List.any_eq_true]; intro x hx hxeq hxk
                  exact absurd (by cases hxeq; exact hx) hSidNotOnStack)]
            exact hInv.selfHistory e'' lid' k hk1 hk3
          · have hkeq : k = totalEntries ss e'' lid' + 1 := by simp [totalEntries] at hk3 ⊢; omega
            rw [hkeq, incrScopeEntryHistory_self]
            have := hInv.zeroFuture e'' lid' (some lid') (totalEntries ss e'' lid' + 1) (by simp only [totalEntriesOpt]; omega)
            omega
        · subst he; rw [incrScopeEntryHistory_ne_sid hl]
          simp [totalEntries, incrScopeEntryHistory_ne_sid hl] at hk2
          exact hInv.selfHistory e'' lid' k hk1 hk2
      · rw [incrScopeEntryHistory_ne_engine he]
        simp [totalEntries, incrScopeEntryHistory_ne_engine he] at hk2
        exact hInv.selfHistory e'' lid' k hk1 hk2
    · -- cumulative
      intro e'' lid' olid hEnc
      simp only [cumExecs, totalEntries]
      by_cases he : e'' = e
      · -- same engine
        subst he
        by_cases hlid : lid' = sid
        · -- lid' = sid
          subst hlid
          by_cases holid : olid = lid'
          · -- self: olid = lid'
            subst holid
            simp [incrScopeEntryHistory_totalEntries]
            have hNotOn := hSidNotOn
            have hNewSelf : ∀ k, 1 ≤ k → k ≤ ss.scopeEntryHistory e'' olid none 1 + 1 →
                incrScopeEntryHistory ss e'' olid (enclosingLoopsFromStack (frame :: rest)) e'' olid (some olid) k = 1 := by
              intro k hk1 hk2
              by_cases hkle : k ≤ totalEntries ss e'' olid
              · rw [incrScopeEntryHistory_self_ne (by simp [totalEntries] at hkle ⊢; omega)
                  (by simp [List.any_eq_true]; intro x hx hxeq hxk
                      simp [loopsOnStack, hStack] at hNotOn
                      exact absurd (by cases hxeq; exact hx) hNotOn)]
                exact hInv.selfHistory e'' olid k hk1 hkle
              · have : k = totalEntries ss e'' olid + 1 := by simp [totalEntries] at hkle ⊢; omega
                rw [this, incrScopeEntryHistory_self]
                have := hInv.zeroFuture e'' olid (some olid) (totalEntries ss e'' olid + 1) (by simp only [totalEntriesOpt]; omega)
                omega
            suffices h : ∀ n, n ≤ ss.scopeEntryHistory e'' olid none 1 + 1 →
              (List.range n).foldl (fun acc k =>
                acc + incrScopeEntryHistory ss e'' olid (enclosingLoopsFromStack (frame :: rest)) e'' olid (some olid) (k + 1)) 0 = n by
              exact h _ (Nat.le_refl _)
            intro n hn; induction n with
            | zero => simp
            | succ m ih =>
              rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
                  ih (by omega), hNewSelf (m + 1) (by omega) (by omega)]
          · -- olid ≠ lid', olid contains lid'
            simp [incrScopeEntryHistory_ne_sid holid, incrScopeEntryHistory_totalEntries]
            by_cases hOlEnc : olid ∈ enclosingLoopsFromStack (frame :: rest)
            · have hOldCum := hInv.cumulative e'' lid' olid hEnc
              simp [cumExecs, totalEntries] at hOldCum
              have hTEpos : ss.scopeEntryHistory e'' olid none 1 > 0 :=
                hInv.activeLoopPos e'' olid (by simp [loopsOnStack, hStack]; exact hOlEnc)
              have hIncr := @foldl_add_incr_one
                (fun k => incrScopeEntryHistory ss e'' lid' (enclosingLoopsFromStack (frame :: rest)) e'' lid' (some olid) k)
                (fun k => ss.scopeEntryHistory e'' lid' (some olid) k)
                (ss.scopeEntryHistory e'' olid none 1)
                (ss.scopeEntryHistory e'' olid none 1 - 1)
                (by omega)
                (by simp only []
                    have hTE : ss.scopeEntryHistory e'' olid none 1 - 1 + 1 = ss.scopeEntryHistory e'' olid none 1 := by omega
                    rw [hTE]; simp [incrScopeEntryHistory, totalEntries]; intro _; exact ⟨olid, hOlEnc, rfl, rfl⟩)
                (by intro k hk hne; simp only []
                    simp [incrScopeEntryHistory, totalEntries]
                    exact ⟨fun h => absurd h holid, fun x hx hxeq hxk => by cases hxeq; omega⟩)
              rw [hOldCum] at hIncr; exact hIncr
            · have hOldCum := hInv.cumulative e'' lid' olid hEnc
              simp [cumExecs, totalEntries] at hOldCum
              have hSame : ∀ k, k ∈ List.range (ss.scopeEntryHistory e'' olid none 1) →
                  incrScopeEntryHistory ss e'' lid' (enclosingLoopsFromStack (frame :: rest)) e'' lid' (some olid) (k + 1) =
                  ss.scopeEntryHistory e'' lid' (some olid) (k + 1) := by
                intro k _; simp [incrScopeEntryHistory, totalEntries]
                exact ⟨fun h => absurd h holid, fun x hx hxeq hxk => by cases hxeq; exact absurd hx hOlEnc⟩
              have h1 := foldl_add_congr hSame
              have _ := h1.trans hOldCum
              exfalso; apply hOlEnc
              exact hAncestor olid hEnc (fun h => holid (h ▸ rfl))
        · -- lid' ≠ sid
          by_cases holid : olid = sid
          · subst holid
            simp [incrScopeEntryHistory_ne_sid hlid, incrScopeEntryHistory_totalEntries]
            rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
            have hZF := hInv.zeroFuture e'' lid' (some olid) (totalEntries ss e'' olid + 1)
              (by simp only [totalEntriesOpt]; omega); simp [totalEntries] at hZF; rw [hZF, Nat.add_zero]
            exact hInv.cumulative e'' lid' olid hEnc
          · simp [incrScopeEntryHistory_ne_sid hlid, incrScopeEntryHistory_ne_sid holid]
            exact hInv.cumulative e'' lid' olid hEnc
      · -- diff engine
        simp [incrScopeEntryHistory_ne_engine he]
        exact hInv.cumulative e'' lid' olid hEnc
    · -- zeroFuture
      intro e_1 lid_1 outerLoop k hk
      simp
      by_cases he : e_1 = e
      · subst he
        by_cases hl : lid_1 = sid
        · subst hl
          have hkSimp : ∀ os, os ≠ lid_1 → totalEntries
            { controlState := funUpdate ss.controlState e_1 (spec.controlOp e_1 lid_1 (ss.controlState e_1)),
              dataPathState := ss.dataPathState,
              pc := funUpdate ss.pc e_1 { stack := ⟨loopBody, 0, newKind⟩ :: frame :: rest, instrIdx := 0 },
              inflight := ss.inflight, rc := ss.rc,
              scopeEntryHistory := incrScopeEntryHistory ss e_1 lid_1 (enclosingLoopsFromStack (frame :: rest)) }
            e_1 os = totalEntries ss e_1 os := by
            intro os hne; simp [totalEntries, incrScopeEntryHistory_ne_sid hne]
          rw [incrScopeEntryHistory_beyond]
          · apply hInv.zeroFuture
            cases outerLoop with
            | none => simp [totalEntriesOpt] at hk ⊢; omega
            | some os =>
              simp [totalEntriesOpt] at hk ⊢
              by_cases hol : os = lid_1
              · subst hol; simp [totalEntries, incrScopeEntryHistory_totalEntries] at hk ⊢; omega
              · rw [hkSimp os hol] at hk; exact hk
          · -- hk_top: outerLoop = none → k > 1
            intro h; subst h; simp [totalEntriesOpt] at hk; omega
          · -- hk_self: outerLoop = some lid_1 → k > totalEntries + 1
            intro h
            cases outerLoop with
            | none => cases h
            | some os =>
              simp [totalEntriesOpt] at hk
              by_cases hol : os = lid_1
              · subst hol; simp [totalEntries, incrScopeEntryHistory_totalEntries] at hk ⊢; omega
              · cases h; exact absurd rfl hol
          · -- hk_enc
            intro outer _ h
            cases outerLoop with
            | none => cases h
            | some os =>
              simp [totalEntriesOpt] at hk
              by_cases hol : os = lid_1
              · subst hol; simp [totalEntries, incrScopeEntryHistory_totalEntries] at hk ⊢; cases h; omega
              · rw [hkSimp os hol] at hk; cases h; exact hk
        · rw [incrScopeEntryHistory_ne_sid hl]
          apply hInv.zeroFuture
          cases outerLoop with
          | none => simp [totalEntriesOpt] at hk ⊢; omega
          | some os =>
            simp [totalEntriesOpt, totalEntries] at hk ⊢
            exact Nat.lt_of_le_of_lt (by simp [incrScopeEntryHistory]; split <;> omega) hk
      · rw [incrScopeEntryHistory_ne_engine he]
        apply hInv.zeroFuture
        cases outerLoop with
        | none => simp [totalEntriesOpt] at hk ⊢; omega
        | some os =>
          simp [totalEntriesOpt, totalEntries, incrScopeEntryHistory_ne_engine he] at hk ⊢; omega
    · -- activeLoopPos
      intro e'' lid' hm
      simp [totalEntries]
      by_cases he : e'' = e
      · subst he; simp [loopsOnStack, funUpdate, hEncNew] at hm
        rcases hm with rfl | hm
        · -- lid' = sid
          simp [incrScopeEntryHistory_totalEntries]
        · by_cases hl : lid' = sid
          · subst hl; simp [incrScopeEntryHistory_totalEntries]
          · simp [incrScopeEntryHistory_ne_sid hl]
            exact hInv.activeLoopPos e'' lid' (by simp [loopsOnStack]; rw [hStack]; exact hm)
      · simp [loopsOnStack, funUpdate, he] at hm; simp [incrScopeEntryHistory_ne_engine he]
        exact hInv.activeLoopPos e'' lid' (by simp [loopsOnStack]; exact hm)
    · -- ancestorsActive
      intro e'' lid_1 loop hm hEnc
      by_cases he : e'' = e
      · subst he
        have hm' : lid_1 = sid ∨ lid_1 ∈ enclosingLoopsFromStack (frame :: rest) := by
          simp [loopsOnStack, funUpdate, hEncNew] at hm; exact hm
        suffices h : loop ∈ loopsOnStack ss e'' by
          simp [loopsOnStack, hStack] at h
          simp [loopsOnStack, funUpdate, hEncNew]
          right; exact h
        rcases hm' with rfl | hm'
        · -- lid_1 = sid
          have hSMP := hStack ▸ hInv.wellFormedPC e''
          have hNe : loop ≠ lid_1 := by
            intro heq; subst heq
            simp [hSBOf] at hEnc
            exact hSidNotInOwnBody hEnc
          have hAnc := hAncestor loop hEnc hNe
          simp [loopsOnStack, hStack]; exact hAnc
        · exact hInv.ancestorsActive e'' lid_1 loop
            (by simp [loopsOnStack, hStack]; exact hm') hEnc
      · have hmOld : lid_1 ∈ loopsOnStack ss e'' := by
          simp [loopsOnStack, funUpdate, he] at hm; simp [loopsOnStack]; exact hm
        have hRes := hInv.ancestorsActive e'' lid_1 loop hmOld hEnc
        simp [loopsOnStack, funUpdate, he] at hRes ⊢; exact hRes
    · -- zeroBeforeEntry
      intro e' lid_1 loop si j stmt hLoop hSi hJ hMem hLt
      simp
      by_cases he : e' = e
      · subst he
        simp only [funUpdate, ite_true, PC.stack_mk] at hSi
        simp only [totalEntries]
        have hLoop' : loop = sid ∨ loop ∈ enclosingLoopsFromStack (frame :: rest) := by
          simp only [loopsOnStack, funUpdate, ite_true, hEncNew,
            List.mem_cons] at hLoop
          exact hLoop
        by_cases hSidEq : sid = loop
        · -- loop = sid: stmtIdxInLoop finds the new frame, giving si = 0
          subst hSidEq
          rw [hSiNew] at hSi; cases hSi
          by_cases hl1 : lid_1 = sid
          · subst hl1; exfalso
            simp [hSBOf] at hJ
            exact hSidNotInOwnBody (mem_scopeIdsOf_of_getElem hJ hMem)
          · rw [incrScopeEntryHistory_ne_sid hl1, incrScopeEntryHistory_totalEntries]
            exact hInv.zeroFuture e' lid_1 (some sid) _ (by simp [totalEntriesOpt, totalEntries])
        · have hSiSimp : stmtIdxInLoop (frame :: rest) loop = some si := by
            rw [hSiPush loop hSidEq] at hSi; exact hSi
          rcases hLoop' with rfl | hLoop
          · exact absurd rfl hSidEq
          · -- loop on old stack
            by_cases hl1 : lid_1 = sid
            · subst hl1; exfalso
              have hSMP := hStack ▸ hInv.wellFormedPC e'
              have hLidInFrame : lid_1 ∈ scopeIdsOf frame.body := hSidInBody
              by_cases hfk : frame.kind.loopId? = some loop
              · have hLBOf := smp_scopeBodyOf_loop hSMP hUniq frame (List.Mem.head _) hfk
                have hLoopUniq := smp_uniqueScopeIds hSMP hUniq frame (List.Mem.head _)
                have hSiEq : si = frame.stmtIdx := by
                  cases hk : frame.kind <;> simp [FrameKind.loopId?, hk] at hfk <;>
                    (subst hfk; simp [stmtIdxInLoop, hk] at hSiSimp; exact hSiSimp.symm)
                subst hSiEq; rw [hLBOf, Option.getD_some] at hJ
                obtain ⟨s0, hs0, hsid0⟩ := hStmtAtIdx
                exact scopeIdsOf_disjoint_stmts hLoopUniq hs0 hJ (by omega) hsid0 hMem
              · have hSiRest : stmtIdxInLoop rest loop = some si := by
                  simp only [stmtIdxInLoop] at hSiSimp
                  revert hSiSimp; cases hk : frame.kind with
                  | top => exact id
                  | cond csid =>
                    have : csid ≠ loop := fun h => hfk (by rw [hk]; simp [FrameKind.loopId?, h])
                    simp [this]
                  | loop flid =>
                    have : flid ≠ loop := fun h => hfk (by rw [hk]; simp [FrameKind.loopId?, h])
                    simp [this]
                have ⟨stmt', hStmt', hLidAtSi⟩ := smp_lid_in_loop_stmt hSMP hUniq rfl hLidInFrame hSiRest
                exact scopeIdsOf_disjoint_stmts
                  (uniqueScopeIds_of_loop_on_stack hSMP hUniq hSiSimp) hStmt' hJ (by omega) hLidAtSi hMem
            · rw [incrScopeEntryHistory_ne_sid hl1]
              have hNotSid : loop ≠ sid :=
                fun heq => hSidNotOnStack (heq ▸ hLoop)
              rw [show incrScopeEntryHistory ss e' sid (enclosingLoopsFromStack (frame :: rest)) e' loop none 1 =
                  ss.scopeEntryHistory e' loop none 1 from by
                simp [incrScopeEntryHistory, hNotSid]]
              exact hInv.zeroBeforeEntry e' lid_1 loop si j stmt
                (by simp [loopsOnStack, hStack]; exact hLoop) (by rw [hStack]; exact hSiSimp) hJ hMem hLt
      · -- diff engine
        have hLoop' : loop ∈ loopsOnStack ss e' := by
          simp [loopsOnStack, funUpdate, he] at hLoop; simp [loopsOnStack]; exact hLoop
        have hSi' : stmtIdxInLoop (ss.pc e').stack loop = some si := by
          simp [funUpdate, he] at hSi; exact hSi
        simp only [totalEntries, incrScopeEntryHistory_ne_engine he]
        exact hInv.zeroBeforeEntry e' lid_1 loop si j stmt hLoop' hSi' hJ hMem hLt
    · -- zeroBeforeEntryTop
      intro e' lid_1 si j stmt hSi hJ hMem hLt
      by_cases he : e' = e
      · subst he; simp [funUpdate] at hSi
        rw [hAtTopPush] at hSi
        simp [stmtIdxAtTop] at hSi
        simp [totalEntries]
        by_cases hl : lid_1 = sid
        · subst hl; exfalso
          have hSMP := hStack ▸ hInv.wellFormedPC e'
          have hLidInFrame : lid_1 ∈ scopeIdsOf frame.body := hSidInBody
          cases hfk : frame.kind with
          | top =>
            simp [hfk] at hSi; subst hSi
            have hBodyEq : frame.body = spec.body := by
              cases hSMP with | base _ _ => rfl | _ => simp at *
            obtain ⟨s0, hs0, hsid0⟩ := hStmtAtIdx
            rw [hBodyEq] at hs0
            exact scopeIdsOf_disjoint_stmts hUniq hs0 hJ (by omega) hsid0 hMem
          | loop _ =>
            simp [hfk] at hSi
            have ⟨stmt', hStmt', hLidAtSi⟩ := smp_lid_in_top_stmt hSMP hUniq rfl hLidInFrame hSi
            exact scopeIdsOf_disjoint_stmts hUniq hStmt' hJ (by omega) hLidAtSi hMem
          | cond =>
            simp [hfk] at hSi
            have ⟨stmt', hStmt', hLidAtSi⟩ := smp_lid_in_top_stmt hSMP hUniq rfl hLidInFrame hSi
            exact scopeIdsOf_disjoint_stmts hUniq hStmt' hJ (by omega) hLidAtSi hMem
        · simp [incrScopeEntryHistory_ne_sid hl]
          exact hInv.zeroBeforeEntryTop e' lid_1 si j stmt (by rw [hStack]; exact hSi) hJ hMem hLt
      · simp [funUpdate, he] at hSi; simp [totalEntries, incrScopeEntryHistory_ne_engine he]
        exact hInv.zeroBeforeEntryTop e' lid_1 si j stmt hSi hJ hMem hLt
    · intro e'
      by_cases he : e' = e
      · simp [he]; exact hSMP_new
      · simp [he]; exact hInv.wellFormedPC e'
    · exact hInv.inflightInBody
    · exact hInv.inflightEngineEq

/-! ## UniqueInstrIds propagation through StackMatchesProgram -/

theorem uniqueInstrIds_of_getElem_loop_smp {engines : List EngineId} {body : List Stmt}
    {idx : Nat} {lid : ScopeId} {lb : List Stmt}
    (hIdx : body[idx]? = some (Stmt.loop lid lb)) (hUI : UniqueInstrIds engines body)
    : UniqueInstrIds engines lb := by
  induction hUI generalizing idx with
  | nil => simp at hIdx
  | block _ _ _ _ _ _ ih => cases idx with | zero => simp at hIdx | succ n => simp at hIdx; exact ih hIdx
  | loop _ _ _ _ hUIB _ _ ih_rest => cases idx <;> aesop
  | cond _ _ _ _ _ _ _ _ _ _ _ ih_rest => cases idx <;> aesop

theorem uniqueInstrIds_of_getElem_condTrue_smp {engines : List EngineId} {body : List Stmt}
    {idx : Nat} {thenId elseId : ScopeId} {tb eb : List Stmt}
    (hIdx : body[idx]? = some (Stmt.cond thenId elseId tb eb)) (hUI : UniqueInstrIds engines body)
    : UniqueInstrIds engines tb := by
  induction hUI generalizing idx with
  | nil => simp at hIdx
  | block _ _ _ _ _ _ ih => cases idx <;> aesop
  | loop _ _ _ _ _ _ _ ih_rest => cases idx <;> aesop
  | cond _ _ _ _ _ hUITb _ _ _ _ _ ih_rest => cases idx <;> aesop

theorem uniqueInstrIds_of_getElem_condFalse_smp {engines : List EngineId} {body : List Stmt}
    {idx : Nat} {thenId elseId : ScopeId} {tb eb : List Stmt}
    (hIdx : body[idx]? = some (Stmt.cond thenId elseId tb eb)) (hUI : UniqueInstrIds engines body)
    : UniqueInstrIds engines eb := by
  induction hUI generalizing idx with
  | nil => simp at hIdx
  | block _ _ _ _ _ _ ih => cases idx <;> aesop
  | loop _ _ _ _ _ _ _ ih_rest => cases idx <;> aesop
  | cond _ _ _ _ _ _ _ _ hUIEb _ _ ih_rest => cases idx <;> aesop

theorem smp_uniqueInstrIds {engines : List EngineId} {progBody : List Stmt} {stack : List Frame}
    (hSMP : StackMatchesProgram progBody stack)
    (hUI : UniqueInstrIds engines progBody)
    : ∀ f, f ∈ stack → UniqueInstrIds engines f.body := by
  induction hSMP with
  | base si ii => intro f hf; simp at hf; subst hf; exact hUI
  | loop lb si ii lid pf rest hStmt hMatch ih =>
    intro f hf; rcases List.mem_cons.mp hf with rfl | hf
    · exact uniqueInstrIds_of_getElem_loop_smp hStmt (ih pf (List.Mem.head _))
    · exact ih f hf
  | cond tb eb si ii tid eid pf rest taken hStmt hMatch ih =>
    intro f hf; rcases List.mem_cons.mp hf with rfl | hf
    · cases taken with
      | false => simp at hf ⊢; exact uniqueInstrIds_of_getElem_condFalse_smp hStmt (ih pf (List.Mem.head _))
      | true => simp at hf ⊢; exact uniqueInstrIds_of_getElem_condTrue_smp hStmt (ih pf (List.Mem.head _))
    · exact ih f hf

/-! ## instrEngine lifts through StackMatchesProgram -/

theorem instrEngine_lift_smp {engines : List EngineId} {progBody : List Stmt}
    {stack : List Frame} {instr : DataPathInstrId} {e : EngineId}
    (hSMP : StackMatchesProgram progBody stack)
    (hUI : UniqueInstrIds engines progBody)
    {frame : Frame} (hMem : frame ∈ stack)
    (hIE : instrEngine engines frame.body instr = some e)
    : instrEngine engines progBody instr = some e := by
  induction hSMP generalizing frame with
  | base si ii =>
    simp at hMem; subst hMem; exact hIE
  | loop loopBody si ii lid parentFrame rest' hStmt hMatch ih =>
    rcases List.mem_cons.mp hMem with rfl | hMemRest
    · have hSingle : instrEngine engines [Stmt.loop lid loopBody] instr = some e := by
        simp [instrEngine, hIE]
      have hUIParent := smp_uniqueInstrIds hMatch hUI parentFrame (List.Mem.head _)
      exact ih (List.Mem.head _) (instrEngine_of_getElem_rest hStmt hSingle hUIParent)
    · exact ih hMemRest hIE
  | cond thenBody elseBody si ii thenId elseId parentFrame rest' taken hStmt hMatch ih =>
    rcases List.mem_cons.mp hMem with rfl | hMemRest
    · have hUIParent := smp_uniqueInstrIds hMatch hUI parentFrame (List.Mem.head _)
      cases taken with
      | false =>
        simp at hIE ⊢
        -- taken = false, frame body = elseBody
        have hInEb : instrInBody engines elseBody instr = true := by
          by_contra hc; simp at hc; exact absurd hIE (by rw [instrEngine_none_of_not_in_body hc]; simp)
        have hNotInTb : instrInBody engines thenBody instr = false :=
          uniqueInstrIds_cond_instrDisjoint' hUIParent hStmt hInEb
        have hTbNone : instrEngine engines thenBody instr = none :=
          instrEngine_none_of_not_in_body hNotInTb
        have hSingle : instrEngine engines [Stmt.cond thenId elseId thenBody elseBody] instr = some e := by
          simp [instrEngine, hTbNone, hIE]
        exact ih (List.Mem.head _) (instrEngine_of_getElem_rest hStmt hSingle hUIParent)
      | true =>
        simp at hIE
        -- taken = true, frame body = thenBody
        have hSingle : instrEngine engines [Stmt.cond thenId elseId thenBody elseBody] instr = some e := by
          simp [instrEngine, hIE]
        exact ih (List.Mem.head _) (instrEngine_of_getElem_rest hStmt hSingle hUIParent)
    · exact ih hMemRest hIE

theorem smp_instrInBody_lift {engines : List EngineId} {progBody : List Stmt} {stack : List Frame}
    (hSMP : StackMatchesProgram progBody stack)
    {fr : Frame} (hMem : fr ∈ stack)
    {i : DataPathInstrId} (hIn : instrInBody engines fr.body i = true)
    : instrInBody engines progBody i = true := by
  induction hSMP generalizing fr with
  | base _ _ => simp at hMem; subst hMem; exact hIn
  | loop lb _ _ lid pf rest' hStmt' hMatch ih =>
    rcases List.mem_cons.mp hMem with rfl | hMem'
    · exact ih (List.Mem.head _)
        (instrInBody_of_getElem_rest hStmt' (by simp [instrInBody]; exact hIn))
    · exact ih hMem' hIn
  | cond tb eb _ _ tid eid pf rest' taken hStmt' hMatch ih =>
    rcases List.mem_cons.mp hMem with rfl | hMem'
    · exact ih (List.Mem.head _)
        (instrInBody_of_getElem_rest hStmt' (by
          cases taken with
          | false => simp at hIn; simp [instrInBody]; right; exact hIn
          | true => simp at hIn; simp [instrInBody]; left; exact hIn))
    · exact ih hMem' hIn

private theorem findInBlock_isSome {engines : List EngineId} {f : EngineId → List DataPathInstrId}
    {e : EngineId} {i : DataPathInstrId}
    (hE : e ∈ engines) (hMem : i ∈ f e)
    : (findInBlock engines f i).isSome = true := by
  induction engines with
  | nil => exact absurd hE List.not_mem_nil
  | cons x xs ih =>
    simp [findInBlock]; by_cases hx : i ∈ f x
    · simp [hx]
    · simp [hx]; rcases List.mem_cons.mp hE with rfl | h
      · exact absurd hMem hx
      · exact ih h

private theorem specInv_advance_top (spec : Program) (e : EngineId) (ss : SpecState)
    (_hUniq : UniqueScopeIds spec.body)
    (hInv : SpecInv spec ss)
    (frame : Frame) (rest : List Frame)
    (hStack : (ss.pc e).stack = frame :: rest)
    : SpecInv spec { ss with
        pc := funUpdate ss.pc e
          { stack := ⟨frame.body, frame.stmtIdx + 1, frame.kind⟩ :: rest, instrIdx := 0 } } := by
  have hLoops : ∀ e', loopsOnStack { ss with
      pc := funUpdate ss.pc e { stack := ⟨frame.body, frame.stmtIdx + 1, frame.kind⟩ :: rest, instrIdx := 0 } } e' = loopsOnStack ss e' := by
    intro e'; by_cases he : e' = e
    · subst he; simp [loopsOnStack, funUpdate, enclosing_change_stmtIdx, hStack]
    · simp [loopsOnStack, funUpdate, he]
  have hStk : ∀ e', (funUpdate ss.pc e { stack := ⟨frame.body, frame.stmtIdx + 1, frame.kind⟩ :: rest, instrIdx := 0 } e').stack = (ss.pc e').stack ∨
      (e' = e ∧ (funUpdate ss.pc e { stack := ⟨frame.body, frame.stmtIdx + 1, frame.kind⟩ :: rest, instrIdx := 0 } e').stack = ⟨frame.body, frame.stmtIdx + 1, frame.kind⟩ :: rest) := by
    intro e'; by_cases he : e' = e <;> simp [funUpdate, he]
  exact { hInv with
    activeLoopPos := by intro e' lid hm; rw [hLoops] at hm; exact hInv.activeLoopPos e' lid hm
    ancestorsActive := by intro e' lid loop hm hEnc; rw [hLoops] at hm ⊢; exact hInv.ancestorsActive e' lid loop hm hEnc
    zeroBeforeEntry := by
      intro e' lid loop si j stmt hLoop hSi hJ hMem hLt; rw [hLoops] at hLoop
      rcases hStk e' with h | ⟨he, h⟩
      · rw [h] at hSi; exact hInv.zeroBeforeEntry e' lid loop si j stmt hLoop hSi hJ hMem hLt
      · subst he; rw [h] at hSi
        match hfk : frame.kind with
        | .top => simp [stmtIdxInLoop, hfk] at hSi
                  exact hInv.zeroBeforeEntry e' lid loop si j stmt hLoop (by rw [hStack]; simp [stmtIdxInLoop, hfk]; exact hSi) hJ hMem hLt
        | .cond sid | .loop sid =>
          simp [stmtIdxInLoop, hfk] at hSi
          by_cases hfs : sid = loop
          · subst hfs; simp at hSi; subst hSi
            exact hInv.zeroBeforeEntry e' lid sid frame.stmtIdx j stmt hLoop (by rw [hStack]; simp [stmtIdxInLoop, hfk]) hJ hMem (by omega)
          · simp [hfs] at hSi
            exact hInv.zeroBeforeEntry e' lid loop si j stmt hLoop (by rw [hStack]; simp [stmtIdxInLoop, hfk, hfs]; exact hSi) hJ hMem hLt
    zeroBeforeEntryTop := by
      intro e' lid si j stmt hSi hJ hMem hLt
      rcases hStk e' with h | ⟨he, h⟩
      · rw [h] at hSi; exact hInv.zeroBeforeEntryTop e' lid si j stmt hSi hJ hMem hLt
      · subst he; rw [h] at hSi
        match hfk : frame.kind with
        | .top => simp [stmtIdxAtTop, hfk] at hSi; subst hSi
                  exact hInv.zeroBeforeEntryTop e' lid frame.stmtIdx j stmt (by rw [hStack]; simp [stmtIdxAtTop, hfk]) hJ hMem (by omega)
        | .loop _ | .cond _ =>
          rw [stmtIdxAtTop_change_nontop (by simp [hfk])] at hSi
          exact hInv.zeroBeforeEntryTop e' lid si j stmt (by rw [hStack]; exact hSi) hJ hMem hLt
    wellFormedPC := by
      intro e'; by_cases he : e' = e
      · subst he; simp [funUpdate]; exact smp_change_top_stmtIdx (hStack ▸ hInv.wellFormedPC e') _ 0
      · simp [funUpdate, he]; exact hInv.wellFormedPC e' }

theorem specInv_step (spec : Program) (e : EngineId) (ss ss' : SpecState)
    (hUniq : UniqueScopeIds spec.body)
    (hInv : SpecInv spec ss) (hStep : SpecStep spec e ss ss')
    (hUniqueInstr : UniqueInstrIds spec.engines spec.body := by assumption)
    : SpecInv spec ss' := by
  cases hStep with
  | commit =>
    rename_i _ idx instr hIdx
    exact specInv_of_same_history hInv rfl rfl (by
      intro e' i ph h; simp [funUpdate] at h
      by_cases he : e' = e
      · subst he; simp at h
        -- (i, ph) ∈ l.set idx (instr, committed) → (i, _) ∈ l
        have hmem : ∀ {α : Type} {l : List α} {n : Nat} {a x : α},
            x ∈ l.set n a → x = a ∨ x ∈ l := by
          intro α l n a x hx
          induction l generalizing n with
          | nil => simp [List.set] at hx
          | cons hd tl ih =>
            cases n with
            | zero => simp [List.set] at hx; rcases hx with rfl | h; left; rfl; right; exact List.Mem.tail _ h
            | succ k => simp [List.set] at hx; rcases hx with rfl | h
                        · right; exact List.Mem.head _
                        · rcases ih h with rfl | h'; left; rfl; right; exact List.Mem.tail _ h'
        rcases hmem h with ⟨rfl, _⟩ | h'
        · exact ⟨Phase.issued, List.mem_of_getElem? hIdx⟩
        · exact ⟨ph, h'⟩
      · exact ⟨ph, by simp [he] at h; exact h⟩)
  | retire =>
    rename_i _ instr rest hHead
    exact specInv_of_same_history hInv rfl rfl (by
      intro e' i ph h; simp [funUpdate] at h
      by_cases he : e' = e
      · subst he; simp at h; exact ⟨ph, by rw [hHead]; exact List.Mem.tail _ h⟩
      · exact ⟨ph, by simp [he] at h; exact h⟩)
  | issue =>
    rename_i hStepE frame rest f instr hStack hStmt hInstr hDeps
    have hLoops : ∀ e', loopsOnStack { ss with
        pc := funUpdate ss.pc e { (ss.pc e) with instrIdx := (ss.pc e).instrIdx + 1 }
        inflight := funUpdate ss.inflight e (ss.inflight e ++ [(instr, Phase.issued)]) } e' = loopsOnStack ss e' := by
      intro e'; simp [loopsOnStack]; by_cases he : e' = e <;> simp [he]
    have hStk : ∀ e', (funUpdate ss.pc e { (ss.pc e) with instrIdx := (ss.pc e).instrIdx + 1 } e').stack = (ss.pc e').stack := by
      intro e'; by_cases he : e' = e <;> simp [funUpdate, he]
    exact { hInv with
      activeLoopPos := by intro e' lid hm; rw [hLoops] at hm; exact hInv.activeLoopPos e' lid hm
      ancestorsActive := by intro e' lid loop hm hEnc; rw [hLoops] at hm ⊢; exact hInv.ancestorsActive e' lid loop hm hEnc
      zeroBeforeEntry := by
        intro e' lid loop si j stmt hLoop hSi hJ hMem hLt
        rw [hLoops] at hLoop; rw [hStk] at hSi
        exact hInv.zeroBeforeEntry e' lid loop si j stmt hLoop hSi hJ hMem hLt
      zeroBeforeEntryTop := by
        intro e' lid si j stmt hSi hJ hMem hLt
        rw [hStk] at hSi; exact hInv.zeroBeforeEntryTop e' lid si j stmt hSi hJ hMem hLt
      wellFormedPC := by
        intro e'; by_cases he : e' = e
        · simp [he]; exact hStack ▸ hInv.wellFormedPC e
        · simp [he]; exact hInv.wellFormedPC e'
      inflightInBody := by
        intro e' i ph h; simp [funUpdate] at h
        by_cases he : e' = e
        · subst he; simp at h
          rcases h with hOld | ⟨rfl, _⟩
          · exact hInv.inflightInBody e' i ph hOld
          · -- newly issued: instr in block f on engine e', in frame.body, in spec.body
            -- instrInBody frame.body i → instrInBody spec.body i via SMP
            have hInBlock : instrInBody spec.engines [Stmt.block f] i = true := by
              simp [instrInBody, instrInBody]
              have hMemI := List.mem_of_getElem? hInstr
              -- findInBlock finds i on some engine since i ∈ f e' and e' ∈ spec.engines
              suffices h : (findInBlock spec.engines f i).isSome = true from h
              exact findInBlock_isSome hStepE hMemI
            have hInFrame := instrInBody_of_getElem_rest hStmt hInBlock
            have hSMP := hStack ▸ hInv.wellFormedPC e'
            exact smp_instrInBody_lift hSMP (List.Mem.head _) hInFrame
        · simp [he] at h; exact hInv.inflightInBody e' i ph h
      inflightEngineEq := by
        intro e' i ph h; simp [funUpdate] at h
        by_cases he : e' = e
        · subst he; simp at h
          rcases h with hOld | ⟨rfl, _⟩
          · exact hInv.inflightEngineEq e' i _ hOld
          · -- newly issued: instrEngine spec.body instr = some e
            have hMemI := List.mem_of_getElem? hInstr
            have hSMP' := hStack ▸ hInv.wellFormedPC e'
            have hUIFrame := smp_uniqueInstrIds hSMP' hUniqueInstr frame (List.Mem.head _)
            have hFIB := findInBlock_isSome hStepE hMemI
            have hIESingle : instrEngine spec.engines [Stmt.block f] i = some e' := by
              simp [instrEngine]
              cases hfb : findInBlock spec.engines f i with
              | none => simp [hfb] at hFIB
              | some eng =>
                simp
                -- eng = e' from findInBlock returns an engine containing i
                -- and single-engine property says i is only on one engine
                -- findInBlock returns eng containing i; single-engine says eng = e'
                exact findInBlock_eq_of_mem hStepE hMemI hfb (by
                  have : ∀ (body : List Stmt) (n : Nat),
                      UniqueInstrIds spec.engines body → body[n]? = some (Stmt.block f) →
                      ∀ instr' e1 e2, e1 ∈ spec.engines → e2 ∈ spec.engines →
                      instr' ∈ f e1 → instr' ∈ f e2 → e1 = e2 := by
                    intro body n hUI hIdx
                    induction body generalizing n with
                    | nil => simp at hIdx
                    | cons s rest ih =>
                      cases n with
                      | zero =>
                        simp at hIdx
                        cases s <;> simp at hIdx
                        obtain ⟨rfl⟩ := hIdx
                        cases hUI with
                        | block => assumption
                      | succ m =>
                        simp at hIdx
                        have hUIR : UniqueInstrIds spec.engines rest := by
                          cases hUI <;> assumption
                        exact ih m hUIR hIdx
                  exact this frame.body frame.stmtIdx hUIFrame hStmt)
            exact instrEngine_lift_smp hSMP' hUniqueInstr (List.Mem.head _)
              (instrEngine_of_getElem_rest hStmt hIESingle hUIFrame)
        · simp [he] at h; exact hInv.inflightEngineEq e' i ph h }
  | blockDone =>
    rename_i _ frame rest f hStack hStmt hDone
    exact specInv_advance_top spec e ss hUniq hInv frame rest hStack
  | loopSkip =>
    rename_i _ frame rest lid loopBody hStack hStmt hGuard
    exact specInv_advance_top spec e ss hUniq hInv frame rest hStack
  | condDone =>
    rename_i _ frame parent rest sid hStack hKind hEnd
    -- condDone pops a cond frame. loopsOnStack shrinks: sid is removed (like loopBack removes lid).
    have hLoopsSub : ∀ e' x, x ∈ loopsOnStack { ss with
        pc := funUpdate ss.pc e { stack := ⟨parent.body, parent.stmtIdx + 1, parent.kind⟩ :: rest, instrIdx := 0 } } e' →
        x ∈ loopsOnStack ss e' := by
      intro e' x hx; by_cases he : e' = e
      · subst he; simp [loopsOnStack, funUpdate, enclosing_change_stmtIdx] at hx ⊢; rw [hStack]
        simp [enclosingLoopsFromStack, hKind]
        right; exact hx
      · simp [loopsOnStack, funUpdate, he] at hx ⊢; exact hx
    have hStk : ∀ e', (funUpdate ss.pc e { stack := ⟨parent.body, parent.stmtIdx + 1, parent.kind⟩ :: rest, instrIdx := 0 } e').stack = (ss.pc e').stack ∨
        (e' = e ∧ (funUpdate ss.pc e { stack := ⟨parent.body, parent.stmtIdx + 1, parent.kind⟩ :: rest, instrIdx := 0 } e').stack = ⟨parent.body, parent.stmtIdx + 1, parent.kind⟩ :: rest) := by
      intro e'; by_cases he : e' = e <;> simp [funUpdate, he]
    exact { hInv with
      activeLoopPos := by
        intro e' lid hm; exact hInv.activeLoopPos e' lid (hLoopsSub e' lid hm)
      ancestorsActive := by
        intro e' lid_1 loop hm hEnc
        have hOld := hInv.ancestorsActive e' lid_1 loop (hLoopsSub e' lid_1 hm) hEnc
        by_cases he : e' = e
        · subst he; simp [loopsOnStack, funUpdate, enclosing_change_stmtIdx] at hm ⊢
          have hOldExp : loop = sid ∨ loop ∈ enclosingLoopsFromStack (parent :: rest) := by
            simp [loopsOnStack, hStack, enclosingLoopsFromStack, hKind] at hOld; exact hOld
          rcases hOldExp with hEq2 | hLoop
          · -- loop = sid (the cond being popped). Show contradiction.
            exfalso
            have hSMP_old := hStack ▸ hInv.wellFormedPC e'
            have hParentSMP : StackMatchesProgram spec.body (parent :: rest) := by
              cases hSMP_old with
              | cond _ _ _ _ _ _ _ _ _ _ hM => exact hM
              | _ => simp at *
            have hLid1InParent : lid_1 ∈ scopeIdsOf parent.body := by
              cases hSMP_old with
              | cond tb eb si' ii tid eid _ rest' taken hStmt' hM =>
                have hPfUniq := smp_uniqueScopeIds hM hUniq parent (List.Mem.head _)
                cases taken with
                | false =>
                  simp at hKind
                  have hEidSid : eid = sid := hKind
                  have hEidInParent : eid ∈ scopeIdsOf parent.body :=
                    mem_scopeIdsOf_of_getElem hStmt' (by simp [scopeIdsOf])
                  have hAgree := smp_scopeBodyOf_agree hM hUniq parent (List.Mem.head _) eid hEidInParent
                  have hSBOfParent := scopeBodyOf_of_getElem_condFalse hStmt' hPfUniq
                  have hSBOfSpec : scopeBodyOf spec.body loop = some eb := by
                    rw [hEq2, ← hEidSid]; exact hAgree.trans hSBOfParent
                  have hLid1InEb : lid_1 ∈ scopeIdsOf eb := by simp [hSBOfSpec] at hEnc; exact hEnc
                  exact mem_scopeIdsOf_of_getElem hStmt' (by
                    simp [scopeIdsOf, List.mem_append]; right; right; right; exact hLid1InEb)
                | true =>
                  simp at hKind
                  have hTidSid : tid = sid := hKind
                  have hTidInParent : tid ∈ scopeIdsOf parent.body :=
                    mem_scopeIdsOf_of_getElem hStmt' (by simp [scopeIdsOf])
                  have hAgree := smp_scopeBodyOf_agree hM hUniq parent (List.Mem.head _) tid hTidInParent
                  have hSBOfParent := scopeBodyOf_of_getElem_condTrue hStmt' hPfUniq
                  have hSBOfSpec : scopeBodyOf spec.body loop = some tb := by
                    rw [hEq2, ← hTidSid]; exact hAgree.trans hSBOfParent
                  have hLid1InTb : lid_1 ∈ scopeIdsOf tb := by simp [hSBOfSpec] at hEnc; exact hEnc
                  exact mem_scopeIdsOf_of_getElem hStmt' (by
                    simp [scopeIdsOf, List.mem_append]; right; right; left; exact hLid1InTb)
              | _ => simp at *
            exact enclosing_disjoint_top hParentSMP hUniq lid_1 hm hLid1InParent
          · exact hLoop
        · simp [loopsOnStack, funUpdate, he] at hm hOld ⊢; exact hOld
      zeroBeforeEntry := by
        intro e' lid' loop si j stmt hLoop hSi hJ hMem hLt
        -- Key fact: sid (the popped cond loop) can't appear in rest's stmtIdxInLoop
        have hSMP_e := hStack ▸ hInv.wellFormedPC e
        have hSidNone := stmtIdxInLoop_none_of_popped hSMP_e hUniq (Or.inl hKind)
        rcases hStk e' with h | ⟨he, h⟩
        · exact hInv.zeroBeforeEntry e' lid' loop si j stmt (hLoopsSub e' loop hLoop) (by rw [h] at hSi; exact hSi) hJ hMem hLt
        · subst he; rw [h] at hSi
          -- New stack is ⟨parent.body, parent.stmtIdx + 1, parent.kind⟩ :: rest.
          -- stmtIdxInLoop on new stack. Need to relate to old stack = frame :: parent :: rest.
          -- First handle: loop = sid (the popped cond). This is impossible on the new stack
          -- because sid can't appear in stmtIdxInLoop (parent :: rest).
          by_cases hss : sid = loop
          · -- loop = sid: stmtIdxInLoop on new stack finds sid in parent or rest.
            -- But stmtIdxInLoop_none_of_popped says stmtIdxInLoop (parent :: rest) sid = none.
            -- The new stack has parent with stmtIdx+1, which doesn't change the if-branch.
            subst hss
            -- hSi says stmtIdxInLoop on new stack (with parent.stmtIdx + 1) gives some si for loop = sid.
            -- stmtIdxInLoop_none_of_popped gives stmtIdxInLoop (parent :: rest) sid = none.
            -- These are almost the same except stmtIdx is +1 in the new stack.
            -- But stmtIdxInLoop only looks at frame.kind, not stmtIdx for the if-branch.
            -- So stmtIdxInLoop ⟨parent.body, parent.stmtIdx+1, parent.kind⟩ :: rest = stmtIdxInLoop (parent :: rest) (same kind).
            -- Wait, stmtIdxInLoop checks f.kind and returns f.stmtIdx. The kind is the same, only stmtIdx differs.
            -- If parent.kind matches loop, it returns parent.stmtIdx (not parent.stmtIdx+1 for old, or +1 for new).
            -- Actually: stmtIdxInLoop returns f.stmtIdx of the matching frame. So on the new stack with
            -- parent.stmtIdx+1, if parent.kind matches, it returns parent.stmtIdx+1, not parent.stmtIdx.
            -- But stmtIdxInLoop_none_of_popped says the old stack (parent :: rest) has none for sid.
            -- This means parent.kind doesn't match sid AND rest doesn't have sid.
            -- On the new stack, parent.kind is still the same, so it still doesn't match. And rest is unchanged. So it's still none.
            exfalso
            have : stmtIdxInLoop (⟨parent.body, parent.stmtIdx + 1, parent.kind⟩ :: rest) sid = none := by
              simp [stmtIdxInLoop]; cases hpk : parent.kind <;> simp [hpk, stmtIdxInLoop] at hSidNone ⊢
              · exact hSidNone
              all_goals split at hSidNone <;> simp_all
            simp [this] at hSi
          · -- loop ≠ sid: on old stack, frame.kind = .cond sid, so if sid = loop is false.
            -- stmtIdxInLoop passes through the .cond sid frame.
            match hpk : parent.kind with
            | .top => simp [stmtIdxInLoop, hpk] at hSi
                      exact hInv.zeroBeforeEntry e' lid' loop si j stmt (hLoopsSub e' loop hLoop) (by rw [hStack]; simp [stmtIdxInLoop, hKind, hss, hpk]; exact hSi) hJ hMem hLt
            | .cond sid' | .loop sid' =>
              simp [stmtIdxInLoop, hpk] at hSi
              by_cases hps : sid' = loop
              · subst hps; simp at hSi; subst hSi
                exact hInv.zeroBeforeEntry e' lid' sid' parent.stmtIdx j stmt (hLoopsSub e' sid' hLoop)
                  (by rw [hStack]; simp [stmtIdxInLoop, hKind, hss, hpk]) hJ hMem (by omega)
              · simp [hps] at hSi
                exact hInv.zeroBeforeEntry e' lid' loop si j stmt (hLoopsSub e' loop hLoop)
                  (by rw [hStack]; simp [stmtIdxInLoop, hKind, hss, hpk, hps]; exact hSi) hJ hMem hLt
      zeroBeforeEntryTop := by
        intro e' lid si j stmt hSi hJ hMem hLt
        rcases hStk e' with h | ⟨he, h⟩
        · rw [h] at hSi; exact hInv.zeroBeforeEntryTop e' lid si j stmt hSi hJ hMem hLt
        · subst he; rw [h] at hSi
          match hpk : parent.kind with
          | .top => simp [stmtIdxAtTop, hpk] at hSi; subst hSi
                    exact hInv.zeroBeforeEntryTop e' lid parent.stmtIdx j stmt (by rw [hStack]; simp [stmtIdxAtTop, hKind, hpk]) hJ hMem (by omega)
          | .loop _ | .cond _ =>
            simp [stmtIdxAtTop, hpk] at hSi
            exact hInv.zeroBeforeEntryTop e' lid si j stmt (by rw [hStack]; simp [stmtIdxAtTop, hKind, hpk]; exact hSi) hJ hMem hLt
      wellFormedPC := by
        intro e'; by_cases he : e' = e
        · subst he; simp [funUpdate]
          have hSMP := hStack ▸ hInv.wellFormedPC e'
          cases hSMP with
          | cond _ _ _ _ _ _ _ _ _ _ hMatch =>
            exact smp_change_top_stmtIdx hMatch (parent.stmtIdx + 1) 0
          | loop lb si ii lid' pf rest' hStmt' hMatch => simp at *
        · simp [funUpdate, he]; exact hInv.wellFormedPC e' }
  | loopBack =>
    rename_i _ frame parent rest lid hStack hKind hEnd
    have hLoopsSub : ∀ e' x, x ∈ loopsOnStack { ss with
        pc := funUpdate ss.pc e { stack := parent :: rest, instrIdx := 0 } } e' →
        x ∈ loopsOnStack ss e' := by
      intro e' x hx; by_cases he : e' = e
      · subst he; simp [loopsOnStack, funUpdate] at hx ⊢; rw [hStack]
        simp [enclosingLoopsFromStack, hKind]
        right; exact hx
      · simp [loopsOnStack, funUpdate, he] at hx ⊢; exact hx
    have hStk : ∀ e', (funUpdate ss.pc e { stack := parent :: rest, instrIdx := 0 } e').stack = (ss.pc e').stack ∨
        (e' = e ∧ (funUpdate ss.pc e { stack := parent :: rest, instrIdx := 0 } e').stack = parent :: rest) := by
      intro e'; by_cases he : e' = e <;> simp [funUpdate, he]
    exact { hInv with
      activeLoopPos := by
        intro e' lid' hm; exact hInv.activeLoopPos e' lid' (hLoopsSub e' lid' hm)
      ancestorsActive := by
        intro e' lid_1 loop hm hEnc
        have hOld := hInv.ancestorsActive e' lid_1 loop (hLoopsSub e' lid_1 hm) hEnc
        by_cases he : e' = e
        · subst he; simp [loopsOnStack, funUpdate] at hm ⊢
          have hOldExp : loop = lid ∨ loop ∈ enclosingLoopsFromStack (parent :: rest) := by
            simp [loopsOnStack, hStack, enclosingLoopsFromStack, hKind] at hOld; exact hOld
          rcases hOldExp with hEq2 | hLoop
          · -- loop = lid (the loop being popped). Show contradiction.
            exfalso
            have hSMP_old := hStack ▸ hInv.wellFormedPC e'
            have hParentSMP : StackMatchesProgram spec.body (parent :: rest) := by
              cases hSMP_old with | loop _ _ _ _ _ _ _ hM => exact hM | _ => simp at *
            -- lid_1 ∈ scopeBodyOf spec.body loop. loop = lid is a loop in parent.body.
            -- lid_1 is inside lid's body, hence in parent.body.
            have hLid1InParent : lid_1 ∈ scopeIdsOf parent.body := by
              -- From SMP, parent.body[parent.stmtIdx] = Stmt.loop lid lb, and frame.body = lb
              -- scopeBodyOf spec.body loop = some lb (via SMP agree)
              -- So lid_1 ∈ scopeIdsOf lb ⊆ scopeIdsOf [Stmt.loop lid lb] ⊆ scopeIdsOf parent.body
              have hSBOf : ∃ lb, scopeBodyOf spec.body loop = some lb ∧ lid_1 ∈ scopeIdsOf lb := by
                cases hSMP_old with
                | loop lb si' ii lid' _ rest' hStmt' hM =>
                  have hLidEq : lid' = lid := by simpa using hKind
                  have hLidIn : lid' ∈ scopeIdsOf parent.body :=
                    mem_scopeIdsOf_of_getElem hStmt' (by simp [scopeIdsOf])
                  have hAg := smp_scopeBodyOf_agree hM hUniq parent (List.Mem.head _) lid' hLidIn
                  have hLocal := scopeBodyOf_of_getElem hStmt' (smp_uniqueScopeIds hM hUniq parent (List.Mem.head _))
                  have hSpec : scopeBodyOf spec.body lid' = some lb := hAg.trans hLocal
                  rw [hLidEq, ← hEq2] at hSpec
                  have hLid1InLb : lid_1 ∈ scopeIdsOf lb := by simp [hSpec] at hEnc; exact hEnc
                  exact ⟨lb, hSpec, hLid1InLb⟩
                | _ => simp at *
              obtain ⟨lb, hSBOfSpec, hLid1InLb⟩ := hSBOf
              -- loop ∈ scopeIdsOf parent.body because loop = lid is a loop header in parent.body
              have hLoopInParent : loop ∈ scopeIdsOf parent.body := by
                rw [hEq2]
                have hSMP2 := hStack ▸ hInv.wellFormedPC e'
                cases hSMP2 with
                | loop _ _ _ lid2 _ _ hStmt2 _ =>
                  have hLeq : lid2 = lid := by simpa using hKind
                  subst hLeq
                  exact mem_scopeIdsOf_of_getElem hStmt2 (by simp [scopeIdsOf])
                | _ => simp at *
              -- scopeBodyOf parent.body loop = some lb (via smp_scopeBodyOf_agree)
              have hAgree := smp_scopeBodyOf_agree hParentSMP hUniq parent (List.Mem.head _) loop hLoopInParent
              have hSBOfParent : scopeBodyOf parent.body loop = some lb := by
                rwa [← hAgree]
              exact scopeBodyOf_subset hSBOfParent lid_1 hLid1InLb
            exact enclosing_disjoint_top hParentSMP hUniq lid_1 hm hLid1InParent
          · exact hLoop
        · simp [loopsOnStack, funUpdate, he] at hOld ⊢; exact hOld
      zeroBeforeEntry := by
        intro e' lid' loop si j stmt hLoop hSi hJ hMem hLt
        rcases hStk e' with h | ⟨he, h⟩
        · exact hInv.zeroBeforeEntry e' lid' loop si j stmt (hLoopsSub e' loop hLoop) (by rw [h] at hSi; exact hSi) hJ hMem hLt
        · subst he; rw [h] at hSi
          by_cases hls : lid = loop
          · subst hls
            have hSMP_old := hStack ▸ hInv.wellFormedPC e'
            have : lid ∈ scopeIdsOf parent.body ∧ StackMatchesProgram spec.body (parent :: rest) := by
              cases hSMP_old with
              | loop lb _ _ lid' _ _ hS hM =>
                have : lid' = lid := by cases hKind; rfl
                subst this
                exact ⟨mem_scopeIdsOf_of_getElem hS (by simp [scopeIdsOf]), hM⟩
              | _ => simp at *
            exfalso; exact enclosing_disjoint_top this.2 hUniq lid (stmtIdxInLoop_mem_enclosing hSi) this.1
          · exact hInv.zeroBeforeEntry e' lid' loop si j stmt (hLoopsSub e' loop hLoop) (by rw [hStack]; simp [stmtIdxInLoop, hKind, hls]; exact hSi) hJ hMem hLt
      zeroBeforeEntryTop := by
        intro e' lid' si j stmt hSi hJ hMem hLt
        rcases hStk e' with h | ⟨he, h⟩
        · rw [h] at hSi; exact hInv.zeroBeforeEntryTop e' lid' si j stmt hSi hJ hMem hLt
        · subst he; rw [h] at hSi
          exact hInv.zeroBeforeEntryTop e' lid' si j stmt (by rw [hStack]; simp [stmtIdxAtTop, hKind]; exact hSi) hJ hMem hLt
      wellFormedPC := by
        intro e'; by_cases he : e' = e
        · subst he; simp [funUpdate]
          have hSMP := hStack ▸ hInv.wellFormedPC e'
          cases hSMP with
          | loop lb si ii lid' pf rest' hStmt' hMatch => exact hMatch
          | cond _ _ _ _ _ _ _ _ _ _ _ => simp at *
        · simp [funUpdate, he]; exact hInv.wellFormedPC e' }
  | loopEnter =>
    rename_i _ frame rest lid loopBody hStack hStmt hGuard
    have hSMP := hStack ▸ hInv.wellFormedPC e
    have hFUniq := smp_uniqueScopeIds hSMP hUniq frame (List.Mem.head _)
    have hLidInBody : lid ∈ scopeIdsOf frame.body :=
      mem_scopeIdsOf_of_getElem hStmt (by simp [scopeIdsOf])
    exact specInv_loopEntry spec e ss hUniq hInv frame rest lid loopBody (.loop lid)
      hStack hLidInBody
      (lid_not_on_stack_at_entry hStack hStmt (hInv.wellFormedPC e) hUniq)
      (by rw [smp_scopeBodyOf_agree hSMP hUniq frame (List.Mem.head _) lid hLidInBody]
          exact scopeBodyOf_of_getElem hStmt hFUniq)
      (lid_not_in_own_body hStmt hFUniq)
      (fun olid hEnc hNe =>
        smp_ancestor_on_stack hSMP hUniq rfl hLidInBody hStmt hEnc hNe)
      ⟨Stmt.loop lid loopBody, hStmt, by simp [scopeIdsOf]⟩
      (by simp [FrameKind.loopId?])
      (StackMatchesProgram.loop loopBody 0 0 lid frame rest hStmt hSMP)
  | condTrue =>
    rename_i _ frame rest thenId elseId thenBody elseBody hStack hStmt hGuard
    have hSMP := hStack ▸ hInv.wellFormedPC e
    have hFUniq := smp_uniqueScopeIds hSMP hUniq frame (List.Mem.head _)
    have hThenIdInBody : thenId ∈ scopeIdsOf frame.body :=
      mem_scopeIdsOf_of_getElem hStmt (by simp [scopeIdsOf])
    exact specInv_loopEntry spec e ss hUniq hInv frame rest thenId thenBody (.cond thenId)
      hStack hThenIdInBody
      (sid_not_on_stack_at_entry hStack hThenIdInBody (hInv.wellFormedPC e) hUniq)
      (by rw [smp_scopeBodyOf_agree hSMP hUniq frame (List.Mem.head _) thenId hThenIdInBody]
          exact scopeBodyOf_of_getElem_condTrue hStmt hFUniq)
      (thenId_not_in_then_body hStmt hFUniq)
      (fun olid hEnc hNe => by
        -- Inline ancestor proof for condTrue
        have hOlidNotIn : olid ∉ scopeIdsOf frame.body := by
          intro hOlIn
          have hAgree := smp_scopeBodyOf_agree hSMP hUniq frame (List.Mem.head _) olid hOlIn
          cases hOB : scopeBodyOf spec.body olid with
          | none => exact absurd hEnc (by simp [hOB, scopeIdsOf])
          | some ob =>
            have hOBf : scopeBodyOf frame.body olid = some ob := by rwa [hAgree] at hOB
            have hLidOb : thenId ∈ scopeIdsOf ob := by simp [hOB] at hEnc; exact hEnc
            have hNotSelf := scopeBodyOf_not_self_mem hFUniq (scopeBodyOf_of_getElem_condTrue hStmt hFUniq)
            have hTnEb := thenId_not_in_else_body hStmt hFUniq
            exact scopeBodyOf_at_same_stmt hFUniq hOBf hLidOb hStmt
              (by simp [scopeIdsOf]) (by
                simp [scopeIdsOf]; refine ⟨hNe, fun h => ?_, fun h => ?_, fun h => ?_⟩
                · subst h
                  have hEBOf := scopeBodyOf_of_getElem_condFalse hStmt hFUniq
                  rw [hEBOf] at hOBf; cases hOBf
                  exact hTnEb hLidOb
                · have hDesc := scopeBodyOf_descend_condTrue hStmt h hFUniq
                  have hOBtb : scopeBodyOf thenBody olid = some ob := by rw [hDesc] at hOBf; exact hOBf
                  exact hNotSelf (scopeBodyOf_subset hOBtb thenId hLidOb)
                · have hDesc := scopeBodyOf_descend_condFalse hStmt h hFUniq
                  have hOBeb : scopeBodyOf elseBody olid = some ob := by rw [hDesc] at hOBf; exact hOBf
                  exact hTnEb (scopeBodyOf_subset hOBeb thenId hLidOb))
        exact smp_not_in_frame_enclosing hSMP hUniq rfl hThenIdInBody hEnc hOlidNotIn)
      ⟨Stmt.cond thenId elseId thenBody elseBody, hStmt, by simp [scopeIdsOf]⟩
      (by simp [FrameKind.loopId?])
      (StackMatchesProgram.cond thenBody elseBody 0 0 thenId elseId frame rest true hStmt hSMP)
  | condFalse =>
    rename_i _ frame rest thenId elseId thenBody elseBody hStack hStmt hGuard
    have hSMP := hStack ▸ hInv.wellFormedPC e
    have hFUniq := smp_uniqueScopeIds hSMP hUniq frame (List.Mem.head _)
    have hElseIdInBody : elseId ∈ scopeIdsOf frame.body :=
      mem_scopeIdsOf_of_getElem hStmt (by simp [scopeIdsOf])
    exact specInv_loopEntry spec e ss hUniq hInv frame rest elseId elseBody (.cond elseId)
      hStack hElseIdInBody
      (elseId_not_on_stack_at_entry hStack hStmt (hInv.wellFormedPC e) hUniq)
      (by rw [smp_scopeBodyOf_agree hSMP hUniq frame (List.Mem.head _) elseId hElseIdInBody]
          exact scopeBodyOf_of_getElem_condFalse hStmt hFUniq)
      (elseId_not_in_else_body hStmt hFUniq)
      (fun olid hEnc hNe =>
        smp_ancestor_on_stack_condFalse hSMP hUniq rfl hElseIdInBody hStmt hEnc hNe)
      ⟨Stmt.cond thenId elseId thenBody elseBody, hStmt, by simp [scopeIdsOf]⟩
      (by simp [FrameKind.loopId?])
      (StackMatchesProgram.cond thenBody elseBody 0 0 thenId elseId frame rest false hStmt hSMP)

theorem specInv_star (spec : Program) (ss ss' : SpecState)
    (hUniq : UniqueScopeIds spec.body)
    (hUniqueInstr : UniqueInstrIds spec.engines spec.body)
    (hInv : SpecInv spec ss)
    (hStar : SpecStar spec ss ss') : SpecInv spec ss' := by
  induction hStar with
  | refl => exact hInv
  | step hS _ ih => obtain ⟨e, hS⟩ := hS; exact ih (specInv_step spec e _ _ hUniq hInv hS hUniqueInstr)

/-! ### SMP lifting for scopeParent.go -/

/-- Lift a scopeParent.go result from a frame's body to the full program body via SMP. -/
theorem smp_lift_scopeParent_go {progBody : List Stmt}
    : ∀ {stack : List Frame},
    StackMatchesProgram progBody stack →
    UniqueScopeIds progBody →
    ∀ {target result : ScopeId},
    ∀ sf rest, stack = sf :: rest →
    scopeParent.go sf.body target (sf.kind.loopId?) = some result →
    target ∈ scopeIdsOf sf.body →
    scopeParent.go progBody target none = some result
  | _, .base si ii, _, _, _, sf, rest, hStack, hGo, _ => by
    obtain ⟨rfl, rfl⟩ := List.cons.inj hStack; simp [FrameKind.loopId?] at hGo; exact hGo
  | _, .loop lb si ii lid pf rest' hPStmt hMatch, hUniq, _, _, sf, rest, hStack, hGo, hMem => by
    obtain ⟨rfl, rfl⟩ := List.cons.inj hStack
    have hPfUniq := smp_uniqueScopeIds hMatch hUniq pf (List.Mem.head _)
    exact smp_lift_scopeParent_go hMatch hUniq pf rest' rfl
      (scopeParent_go_lift_loop hPStmt hPfUniq hGo hMem)
      (mem_scopeIdsOf_of_getElem hPStmt (by simp [scopeIdsOf]; right; exact hMem))
  | _, .cond tb eb si ii tid eid pf rest' taken hPStmt hMatch, hUniq, _, _, sf, rest, hStack, hGo, hMem => by
    obtain ⟨rfl, rfl⟩ := List.cons.inj hStack
    have hPfUniq := smp_uniqueScopeIds hMatch hUniq pf (List.Mem.head _)
    cases taken with
    | true =>
      simp at hGo hMem
      exact smp_lift_scopeParent_go hMatch hUniq pf rest' rfl
        (scopeParent_go_lift_cond_then hPStmt hPfUniq hGo hMem)
        (mem_scopeIdsOf_of_getElem hPStmt (by simp [scopeIdsOf]; right; right; left; exact hMem))
    | false =>
      simp at hGo hMem
      exact smp_lift_scopeParent_go hMatch hUniq pf rest' rfl
        (scopeParent_go_lift_cond_else hPStmt hPfUniq hGo hMem)
        (mem_scopeIdsOf_of_getElem hPStmt (by simp [scopeIdsOf]; right; right; right; assumption))
