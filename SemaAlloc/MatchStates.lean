import SemaAlloc.Spec
import SemaAlloc.PerInstrAlloc
import SemaAlloc.Allocatable
import Aesop

def frameKindCorr : FrameKind → ImplFrameKind → Prop
  | .top, .top => True
  | .loop lid₁, .loop lid₂ => lid₁ = lid₂
  | .cond sid₁, .cond sid₂ => sid₁ = sid₂
  | _, _ => False

def atRegOp (imf : ImplFrame) : Prop :=
  match imf.kind with
  | .loop _ => imf.stmtIdx = 0
  | .cond _ => imf.stmtIdx = 0
  | _ => False

structure FrameCorr (ab : AllocBase spec impl) (sf : Frame) (imf : ImplFrame) : Prop where
  kindCorr : frameKindCorr sf.kind imf.kind
  bodyCorr : ∃ implBody, BodyMatch ab.monotoneReg ab.tripReg sf.body implBody ∧
    match imf.kind with
    | .loop lid => imf.body = [ImplStmt.regOp (scopeEntryOps ab.monotoneReg ab.tripReg sf.body · lid)] ++ implBody
    | .cond sid => imf.body = [ImplStmt.regOp (scopeEntryOps ab.monotoneReg ab.tripReg sf.body · sid)] ++ implBody
    | _ => imf.body = implBody
  idxCorr :
    (atRegOp imf → sf.stmtIdx = 0 ∧ imf.stmtIdx = 0) ∧
    (¬ atRegOp imf →
      match imf.kind with
      | .loop _ => sf.stmtIdx + 1 = imf.stmtIdx
      | .cond _ => sf.stmtIdx + 1 = imf.stmtIdx
      | _ => sf.stmtIdx = imf.stmtIdx)

inductive StackCorr (ab : AllocBase spec impl) :
    List Frame → List ImplFrame → Prop where
  | nil : StackCorr ab [] []
  | cons (sf : Frame) (imf : ImplFrame)
      (srest : List Frame) (imrest : List ImplFrame)
      (hFrame : FrameCorr ab sf imf)
      (hRest : StackCorr ab srest imrest)
      (hCovSpec : ∀ sf' srest', srest = sf' :: srest' → sf'.stmtIdx < sf'.body.length)
      (hCovImpl : ∀ imf' imrest', imrest = imf' :: imrest' → imf'.stmtIdx < imf'.body.length)
      (hNoRegOp : ∀ imf' imrest', imrest = imf' :: imrest' → ¬ atRegOp imf')
      : StackCorr ab (sf :: srest) (imf :: imrest)

structure PCCorr (ab : AllocBase spec impl) (spc : PC) (ipc : ImplPC) : Prop where
  stackCorr : StackCorr ab spc.stack ipc.stack
  instrEq : spc.instrIdx = ipc.instrIdx

theorem stackCorr_cons_inv {ab : AllocBase spec impl}
    {sstack : List Frame} {imf : ImplFrame} {imrest : List ImplFrame}
    (hSC : StackCorr ab sstack (imf :: imrest))
    : ∃ sf srest, sstack = sf :: srest ∧ FrameCorr ab sf imf ∧ StackCorr ab srest imrest ∧
        (∀ sf' srest', srest = sf' :: srest' → sf'.stmtIdx < sf'.body.length) ∧
        (∀ imf' imrest', imrest = imf' :: imrest' → imf'.stmtIdx < imf'.body.length) ∧
        (∀ imf' imrest', imrest = imf' :: imrest' → ¬ atRegOp imf') := by
  cases hSC with
  | cons sf _ srest _ hFrame hRest hCS hCI hNR => exact ⟨sf, srest, rfl, hFrame, hRest, hCS, hCI, hNR⟩

theorem stackCorr_spec_cons_inv {ab : AllocBase spec impl}
    {sf : Frame} {srest : List Frame} {implStack : List ImplFrame}
    (hSC : StackCorr ab (sf :: srest) implStack)
    : ∃ imf imrest, implStack = imf :: imrest ∧ FrameCorr ab sf imf ∧
        StackCorr ab srest imrest ∧
        (∀ sf' srest', srest = sf' :: srest' → sf'.stmtIdx < sf'.body.length) ∧
        (∀ imf' imrest', imrest = imf' :: imrest' → imf'.stmtIdx < imf'.body.length) ∧
        (∀ imf' imrest', imrest = imf' :: imrest' → ¬ atRegOp imf') := by
  cases hSC with
  | cons _ imf _ imrest hF hR hCS hCI hNR => exact ⟨imf, imrest, rfl, hF, hR, hCS, hCI, hNR⟩

theorem pcCorr_stack_cons {ab : AllocBase spec impl}
    {spc : PC} {ipc : ImplPC} {imf : ImplFrame} {imrest : List ImplFrame}
    (hPC : PCCorr ab spc ipc) (hStack : ipc.stack = imf :: imrest)
    : ∃ sf srest, spc.stack = sf :: srest ∧ FrameCorr ab sf imf ∧ StackCorr ab srest imrest ∧
        (∀ sf' srest', srest = sf' :: srest' → sf'.stmtIdx < sf'.body.length) ∧
        (∀ imf' imrest', imrest = imf' :: imrest' → imf'.stmtIdx < imf'.body.length) ∧
        (∀ imf' imrest', imrest = imf' :: imrest' → ¬ atRegOp imf') := by
  obtain ⟨hSC, _⟩ := hPC; rw [hStack] at hSC; exact stackCorr_cons_inv hSC

theorem bodyMatch_length {monotoneReg tripReg specBody implBody}
    (hBM : BodyMatch monotoneReg tripReg specBody implBody)
    : specBody.length = implBody.length := by
  induction hBM with
  | nil => rfl | block _ _ _ _ ih => simp [ih]
  | loop _ _ _ _ _ _ _ ih_body ih_rest => simp only [List.length_cons]; omega
  | cond _ _ _ _ _ _ _ _ _ _ ih_rest ih => simp; assumption

theorem bodyMatch_block_at {monotoneReg tripReg specBody implBody}
    (hBM : BodyMatch monotoneReg tripReg specBody implBody)
    {i : Nat} {f : EngineId → List DataPathInstrId} (hIdx : implBody[i]? = some (ImplStmt.block f))
    : specBody[i]? = some (Stmt.block f) := by
  induction hBM generalizing i with
  | nil => simp at hIdx
  | block _ _ _ _ ih => cases i with | zero => simp_all | succ n => simp at hIdx ⊢; exact ih hIdx
  | loop _ _ _ _ _ _ _ _ ih
  | cond _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    cases i with | zero => simp at hIdx | succ n => simp at hIdx ⊢; exact ih hIdx

theorem bodyMatch_loop_at {monotoneReg tripReg specBody implBody}
    (hBM : BodyMatch monotoneReg tripReg specBody implBody)
    {i : Nat} {lid : ScopeId} {implLoopBody : List ImplStmt}
    (hIdx : implBody[i]? = some (ImplStmt.loop lid implLoopBody))
    : ∃ specLoopBody implInner,
        specBody[i]? = some (Stmt.loop lid specLoopBody) ∧
        BodyMatch monotoneReg tripReg specLoopBody implInner ∧
        implLoopBody = [ImplStmt.regOp (scopeEntryOps monotoneReg tripReg specLoopBody · lid)] ++ implInner := by
  induction hBM generalizing i with
  | nil => simp at hIdx
  | block _ _ _ _ ih
  | cond _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    cases i with | zero => simp at hIdx | succ n => simp at hIdx ⊢; obtain ⟨a, b, c, d, e⟩ := ih hIdx; exact ⟨a, c, b, d, e⟩
  | loop lid' specBody' implBody' specRest implRest hBody hRest ih_body ih_rest =>
    cases i with
    | zero => simp at hIdx; obtain ⟨rfl, rfl⟩ := hIdx; exact ⟨specBody', implBody', by simp, hBody, rfl⟩
    | succ n => simp at hIdx ⊢; obtain ⟨a, b, c, d, e⟩ := ih_rest hIdx; exact ⟨a, c, b, d, e⟩

theorem bodyMatch_no_regOp {monotoneReg tripReg specBody implBody}
    (hBM : BodyMatch monotoneReg tripReg specBody implBody)
    {i : Nat} {ops} (hIdx : implBody[i]? = some (ImplStmt.regOp ops)) : False := by
  induction hBM generalizing i with
  | nil => simp at hIdx
  | block _ _ _ _ ih
  | loop _ _ _ _ _ _ _ _ ih
  | cond _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    cases i with | zero => simp at hIdx | succ n => simp at hIdx; exact ih hIdx

theorem bodyMatch_cond_at {monotoneReg tripReg specBody implBody}
    (hBM : BodyMatch monotoneReg tripReg specBody implBody)
    {i : Nat} {thenId elseId : ScopeId} {implThen implElse : List ImplStmt}
    (hIdx : implBody[i]? = some (ImplStmt.cond thenId elseId implThen implElse))
    : ∃ specThen specElse implThenInner implElseInner,
        specBody[i]? = some (Stmt.cond thenId elseId specThen specElse) ∧
        BodyMatch monotoneReg tripReg specThen implThenInner ∧
        BodyMatch monotoneReg tripReg specElse implElseInner ∧
        implThen = [ImplStmt.regOp (scopeEntryOps monotoneReg tripReg specThen · thenId)] ++ implThenInner ∧
        implElse = [ImplStmt.regOp (scopeEntryOps monotoneReg tripReg specElse · elseId)] ++ implElseInner := by
  induction hBM generalizing i with
  | nil => simp at hIdx
  | block _ _ _ _ ih
  | loop _ _ _ _ _ _ _ _ ih =>
    cases i with | zero => simp at hIdx | succ n => simp at hIdx ⊢; obtain ⟨a, b, c, d, e1, e2, e3, e4, e5⟩ := ih hIdx; exact ⟨a, b, e1, c, e2, d, e3, e4, e5⟩
  | cond thenId' elseId' specThen' specElse' implThen' implElse' specRest implRest hThen hElse hRest _ _ ih_rest =>
    cases i with
    | zero => simp at hIdx; obtain ⟨rfl, rfl, hThenEq, hElseEq⟩ := hIdx; exact ⟨specThen', specElse', implThen', implElse', by simp, hThen, hElse, hThenEq.symm, hElseEq.symm⟩
    | succ n => simp at hIdx ⊢; obtain ⟨a, b, c, d, e1, e2, e3, e4, e5⟩ := ih_rest hIdx; exact ⟨a, b, e1, c, e2, d, e3, e4, e5⟩

theorem list_prepend_getElem_regOp_zero {xs : List ImplStmt} {regOps}
    {ops : EngineId → List RegOp}
    (h : ([ImplStmt.regOp regOps] ++ xs)[0]? = some (ImplStmt.regOp ops))
    : ops = regOps := by simp at h; exact h.symm

def expectedWaitVal (spec : Program) (ss : SpecState) (e : EngineId) (instr : DataPathInstrId) : Nat :=
  match spec.depGraph instr with
  | .none => 0
  | .dep producer offset =>
    let parentLoop := innermostParentScope spec.engines spec.body producer
    let sharedLoop := innermostSharedScope spec.engines spec.body producer instr
    match parentLoop with
    | some plid =>
      if sharedLoop = parentLoop then
        totalEntries ss e plid - offset
      else
        totalEntries ss e plid
    | none => 1 - offset

def foldRegOps (ops : List RegOp) (regs : RegId → Nat) : RegId → Nat :=
  match ops with
  | [] => regs
  | (dst, src, t) :: rest => foldRegOps rest (funUpdate regs dst (applyRegOpKind t (regs src) (regs dst)))

theorem foldRegOps_congr {ops : List RegOp} {regs₁ regs₂ : RegId → Nat}
    (h : ∀ r, regs₁ r = regs₂ r) : ∀ r, foldRegOps ops regs₁ r = foldRegOps ops regs₂ r := by
  induction ops generalizing regs₁ regs₂ with
  | nil => exact h
  | cons op rest ih =>
    obtain ⟨dst, src, t⟩ := op; simp only [foldRegOps]
    apply ih; intro r; simp [funUpdate]
    split
    · rw [h src, h dst]
    · exact h r

theorem foldRegOps_dst_init_irrelevant
    {ops : List RegOp} {f₁ f₂ : RegId → Nat} {w : RegId}
    (hAgree : ∀ r, r ≠ w → f₁ r = f₂ r)
    (hAllDst : ∀ op ∈ ops, op.1 = w)
    (hFirstSafe : ∀ src t, ops[0]? = some (w, src, t) →
      t.usesDst = false ∧ (src = w → ∃ n, t = .const n))
    (hNonEmpty : ops.length > 0)
    : foldRegOps ops f₁ w = foldRegOps ops f₂ w := by
  cases ops with
  | nil => simp at hNonEmpty
  | cons op rest =>
    obtain ⟨dst, src, t⟩ := op
    have hDst : dst = w := hAllDst _ (List.mem_cons_self ..)
    have ⟨hDoesNotUseDst, hSrcW⟩ := hFirstSafe src t (by simp [hDst])
    simp only [foldRegOps]
    apply foldRegOps_congr
    intro r; simp [funUpdate]
    split
    · by_cases hSrc : src = w
      · obtain ⟨n, hn⟩ := hSrcW hSrc
        simp [hn, applyRegOpKind]
      · cases t <;> simp_all [RegOpKind.usesDst, applyRegOpKind]
    · next h => exact hAgree r (by rw [hDst] at h; exact h)

theorem foldRegOps_drop_step {ops : List RegOp} {regs : RegId → Nat}
    {n : Nat} {dst src : RegId} {t : RegOpKind}
    (hLt : n < ops.length) (hGet : ops[n]? = some (dst, src, t))
    : foldRegOps (ops.drop n) regs = foldRegOps (ops.drop (n + 1)) (funUpdate regs dst (applyRegOpKind t (regs src) (regs dst))) := by
  induction n generalizing ops regs with
  | zero => cases ops with | nil => simp at hLt | cons h rest => simp [List.drop] at hGet ⊢; obtain ⟨rfl, rfl, rfl⟩ := hGet; rfl
  | succ k ih => cases ops with | nil => simp at hLt | cons h rest => simp only [List.drop_succ_cons]; exact ih (by simp at hLt; omega) (by simp [List.getElem?_cons_succ] at hGet; exact hGet)

theorem foldRegOps_other {ops : List RegOp} {regs : RegId → Nat}
    {r : RegId} (h : ∀ op ∈ ops, op.1 ≠ r) : foldRegOps ops regs r = regs r := by
  induction ops generalizing regs with
  | nil => rfl
  | cons op rest ih => obtain ⟨dst, src, t⟩ := op; simp only [foldRegOps]; rw [ih (fun op hm => h op (List.mem_cons_of_mem _ hm))]; simp [funUpdate, Ne.symm (h (dst, src, t) (by simp))]

theorem perInstrExpectedRegOps_dst_eq_waitReg (spec : Program) (waitReg : RegId) (monotoneReg : EngineId → ScopeId → RegId)
    (e : EngineId) (consumer : DataPathInstrId)
    : ∀ op ∈ perInstrExpectedRegOps spec waitReg monotoneReg e consumer, op.1 = waitReg := by
  intro op hMem; simp only [perInstrExpectedRegOps] at hMem
  split at hMem
  · simp_all
  · split at hMem
    · split at hMem
      · simp [List.mem_cons] at hMem; rcases hMem with ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ <;> rfl
      · simp_all
    · simp_all

structure ImplInv (impl : ImplProgram) (is : ImplState) : Prop where
  regOpBound : ∀ e frame rest f instr,
    (is.pc e).stack = frame :: rest → frame.body[frame.stmtIdx]? = some (ImplStmt.block f) →
    (f e)[(is.pc e).instrIdx]? = some instr → (is.pc e).regOpIdx ≤ (impl.regOps e instr).length
  stmtRegOpBound : ∀ e frame rest ops,
    (is.pc e).stack = frame :: rest → frame.body[frame.stmtIdx]? = some (ImplStmt.regOp ops) →
    (is.pc e).stmtRegOpIdx ≤ (ops e).length
  topKindOnly : ∀ e, e ∉ impl.engines → ∀ frame rest,
    (is.pc e).stack = frame :: rest → frame.kind = .top

theorem implInv_step (impl : ImplProgram) (e : EngineId) (is is' : ImplState)
    (hInv : ImplInv impl is) (hStep : ImplStep impl e is is') : ImplInv impl is' where
  regOpBound := by
    intro e' frame' rest' f' instr' hStack' hStmt' hInstr'
    cases hStep with
    | regOpStep _ frame rest f instr dst src t hStack hStmt hInstr hRegOp =>
      by_cases he : e' = e
      · subst he
        simp only [funUpdate, ite_true] at hStack' hInstr' ⊢
        have hFE : frame = frame' := (List.cons.inj (hStack ▸ hStack')).1; subst hFE
        rw [hStmt] at hStmt'; obtain rfl := ImplStmt.block.inj (Option.some.inj hStmt')
        rw [hInstr] at hInstr'; obtain rfl := Option.some.inj hInstr'
        exact Nat.succ_le_of_lt (Nat.lt_of_not_le (fun h => by simp [List.getElem?_eq_none h] at hRegOp))
      · simp only [funUpdate, if_neg he] at hStack' hInstr' ⊢
        exact hInv.regOpBound e' frame' rest' f' instr' hStack' hStmt' hInstr'
    | stmtRegOpStep _ frame rest ops dst src t hStack hStmt hOp =>
      by_cases he : e' = e
      · subst he
        simp only [funUpdate, ite_true] at hStack' hStmt' ⊢
        have hFE : frame = frame' := (List.cons.inj (hStack ▸ hStack')).1; subst hFE
        rw [hStmt] at hStmt'; simp at hStmt'
      · simp only [funUpdate, if_neg he] at hStack' hInstr' ⊢
        exact hInv.regOpBound e' frame' rest' f' instr' hStack' hStmt' hInstr'
    | stmtRegOpDone _ frame rest ops hStack hStmt hDone =>
      by_cases he : e' = e
      · subst he
        simp only [funUpdate, ite_true] at hStack' hInstr' ⊢
        omega
      · simp only [funUpdate, if_neg he] at hStack' hInstr' ⊢
        exact hInv.regOpBound e' frame' rest' f' instr' hStack' hStmt' hInstr'
    | commit _ | retire _ =>
      exact hInv.regOpBound e' frame' rest' f' instr' hStack' hStmt' hInstr'
    | _ =>
      by_cases he : e' = e
      · subst he; simp only [funUpdate, ite_true] at hStack' hInstr' ⊢
        omega
      · try simp only [funUpdate, if_neg he] at hStack' hInstr' ⊢
        exact hInv.regOpBound e' frame' rest' f' instr' hStack' hStmt' hInstr'
  stmtRegOpBound := by
    intro e' frame' rest' ops' hStack' hStmt'
    cases hStep with
    | stmtRegOpStep _ _ _ ops₀ _ _ _ hStack hStmt hOp =>
      by_cases he : e' = e
      · subst he; simp only [funUpdate, ite_true] at hStack' hStmt' ⊢
        have hFE := (List.cons.inj (hStack ▸ hStack')).1
        rw [← hFE, hStmt] at hStmt'
        have hOpsEq : ops₀ = ops' := by simpa using hStmt'
        rw [← hOpsEq]
        exact Nat.succ_le_of_lt (Nat.lt_of_not_le (fun h => by simp [List.getElem?_eq_none h] at hOp))
      · simp only [funUpdate, if_neg he] at hStack' ⊢
        exact hInv.stmtRegOpBound e' frame' rest' ops' hStack' hStmt'
    | stmtRegOpDone _ _ _ _ hStack hStmt hDone =>
      by_cases he : e' = e
      · subst he; simp only [funUpdate, ite_true] at hStack' ⊢; exact Nat.zero_le _
      · simp only [funUpdate, if_neg he] at hStack' ⊢
        exact hInv.stmtRegOpBound e' frame' rest' ops' hStack' hStmt'
    | regOpStep _ _ _ _ _ _ _ _ hStack hStmt _ _ =>
      by_cases he : e' = e
      · subst he; simp only [funUpdate, ite_true] at hStack' hStmt'
        have hFE := (List.cons.inj (hStack ▸ hStack')).1
        rw [← hFE, hStmt] at hStmt'; simp at hStmt'
      · simp only [funUpdate, if_neg he] at hStack' ⊢
        exact hInv.stmtRegOpBound e' frame' rest' ops' hStack' hStmt'
    | issue _ _ _ _ _ hStack hStmt _ _ _ =>
      by_cases he : e' = e
      · subst he; simp only [funUpdate, ite_true] at hStack' hStmt'
        have hFE := (List.cons.inj (hStack ▸ hStack')).1
        rw [← hFE, hStmt] at hStmt'; simp at hStmt'
      · simp only [funUpdate, if_neg he] at hStack' ⊢
        exact hInv.stmtRegOpBound e' frame' rest' ops' hStack' hStmt'
    | commit _ | retire _ =>
      exact hInv.stmtRegOpBound e' frame' rest' ops' hStack' hStmt'
    | blockDone _ _ _ _ hStack _ _ =>
      by_cases he : e' = e
      · subst he; simp only [funUpdate, ite_true] at hStack' ⊢; exact Nat.zero_le _
      · simp only [funUpdate, if_neg he] at hStack' ⊢
        exact hInv.stmtRegOpBound e' frame' rest' ops' hStack' hStmt'
    | loopEnter _ _ _ _ _ hStack _ _ =>
      by_cases he : e' = e
      · subst he; simp only [funUpdate, ite_true] at hStack' ⊢; exact Nat.zero_le _
      · simp only [funUpdate, if_neg he] at hStack' ⊢
        exact hInv.stmtRegOpBound e' frame' rest' ops' hStack' hStmt'
    | loopSkip _ _ _ _ _ hStack _ _ =>
      by_cases he : e' = e
      · subst he; simp only [funUpdate, ite_true] at hStack' ⊢; exact Nat.zero_le _
      · simp only [funUpdate, if_neg he] at hStack' ⊢
        exact hInv.stmtRegOpBound e' frame' rest' ops' hStack' hStmt'
    | loopBack _ _ _ _ _ hStack _ _ =>
      by_cases he : e' = e
      · subst he; simp only [funUpdate, ite_true] at hStack' ⊢; exact Nat.zero_le _
      · simp only [funUpdate, if_neg he] at hStack' ⊢
        exact hInv.stmtRegOpBound e' frame' rest' ops' hStack' hStmt'
    | condTrue _ _ _ _ _ _ _ hStack _ _ =>
      by_cases he : e' = e
      · subst he; simp only [funUpdate, ite_true] at hStack' ⊢; exact Nat.zero_le _
      · simp only [funUpdate, if_neg he] at hStack' ⊢
        exact hInv.stmtRegOpBound e' frame' rest' ops' hStack' hStmt'
    | condFalse _ _ _ _ _ _ _ hStack _ _ =>
      by_cases he : e' = e
      · subst he; simp only [funUpdate, ite_true] at hStack' ⊢; exact Nat.zero_le _
      · simp only [funUpdate, if_neg he] at hStack' ⊢
        exact hInv.stmtRegOpBound e' frame' rest' ops' hStack' hStmt'
    | condDone _ _ _ _ _ hStack _ _ =>
      by_cases he : e' = e
      · subst he; simp only [funUpdate, ite_true] at hStack' ⊢; exact Nat.zero_le _
      · simp only [funUpdate, if_neg he] at hStack' ⊢
        exact hInv.stmtRegOpBound e' frame' rest' ops' hStack' hStmt'
  topKindOnly := by
    intro e' hNotMem frame' rest' hStack'
    have hNe : e' ≠ e := fun h => hNotMem (h ▸ hStep.mem_engines)
    cases hStep with
    | commit _ | retire _ => exact hInv.topKindOnly e' hNotMem frame' rest' hStack'
    | _ =>
      simp only [funUpdate, if_neg hNe] at hStack'
      exact hInv.topKindOnly e' hNotMem frame' rest' hStack'

-- Main check implies semaphore bound. Takes the main check directly
-- (not the full depSatisfied disjunction, since the vacuous case is handled by the gate).
theorem mainCheck_implies_sema_ge (spec : Program) (alloc : PerInstrAllocR spec impl)
    (ss : SpecState) (is : ImplState) (e : EngineId) (instr : DataPathInstrId)
    (hSemaEq : ∀ i, is.semaphores (alloc.sema i) = ss.rc i)
    (hWSE : ∀ i, impl.waitOf i = match depProducer (spec.depGraph i) with | some p => alloc.sema p | none => impl.waitOf i)
    (hWf : AllocatableAt spec ss e instr)
    (hMainCheck : match spec.depGraph instr with
      | .none => True
      | .dep producer offset =>
        let sharedLoop := innermostSharedScope spec.engines spec.body producer instr
        match innermostParentScope spec.engines spec.body producer with
        | none => ss.rc producer ≥ totalEntriesOpt ss e sharedLoop - offset
        | some plid =>
          ss.rc producer ≥ cumExecs ss e plid sharedLoop (totalEntriesOpt ss e sharedLoop - offset))
    : is.semaphores (impl.waitOf instr) ≥ expectedWaitVal spec ss e instr := by
  simp only [expectedWaitVal, AllocatableAt] at *
  match hDep : spec.depGraph instr with
  | .none => simp
  | .dep producer offset =>
    simp only [hDep] at hMainCheck hWf ⊢
    have hWS : impl.waitOf instr = alloc.sema producer := by
      have := hWSE instr; simp [hDep, depProducer] at this; exact this
    rw [hWS, hSemaEq]
    match hPL : innermostParentScope spec.engines spec.body producer with
    | none =>
      have hSS := innermostSharedScope_eq_none_of_parent_eq_none
        (consumer := instr) hPL
      simp only [hPL, hSS, totalEntriesOpt] at hMainCheck ⊢
      exact hMainCheck
    | some plid =>
      simp only [hPL] at hMainCheck hWf ⊢
      split at hWf
      · rename_i h; simp [h]; rw [hWf] at hMainCheck; omega
      · rename_i h; simp [h]; rw [hWf] at hMainCheck; exact hMainCheck

theorem foldRegOps_perInstrExpectedRegOps_waitReg
    {spec : Program} {ss : SpecState} {e : EngineId} {instr : DataPathInstrId}
    {ab : AllocBase spec impl}
    (baseRegs : RegId → Nat)
    (hLoopReg : ∀ plid, baseRegs (ab.monotoneReg e plid) = totalEntries ss e plid)
    : foldRegOps (perInstrExpectedRegOps spec (ab.waitReg e) ab.monotoneReg e instr) baseRegs (ab.waitReg e)
      = expectedWaitVal spec ss e instr := by
  unfold perInstrExpectedRegOps expectedWaitVal
  match hDep : spec.depGraph instr with
  | .none => simp [foldRegOps, funUpdate, applyRegOpKind]
  | .dep producer offset =>
    simp; match hPL : innermostParentScope spec.engines spec.body producer with
    | none => simp [foldRegOps, funUpdate, applyRegOpKind]
    | some plid => simp; split <;> simp [foldRegOps, funUpdate, applyRegOpKind, hLoopReg plid]

theorem sema_wait_implies_depSatisfied
    {spec : Program} {ss : SpecState} {e : EngineId} {instr : DataPathInstrId}
    {impl : ImplProgram} {is : ImplState} {alloc : PerInstrAllocR spec impl}
    (hSema : ∀ i, is.semaphores (alloc.sema i) = ss.rc i)
    (hWait : is.semaphores (impl.waitOf instr) ≥ is.registers e (impl.waitReg e instr))
    (hWRV : is.registers e (impl.waitReg e instr) = expectedWaitVal spec ss e instr)
    (hWf : AllocatableAt spec ss e instr)
    : depSatisfied spec (spec.depGraph instr) instr ss e = true := by
  simp only [depSatisfied, expectedWaitVal, AllocatableAt] at *
  match hDep : spec.depGraph instr with
  | .none => simp
  | .dep producer offset =>
    simp only [hDep] at hWRV hWf
    have hWS : impl.waitOf instr = alloc.sema producer := by
      have := alloc.waitOfEq instr; simp [hDep, depProducer] at this; exact this
    rw [hWS] at hWait; rw [hWRV] at hWait; rw [hSema] at hWait
    simp only [Bool.or_eq_true]
    match hPL : innermostParentScope spec.engines spec.body producer with
    | none =>
      have hSS := innermostSharedScope_eq_none_of_parent_eq_none
        (consumer := instr) hPL
      simp only [hPL, hSS, totalEntriesOpt, decide_eq_true_eq] at hWait ⊢
      exact Or.inr hWait
    | some plid =>
      simp only [hPL] at hWait hWf
      by_cases hEq : innermostSharedScope spec.engines spec.body producer instr = some plid
      · simp only [hEq, ↓reduceIte] at hWait hWf
        right
        simp only [hEq, decide_eq_true_eq]
        rw [hWf]
        exact hWait
      · simp only [hEq, ↓reduceIte] at hWait hWf
        right
        simp only [decide_eq_true_eq]
        rw [hWf]
        exact hWait

def atLoopStart (is : ImplState) (e : EngineId) (lid : ScopeId) : Prop :=
  ∃ frame rest, (is.pc e).stack = frame :: rest ∧
    (frame.kind = .loop lid ∨ frame.kind = .cond lid) ∧ frame.stmtIdx = 0

abbrev SemaInvMono (SemaInv : SpecState → ImplState → Prop) : Prop :=
  ∀ (ss0 ss1 : SpecState) (is0 is1 : ImplState),
    ss0.rc = ss1.rc → is0.semaphores = is1.semaphores →
    SemaInv ss0 is0 → SemaInv ss1 is1

abbrev RetireSemaInv (impl : ImplProgram) (SemaInv : SpecState → ImplState → Prop) : Prop :=
  ∀ (e' : EngineId) (instr : DataPathInstrId) (rest : List (DataPathInstrId × Phase))
    (ss0 : SpecState) (is0 : ImplState),
    SemaInv ss0 is0 →
    ss0.inflight e' = (instr, Phase.committed) :: rest →
    let ss1 := specRetireUpdate ss0 e' instr rest
    let is1 := { is0 with inflight := funUpdate is0.inflight e' rest,
                          semaphores := funUpdate is0.semaphores (impl.updateOf instr) (is0.semaphores (impl.updateOf instr) + 1) }
    SemaInv ss1 is1

abbrev ForwardIssueSemaGe (spec : Program) (impl : ImplProgram) (ab : AllocBase spec impl)
    (SemaInv : SpecState → ImplState → Prop) : Prop :=
  ∀ (e : EngineId) (instr : DataPathInstrId) (ss : SpecState) (is : ImplState),
    SemaInv ss is →
    depSatisfied spec (spec.depGraph instr) instr ss e = true →
    AllocatableAt spec ss e instr →
    SpecInv spec ss →
    (∀ plid, is.registers e (ab.monotoneReg e plid) = totalEntries ss e plid) →
    (∀ lid, is.registers e (ab.tripReg e lid) = tripEntries ss e spec.body lid) →
    is.semaphores (impl.waitOf instr) ≥
      foldRegOps (impl.regOps e instr) (fun r => if r = ab.waitReg e then 0 else is.registers e r) (ab.waitReg e)

-- Properties of inner register operations (before gate wrapping).
-- Takes the inner ops function directly, so callers can pass `perInstrExpectedRegOps` or `perScopeExpectedRegOps`.
structure InnerRegOpsWf (innerOps : EngineId → DataPathInstrId → List RegOp)
    (ab : AllocBase spec impl) : Prop where
  firstSafe : ∀ e i (src : RegId) (t : RegOpKind),
    (innerOps e i)[0]? = some (ab.waitReg e, src, t) →
    t.usesDst = false ∧ (src = ab.waitReg e → ∃ n, t = .const n)
  nonEmpty : ∀ e i, (innerOps e i).length > 0
  dstWaitReg : ∀ e i (idx : Nat) (dst src : RegId) (t : RegOpKind),
    (innerOps e i)[idx]? = some (dst, src, t) → dst = ab.waitReg e

-- Deprecated: old name for backward compat during migration
abbrev RegOpsWf (impl : ImplProgram) (ab : AllocBase spec impl) : Prop :=
  InnerRegOpsWf impl.regOps ab

abbrev IssueDepSat (spec : Program) (impl : ImplProgram) (ab : AllocBase spec impl)
    (SemaInv : SpecState → ImplState → Prop) : Prop :=
  ∀ (e : EngineId) (instr : DataPathInstrId) (ss : SpecState) (is : ImplState),
    SemaInv ss is → SpecInv spec ss → AllocatableAt spec ss e instr →
    is.semaphores (impl.waitOf instr) ≥ is.registers e (ab.waitReg e) →
    is.registers e (ab.waitReg e) =
      foldRegOps (impl.regOps e instr) (fun r => if r = ab.waitReg e then 0 else is.registers e r) (ab.waitReg e) →
    (∀ plid,
      (fun r => if r = ab.waitReg e then 0 else is.registers e r) (ab.monotoneReg e plid) =
      totalEntries ss e plid) →
    (∀ lid, is.registers e (ab.tripReg e lid) = tripEntries ss e spec.body lid) →
    depSatisfied spec (spec.depGraph instr) instr ss e = true


structure MatchStates (spec : Program) (impl : ImplProgram) (ab : AllocBase spec impl)
    (SemaInv : SpecState → ImplState → Prop)
    (ss : SpecState) (is : ImplState) : Prop where
  dataPathEq : is.dataPathState = ss.dataPathState
  inflightEq : ∀ e, is.inflight e = ss.inflight e
  controlEq : ∀ e, is.controlState e = ss.controlState e
  semaInv : SemaInv ss is
  monotoneRegInv : ∀ e lid,
    (¬ atLoopStart is e lid → is.registers e (ab.monotoneReg e lid) = totalEntries ss e lid)
  tripRegInv : ∀ e lid,
    ((∀ lid', ¬ atLoopStart is e lid') →
     is.registers e (ab.tripReg e lid) = tripEntries ss e spec.body lid)
  regOpFold : ∀ e frame rest ops,
    (is.pc e).stack = frame :: rest →
    frame.body[frame.stmtIdx]? = some (.regOp ops) →
    (∀ lid, foldRegOps ((ops e).drop (is.pc e).stmtRegOpIdx) (is.registers e) (ab.monotoneReg e lid) = totalEntries ss e lid) ∧
    (∀ lid, foldRegOps ((ops e).drop (is.pc e).stmtRegOpIdx) (is.registers e) (ab.tripReg e lid) = tripEntries ss e spec.body lid)
  pcCorr : ∀ e, PCCorr ab (ss.pc e) (is.pc e)
  waitRegChain : ∀ e frame rest f instr,
    (is.pc e).stack = frame :: rest → frame.body[frame.stmtIdx]? = some (ImplStmt.block f) →
    (f e)[(is.pc e).instrIdx]? = some instr → (is.pc e).regOpIdx > 0 →
    let baseRegs := fun r => if r = ab.waitReg e then 0 else is.registers e r
    is.registers e (ab.waitReg e) =
      (foldRegOps ((impl.regOps e instr).take (is.pc e).regOpIdx) baseRegs) (ab.waitReg e)
  gateRegChain : ∀ e frame rest f instr,
    (is.pc e).stack = frame :: rest → frame.body[frame.stmtIdx]? = some (ImplStmt.block f) →
    (f e)[(is.pc e).instrIdx]? = some instr → (is.pc e).regOpIdx > 0 →
    let baseRegs := fun r => if r = ab.waitReg e then 0 else is.registers e r
    is.registers e (ab.gateReg e) =
      (foldRegOps ((impl.regOps e instr).take (is.pc e).regOpIdx) baseRegs) (ab.gateReg e)

def perInstrSemaInv (alloc : PerInstrAllocR spec impl) (ss : SpecState) (is : ImplState) : Prop :=
  ∀ i, is.semaphores (alloc.sema i) = ss.rc i

inductive ImplStar (impl : ImplProgram) (e : EngineId) : ImplState → ImplState → Prop where
  | refl : ImplStar impl e s s
  | step : ImplStep impl e s s' → ImplStar impl e s' s'' → ImplStar impl e s s''

theorem implStar_trans {impl : ImplProgram} {e : EngineId} {s₁ s₂ s₃ : ImplState}
    (h₁ : ImplStar impl e s₁ s₂) (h₂ : ImplStar impl e s₂ s₃) : ImplStar impl e s₁ s₃ := by
  induction h₁ with | refl => exact h₂ | step hStep _ ih => exact ImplStar.step hStep (ih h₂)

inductive ImplStarAny (impl : ImplProgram) : ImplState → ImplState → Prop where
  | refl : ImplStarAny impl s s
  | step : (∃ e, ImplStep impl e s s') → ImplStarAny impl s' s'' → ImplStarAny impl s s''

/-! `ImplPlusAny` requires taking 1 or more steps. 0 steps is not allowed. -/
inductive ImplPlusAny (impl : ImplProgram) : ImplState → ImplState → Prop where
  | step : ImplStep impl e s s' → ImplStarAny impl s' s'' → ImplPlusAny impl s s''

theorem implInv_star (impl : ImplProgram) (e : EngineId) (is is' : ImplState)
    (hInv : ImplInv impl is) (hStar : ImplStar impl e is is') : ImplInv impl is' := by
  induction hStar with | refl => exact hInv | step hStep _ ih => exact ih (implInv_step impl e _ _ hInv hStep)

theorem implInv_starAny (impl : ImplProgram) (is is' : ImplState)
    (hInv : ImplInv impl is) (hStar : ImplStarAny impl is is') : ImplInv impl is' := by
  induction hStar with
  | refl => exact hInv
  | step hStep _ ih =>
      obtain ⟨e, hStep⟩ := hStep
      exact ih (implInv_step impl e _ _ hInv hStep)

theorem ImplStar_to_ImplStarAny {impl : ImplProgram} {e : EngineId} {is is' : ImplState}
    (h : ImplStar impl e is is') : ImplStarAny impl is is' := by
  induction h with | refl => exact ImplStarAny.refl | step hStep _ ih => exact ImplStarAny.step ⟨e, hStep⟩ ih

theorem ImplStarAny.trans {impl : ImplProgram} {s₁ s₂ s₃ : ImplState}
    (h₁ : ImplStarAny impl s₁ s₂) (h₂ : ImplStarAny impl s₂ s₃) : ImplStarAny impl s₁ s₃ := by
  induction h₁ with | refl => exact h₂ | step hStep _ ih => exact ImplStarAny.step hStep (ih h₂)

theorem ImplPlusAny.to_star {impl : ImplProgram} {s₁ s₂ : ImplState}
    (h : ImplPlusAny impl s₁ s₂) : ImplStarAny impl s₁ s₂ := by
  cases h with | step hStep hTail => exact ImplStarAny.step ⟨_, hStep⟩ hTail

theorem ImplStarAny.trans_plus {impl : ImplProgram} {s₁ s₂ s₃ : ImplState}
    (h₁ : ImplStarAny impl s₁ s₂) (h₂ : ImplPlusAny impl s₂ s₃) : ImplPlusAny impl s₁ s₃ := by
  induction h₁ with
  | refl => exact h₂
  | step hStep hTail _ =>
      obtain ⟨e, h⟩ := hStep
      exact ImplPlusAny.step (e := e) h (ImplStarAny.trans hTail h₂.to_star)

theorem spec_guard_of_impl {spec : Program} {impl : ImplProgram}
    (hBaseEq : spec.toProgramBase = impl.toProgramBase) {e : EngineId} {sid : ScopeId}
    {cs : ControlState} {b : Bool}
    (hControl : is_cs = cs) (hGuard : impl.guard e sid is_cs = b)
    : spec.guard e sid cs = b := by
  have := congrArg ProgramBase.guard hBaseEq; rw [this, ← hControl]; exact hGuard

theorem not_atLoopStart_of_not_atRegOp {is : ImplState} {e : EngineId}
    {frame : ImplFrame} {rest : List ImplFrame}
    (hStack : (is.pc e).stack = frame :: rest) (hNRO : ¬ atRegOp frame)
    : ∀ lid, ¬ atLoopStart is e lid := by
  intro lid ⟨f, r, hS, hK, hI⟩
  have := List.cons.inj (hStack ▸ hS)
  rw [← this.1] at hK hI; apply hNRO; simp [atRegOp]
  rcases hK with hK | hK <;> rw [hK] <;> exact hI

/-- In a FrameCorr frame, if `¬ atRegOp imf`, then no `.regOp` appears at or after `imf.stmtIdx`. -/
theorem frameCorr_no_regOp {ab : AllocBase spec impl} {sf : Frame} {imf : ImplFrame}
    (hFC : FrameCorr ab sf imf) (hNotRO : ¬ atRegOp imf)
    {n : Nat} {ops} (hGe : n ≥ imf.stmtIdx) (hGet : imf.body[n]? = some (.regOp ops))
    : False := by
  obtain ⟨_, ⟨implBody, hBM, hBE⟩, hIC⟩ := hFC
  cases hk : imf.kind with
  | top => rw [hk] at hBE; rw [hBE] at hGet; exact bodyMatch_no_regOp hBM hGet
  | loop lid =>
    rw [hk] at hBE; simp at hBE; rw [hBE] at hGet
    have hStmt : imf.stmtIdx ≥ 1 := by
      simp [atRegOp, hk] at hNotRO; omega
    cases n with
    | zero => omega
    | succ m => simp [List.getElem?_cons_succ] at hGet; exact bodyMatch_no_regOp hBM hGet
  | cond sid =>
    rw [hk] at hBE; simp at hBE; rw [hBE] at hGet
    have hStmt : imf.stmtIdx ≥ 1 := by
      simp [atRegOp, hk] at hNotRO; omega
    cases n with
    | zero => omega
    | succ m => simp [List.getElem?_cons_succ] at hGet; exact bodyMatch_no_regOp hBM hGet

private theorem implBody_from_frameCorr {ab : AllocBase spec impl} {sf : Frame} {imf : ImplFrame}
    (hFC : FrameCorr ab sf imf) (hNotRO : ¬ atRegOp imf)
    : ∃ implBody, BodyMatch ab.monotoneReg ab.tripReg sf.body implBody ∧
        implBody[sf.stmtIdx]? = imf.body[imf.stmtIdx]? := by
  obtain ⟨_, ⟨implBody, hBM, hBE⟩, hIC⟩ := hFC
  refine ⟨implBody, hBM, ?_⟩
  have hIC2 := hIC.2 hNotRO
  cases hk : imf.kind <;> simp [hk] at hBE hIC2
  · rw [hBE]; congr 1
  all_goals
    rw [hBE]; cases hsi : imf.stmtIdx with
    | zero => exact absurd hsi (by simp [atRegOp, hk] at hNotRO; exact hNotRO)
    | succ n => simp [List.getElem?_cons_succ]; congr 1; omega

theorem frameCorr_loop_stmt {ab : AllocBase spec impl} {sf : Frame} {imf : ImplFrame}
    (hFC : FrameCorr ab sf imf) (hNotRO : ¬ atRegOp imf)
    {lid : ScopeId} {implLoopBody : List ImplStmt}
    (hStmt : imf.body[imf.stmtIdx]? = some (ImplStmt.loop lid implLoopBody))
    : ∃ specLoopBody implInner,
        sf.body[sf.stmtIdx]? = some (Stmt.loop lid specLoopBody) ∧
        BodyMatch ab.monotoneReg ab.tripReg specLoopBody implInner ∧
        implLoopBody = [ImplStmt.regOp (scopeEntryOps ab.monotoneReg ab.tripReg specLoopBody · lid)] ++ implInner := by
  obtain ⟨implBody, hBM, hEq⟩ := implBody_from_frameCorr hFC hNotRO
  rw [hStmt] at hEq; exact bodyMatch_loop_at hBM (by rw [← hEq])

theorem frameCorr_block_stmt {ab : AllocBase spec impl} {sf : Frame} {imf : ImplFrame}
    (hFC : FrameCorr ab sf imf) (hNotRO : ¬ atRegOp imf)
    {f : EngineId → List DataPathInstrId}
    (hStmt : imf.body[imf.stmtIdx]? = some (ImplStmt.block f))
    : sf.body[sf.stmtIdx]? = some (Stmt.block f) := by
  obtain ⟨implBody, hBM, hEq⟩ := implBody_from_frameCorr hFC hNotRO
  rw [hStmt] at hEq; exact bodyMatch_block_at hBM (by rw [← hEq])

theorem frameCorr_cond_stmt {ab : AllocBase spec impl} {sf : Frame} {imf : ImplFrame}
    (hFC : FrameCorr ab sf imf) (hNotRO : ¬ atRegOp imf)
    {thenId elseId : ScopeId} {implThen implElse : List ImplStmt}
    (hStmt : imf.body[imf.stmtIdx]? = some (ImplStmt.cond thenId elseId implThen implElse))
    : ∃ specThen specElse implThenInner implElseInner,
        sf.body[sf.stmtIdx]? = some (Stmt.cond thenId elseId specThen specElse) ∧
        BodyMatch ab.monotoneReg ab.tripReg specThen implThenInner ∧
        BodyMatch ab.monotoneReg ab.tripReg specElse implElseInner ∧
        implThen = [ImplStmt.regOp (scopeEntryOps ab.monotoneReg ab.tripReg specThen · thenId)] ++ implThenInner ∧
        implElse = [ImplStmt.regOp (scopeEntryOps ab.monotoneReg ab.tripReg specElse · elseId)] ++ implElseInner := by
  obtain ⟨implBody, hBM, hEq⟩ := implBody_from_frameCorr hFC hNotRO
  rw [hStmt] at hEq; exact bodyMatch_cond_at hBM (by rw [← hEq])

theorem frameCorr_advance_parent {ab : AllocBase spec impl}
    {sparent : Frame} {parent : ImplFrame}
    (hPC : FrameCorr ab sparent parent)
    (hNotRO : ¬ atRegOp parent)
    (_ : sparent.stmtIdx < sparent.body.length)
    (_ : parent.stmtIdx < parent.body.length)
    : FrameCorr ab ⟨sparent.body, sparent.stmtIdx + 1, sparent.kind⟩
        ⟨parent.body, parent.stmtIdx + 1, parent.kind⟩ := by
  obtain ⟨hPKind, ⟨pImpl, hPBM, hPBE⟩, hPIdx⟩ := hPC
  have hIC2 := hPIdx.2 hNotRO
  exact ⟨hPKind, ⟨pImpl, hPBM, hPBE⟩, by
    constructor
    · intro hAR; simp [atRegOp] at hAR
      cases hk : parent.kind <;> simp [hk] at hAR
    · intro _; cases hk : parent.kind <;> simp [hk] at hIC2 ⊢ <;> omega⟩

theorem monotoneRegInv_preserved_no_reg_no_hist
    {spec : Program} {impl : ImplProgram} {ab : AllocBase spec impl}
    {ss ss' : SpecState} {is is' : ImplState}
    (hLoopRegInv : ∀ e lid,
      (¬ atLoopStart is e lid → is.registers e (ab.monotoneReg e lid) = totalEntries ss e lid))
    (hRegs : is'.registers = is.registers)
    (hHist : ∀ e lid (ol : Option ScopeId) k, ss'.scopeEntryHistory e lid ol k = ss.scopeEntryHistory e lid ol k)
    (hPC : ∀ e lid, atLoopStart is' e lid ↔ atLoopStart is e lid)
    : ∀ e lid,
      (¬ atLoopStart is' e lid → is'.registers e (ab.monotoneReg e lid) = totalEntries ss' e lid) := by
  intro e lid; simp only [hRegs, totalEntries, hHist]
  exact fun h => (hLoopRegInv e lid) (mt (hPC e lid).mpr h)

theorem tripRegInv_preserved_no_reg_no_hist
    {spec : Program} {impl : ImplProgram} {ab : AllocBase spec impl}
    {ss ss' : SpecState} {is is' : ImplState}
    (hTripRegInv : ∀ e lid,
      ((∀ lid', ¬ atLoopStart is e lid') →
       is.registers e (ab.tripReg e lid) = tripEntries ss e spec.body lid))
    (hRegs : is'.registers = is.registers)
    (hHist : ∀ e lid (ol : Option ScopeId) k, ss'.scopeEntryHistory e lid ol k = ss.scopeEntryHistory e lid ol k)
    (hPC : ∀ e lid, atLoopStart is' e lid ↔ atLoopStart is e lid)
    : ∀ e lid,
      ((∀ lid', ¬ atLoopStart is' e lid') →
       is'.registers e (ab.tripReg e lid) = tripEntries ss' e spec.body lid) := by
  intro e lid; simp only [hRegs, tripEntries, scopeParent, totalEntries, hHist]
  exact fun h => (hTripRegInv e lid) (fun lid' h' => h lid' ((hPC e lid').mpr h'))

theorem foldRegOps_append (a b : List RegOp) (regs : RegId → Nat) :
    foldRegOps (a ++ b) regs = foldRegOps b (foldRegOps a regs) := by
  induction a generalizing regs with
  | nil => simp [foldRegOps]
  | cons op rest ih => obtain ⟨dst, src, t⟩ := op; simp [foldRegOps, ih]

-- If no op in the list writes to `g` or reads `g` as source, then funUpdate g v
-- doesn't affect the result at any register.
theorem foldRegOps_irrelevant_update {ops : List RegOp}
    {regs : RegId → Nat} {g : RegId} {v : Nat}
    (hNotDst : ∀ op ∈ ops, op.1 ≠ g)
    (hNotSrc : ∀ op ∈ ops, op.2.1 ≠ g)
    : ∀ r, r ≠ g → foldRegOps ops (funUpdate regs g v) r = foldRegOps ops regs r := by
  induction ops generalizing regs with
  | nil => intro r hr; simp [foldRegOps, funUpdate, hr]
  | cons op rest ih =>
    obtain ⟨dst, src, t⟩ := op
    have hd : dst ≠ g := hNotDst _ (List.mem_cons_self ..)
    have hs : src ≠ g := hNotSrc _ (List.mem_cons_self ..)
    intro r hr; simp only [foldRegOps]
    have : funUpdate (funUpdate regs g v) dst
        (applyRegOpKind t ((funUpdate regs g v) src) ((funUpdate regs g v) dst)) =
      funUpdate (funUpdate regs dst (applyRegOpKind t (regs src) (regs dst))) g v := by
        ext x; simp only [funUpdate]
        by_cases hxg : x = g <;> by_cases hxd : x = dst <;> simp_all
    rw [this]
    exact ih (fun op hm => hNotDst op (List.mem_cons_of_mem _ hm))
      (fun op hm => hNotSrc op (List.mem_cons_of_mem _ hm)) r hr

-- Gate decomposition: the waitReg value after processing wrapWithGate ops.
-- When gated (dep with shared loop): waitReg = gate * innerResult
-- When ungated (no dep or no shared loop): waitReg = innerResult
-- The gate value is: if tripReg > offset then 1 else 0
theorem foldRegOps_wrapWithGate_waitReg {spec : Program} {gateR waitR : RegId}
    {tripReg : EngineId → ScopeId → RegId} {e : EngineId} {consumer : DataPathInstrId}
    {innerOps : List RegOp}
    {regs : RegId → Nat}
    (hGateNeWait : gateR ≠ waitR)
    (hInnerDst : ∀ op ∈ innerOps, op.1 = waitR)
    (hInnerSrcNeGate : ∀ op ∈ innerOps, op.2.1 ≠ gateR)
    (hResNeWait : ∀ sid, tripReg e sid ≠ waitR)
    (hFirstSafe : ∀ src t, innerOps[0]? = some (waitR, src, t) →
        t.usesDst = false ∧ (src = waitR → ∃ n, t = .const n))
    (hNonEmpty : innerOps.length > 0)
    : let wrapped := wrapWithGate spec gateR waitR tripReg e consumer innerOps
      let innerResult := foldRegOps innerOps regs waitR
      match spec.depGraph consumer with
      | .none => foldRegOps wrapped regs waitR = innerResult
      | .dep producer offset =>
        match innermostSharedScope spec.engines spec.body producer consumer with
        | some sid =>
          let gate := if regs (tripReg e sid) > offset then 1 else 0
          foldRegOps wrapped regs waitR = gate * innerResult
        | none => foldRegOps wrapped regs waitR = innerResult := by
  match hDep : spec.depGraph consumer with
  | .none =>
    simp only [wrapWithGate, hDep]
  | .dep producer offset =>
    show match innermostSharedScope spec.engines spec.body producer consumer with
      | some sid => foldRegOps (wrapWithGate spec gateR waitR tripReg e consumer innerOps) regs waitR =
          (if regs (tripReg e sid) > offset then 1 else 0) * foldRegOps innerOps regs waitR
      | none => foldRegOps (wrapWithGate spec gateR waitR tripReg e consumer innerOps) regs waitR =
          foldRegOps innerOps regs waitR
    match hSS : innermostSharedScope spec.engines spec.body producer consumer with
    | some sid =>
      simp only [wrapWithGate, hDep, hSS]
      simp only [foldRegOps_append]
      have hResNe : tripReg e sid ≠ waitR := hResNeWait sid
      have hPrefixEq : foldRegOps [(waitR, waitR, .const 0), (gateR, tripReg e sid, .isGT offset)] regs =
          funUpdate (funUpdate regs waitR 0) gateR (if regs (tripReg e sid) > offset then 1 else 0) := by
        simp [foldRegOps, applyRegOpKind, funUpdate, hResNe]
      rw [hPrefixEq]
      have hNotDstG : ∀ op ∈ innerOps, op.1 ≠ gateR :=
        fun op hMem h => hGateNeWait (h.symm.trans (hInnerDst op hMem))
      let gv := if regs (tripReg e sid) > offset then 1 else 0
      let F := funUpdate (funUpdate regs waitR 0) gateR gv
      have hGateUnchanged : foldRegOps innerOps F gateR = gv := by
        rw [foldRegOps_other hNotDstG]; simp [F]
      have hInnerEq : foldRegOps innerOps F waitR = foldRegOps innerOps regs waitR := by
        show foldRegOps innerOps (funUpdate (funUpdate regs waitR 0) gateR gv) waitR = _
        rw [foldRegOps_irrelevant_update hNotDstG hInnerSrcNeGate waitR (Ne.symm hGateNeWait)]
        exact foldRegOps_dst_init_irrelevant
          (fun r hr => by simp [funUpdate, hr]) hInnerDst hFirstSafe hNonEmpty
      -- Suffix: [(waitR, gateR, .mulSrc)]
      change foldRegOps [(waitR, gateR, .mulSrc)] (foldRegOps innerOps F) waitR = _
      simp only [foldRegOps, applyRegOpKind, funUpdate, ite_true]
      rw [hGateUnchanged, hInnerEq]
      exact Nat.mul_comm _ _
    | none =>
      simp only [wrapWithGate, hDep, hSS]

-- foldRegOps of wrapWithGate at waitR doesn't depend on the initial waitR value
theorem foldRegOps_wrapWithGate_waitR_init_irrelevant
    {spec : Program} {gateR waitR : RegId}
    {tripReg : EngineId → ScopeId → RegId} {e : EngineId} {consumer : DataPathInstrId}
    {innerOps : List RegOp}
    {f₁ f₂ : RegId → Nat}
    (hAgree : ∀ r, r ≠ waitR → f₁ r = f₂ r)
    (hGateNeWait : gateR ≠ waitR)
    (hInnerDst : ∀ op ∈ innerOps, op.1 = waitR)
    (hResNeWait : ∀ sid, tripReg e sid ≠ waitR)
    (hFirstSafe : ∀ src t, innerOps[0]? = some (waitR, src, t) →
        t.usesDst = false ∧ (src = waitR → ∃ n, t = .const n))
    (hNonEmpty : innerOps.length > 0)
    : foldRegOps (wrapWithGate spec gateR waitR tripReg e consumer innerOps) f₁ waitR =
      foldRegOps (wrapWithGate spec gateR waitR tripReg e consumer innerOps) f₂ waitR := by
  show foldRegOps (wrapWithGate spec gateR waitR tripReg e consumer innerOps) f₁ waitR =
       foldRegOps (wrapWithGate spec gateR waitR tripReg e consumer innerOps) f₂ waitR
  unfold wrapWithGate
  match hDep : spec.depGraph consumer with
  | .none =>
    simp only []
    exact foldRegOps_dst_init_irrelevant hAgree hInnerDst hFirstSafe hNonEmpty
  | .dep producer offset =>
    simp only []
    match hSS : innermostSharedScope spec.engines spec.body producer consumer with
    | none =>
      simp only []
      exact foldRegOps_dst_init_irrelevant hAgree hInnerDst hFirstSafe hNonEmpty
    | some sid =>
      simp only []
      have hResNe : tripReg e sid ≠ waitR := hResNeWait sid
      have hPrefixAgree : ∀ r,
          foldRegOps [(waitR, waitR, .const 0), (gateR, tripReg e sid, .isGT offset)] f₁ r =
          foldRegOps [(waitR, waitR, .const 0), (gateR, tripReg e sid, .isGT offset)] f₂ r := by
        intro r; simp only [foldRegOps, applyRegOpKind, funUpdate]
        by_cases hw : r = waitR
        · subst hw; simp [hResNe, hAgree _ hResNe]
        · by_cases hg : r = gateR
          · subst hg; simp [hAgree _ hResNe]
          · simp [hw, hg, hAgree r hw]
      simp only [foldRegOps_append]
      exact foldRegOps_congr (foldRegOps_congr hPrefixAgree) waitR

theorem wrapWithGate_nonEmpty {spec : Program} {gateR waitR : RegId}
    {tripReg : EngineId → ScopeId → RegId} {e : EngineId} {consumer : DataPathInstrId}
    {innerOps : List RegOp}
    (hInner : innerOps.length > 0)
    : (wrapWithGate spec gateR waitR tripReg e consumer innerOps).length > 0 := by
  unfold wrapWithGate
  split
  · exact hInner
  · simp only []
    split <;> simp; omega

theorem wrapWithGate_dst {spec : Program} {gateR waitR : RegId}
    {tripReg : EngineId → ScopeId → RegId} {e : EngineId} {consumer : DataPathInstrId}
    {innerOps : List RegOp}
    (hInnerDst : ∀ op ∈ innerOps, op.1 = waitR)
    {idx : Nat} {dst src : RegId} {t : RegOpKind}
    (hGet : (wrapWithGate spec gateR waitR tripReg e consumer innerOps)[idx]? = some (dst, src, t))
    : dst = waitR ∨ dst = gateR := by
  unfold wrapWithGate at hGet
  match hDep : spec.depGraph consumer with
  | .none => simp only [hDep] at hGet; exact Or.inl (hInnerDst _ (List.mem_of_getElem? hGet))
  | .dep producer offset =>
    simp only [hDep] at hGet
    match hSS : innermostSharedScope spec.engines spec.body producer consumer with
    | none => simp only [hSS] at hGet; exact Or.inl (hInnerDst _ (List.mem_of_getElem? hGet))
    | some sid =>
      simp only [hSS, List.cons_append, List.nil_append] at hGet
      match idx with
      | 0 => simp at hGet; exact Or.inl hGet.1.symm
      | 1 => simp at hGet; exact Or.inr hGet.1.symm
      | n + 2 =>
        simp at hGet
        have hMem := List.mem_of_getElem? hGet
        rcases List.mem_append.mp hMem with h | h
        · exact Or.inl (hInnerDst _ h)
        · simp at h; exact Or.inl h.1

-- build MatchStates when only `pc` changes via funUpdate for one engine.
-- Handles ALL 7 fields automatically. User provides:
--   newSpecPC, newImplPC: the new PC values for engine e
--   hPCCorr: PCCorr for the new PCs
--   hAtLoop: atLoopStart iff between old and new impl state
theorem MatchStates.of_funUpdate_pc {spec : Program} {impl : ImplProgram} {ab : AllocBase spec impl}
    {SemaInv : SpecState → ImplState → Prop}
    {ss : SpecState} {is : ImplState} {e : EngineId}
    (hSim : MatchStates spec impl ab SemaInv ss is)
    (hSemaInvMono : SemaInvMono SemaInv)
    (newSpecPC : PC) (newImplPC : ImplPC)
    (hPCCorr : PCCorr ab newSpecPC newImplPC)
    (hRegOp0 : newImplPC.regOpIdx = 0)
    (hAtLoop : ∀ e' lid, atLoopStart
      { is with pc := funUpdate is.pc e newImplPC } e' lid ↔ atLoopStart is e' lid)
    (hNoNewRegOp : ∀ frame rest ops, newImplPC.stack = frame :: rest →
      frame.body[frame.stmtIdx]? ≠ some (.regOp ops))
    : MatchStates spec impl ab SemaInv
        { ss with pc := funUpdate ss.pc e newSpecPC }
        { is with pc := funUpdate is.pc e newImplPC } where
  dataPathEq := hSim.dataPathEq
  inflightEq := hSim.inflightEq
  controlEq := hSim.controlEq
  semaInv := hSemaInvMono ss _ is _ rfl rfl hSim.semaInv
  monotoneRegInv := monotoneRegInv_preserved_no_reg_no_hist (fun e lid => hSim.monotoneRegInv e lid) rfl (by simp) hAtLoop
  tripRegInv := tripRegInv_preserved_no_reg_no_hist hSim.tripRegInv rfl (by simp) hAtLoop
  regOpFold := by
    intro e' frame' rest' ops' hStack' hStmt'
    by_cases he : e' = e
    · subst he; simp [funUpdate] at hStack'; exact absurd hStmt' (hNoNewRegOp frame' rest' ops' hStack')
    · simp [funUpdate, he] at hStack' ⊢
      exact hSim.regOpFold e' frame' rest' ops' hStack' hStmt'
  pcCorr := by
    intro e'; by_cases he : e' = e
    · subst he; simp [funUpdate]; exact hPCCorr
    · simp [funUpdate, he]; exact hSim.pcCorr e'
  waitRegChain := by
    intro e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
    by_cases he : e' = e
    · subst he; simp [funUpdate] at hROI; rw [hRegOp0] at hROI; omega
    · simp [funUpdate, he] at hStack' hInstr' hROI ⊢
      exact hSim.waitRegChain e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
  gateRegChain := by
    intro e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
    by_cases he : e' = e
    · subst he; simp [funUpdate] at hROI; rw [hRegOp0] at hROI; omega
    · simp [funUpdate, he] at hStack' hInstr' hROI ⊢
      exact hSim.gateRegChain e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI

-- CPDT-style: build MatchStates for loop-enter cases (loopEnter, condTrue, condFalse).
-- These change pc + controlState + scopeEntryHistory but NOT datapath/inflight/registers/semaphores.
-- Handles: dataPathEq, inflightEq, semaInv, waitRegChain automatically.
-- User provides: controlEq proof, monotoneRegInv proof, pcCorr proof.
theorem MatchStates.of_loop_enter {spec : Program} {impl : ImplProgram} {ab : AllocBase spec impl}
    {SemaInv : SpecState → ImplState → Prop}
    {ss : SpecState} {is : ImplState} {e : EngineId}
    (hSim : MatchStates spec impl ab SemaInv ss is)
    (hSemaInvMono : SemaInvMono SemaInv)
    (ss' : SpecState) (is' : ImplState)
    (hDataPath' : ss'.dataPathState = ss.dataPathState)
    (hInflight' : ss'.inflight = ss.inflight)
    (hRetire' : ss'.rc = ss.rc)
    (hImplDataPath : is'.dataPathState = is.dataPathState)
    (hImplInflight : is'.inflight = is.inflight)
    (hImplRegs : is'.registers = is.registers)
    (hImplSema : is'.semaphores = is.semaphores)
    (hControlEq : ∀ e', is'.controlState e' = ss'.controlState e')
    (hLoopRegInv : ∀ e' lid,
      (atLoopStart is' e' lid → is'.registers e' (ab.monotoneReg e' lid) + 1 = totalEntries ss' e' lid) ∧
      (¬ atLoopStart is' e' lid → is'.registers e' (ab.monotoneReg e' lid) = totalEntries ss' e' lid))
    (hTripRegInv : ∀ e' lid,
      ((∀ lid', ¬ atLoopStart is' e' lid') →
       is'.registers e' (ab.tripReg e' lid) = tripEntries ss' e' spec.body lid))
    (hPCCorr : ∀ e', PCCorr ab (ss'.pc e') (is'.pc e'))
    (hWaitNe : ∀ e', e' ≠ e → is'.pc e' = is.pc e')
    (hRegOp0 : ∀ e', e' = e → (is'.pc e').regOpIdx > 0 → False)
    (hRegOpFold : ∀ e' frame rest ops,
      (is'.pc e').stack = frame :: rest →
      frame.body[frame.stmtIdx]? = some (.regOp ops) →
      (∀ lid, foldRegOps ((ops e').drop (is'.pc e').stmtRegOpIdx) (is'.registers e') (ab.monotoneReg e' lid) = totalEntries ss' e' lid) ∧
      (∀ lid, foldRegOps ((ops e').drop (is'.pc e').stmtRegOpIdx) (is'.registers e') (ab.tripReg e' lid) = tripEntries ss' e' spec.body lid))
    : MatchStates spec impl ab SemaInv ss' is' where
  dataPathEq := by rw [hImplDataPath, hSim.dataPathEq, hDataPath']
  inflightEq := by intro e'; rw [hImplInflight, hSim.inflightEq, hInflight']
  controlEq := hControlEq
  semaInv := hSemaInvMono ss ss' is is' hRetire'.symm hImplSema.symm hSim.semaInv
  monotoneRegInv := fun e lid hNotALS => (hLoopRegInv e lid).2 hNotALS
  tripRegInv := hTripRegInv
  regOpFold := hRegOpFold
  pcCorr := hPCCorr
  waitRegChain := by
    intro e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
    by_cases he : e' = e
    · exact absurd hROI (hRegOp0 e' he)
    · rw [hWaitNe e' he] at hStack' hInstr' hROI ⊢
      rw [hImplRegs]
      exact hSim.waitRegChain e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
  gateRegChain := by
    intro e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
    by_cases he : e' = e
    · exact absurd hROI (hRegOp0 e' he)
    · rw [hWaitNe e' he] at hStack' hInstr' hROI ⊢
      rw [hImplRegs]
      exact hSim.gateRegChain e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI

-- CPDT-style: shared monotoneRegInv proof for loop-entry cases.
-- Used by loopEnter, condTrue, condFalse in both forward and backward sim.
theorem monotoneRegInv_loop_entry
    {spec : Program} {impl : ImplProgram} {ab : AllocBase spec impl}
    {SemaInv : SpecState → ImplState → Prop}
    {ss : SpecState} {is : ImplState} {e : EngineId}
    {sid : ScopeId}
    (hSim : MatchStates spec impl ab SemaInv ss is)
    (hOldNotALS : ∀ lid', ¬ atLoopStart is e lid')
    (hNewBody : List ImplStmt) (hNewKind : ImplFrameKind)
    (frame : ImplFrame) (rest : List ImplFrame)
    (hStack : (is.pc e).stack = frame :: rest)
    (hKindMatch : hNewKind = .loop sid ∨ hNewKind = .cond sid)
    (outerLoops : List ScopeId)
    : let is' := { is with
        pc := funUpdate is.pc e
          { stack := ⟨hNewBody, 0, hNewKind⟩ :: frame :: rest,
            instrIdx := 0, regOpIdx := 0, stmtRegOpIdx := 0 } }
      let ss' := { ss with scopeEntryHistory := incrScopeEntryHistory ss e sid outerLoops }
      ∀ e' lid',
      (¬ atLoopStart is' e' lid' →
       is.registers e' (ab.monotoneReg e' lid') = totalEntries ss' e' lid') := by
  dsimp only; intro e' lid'
  by_cases he : e' = e
  · -- e' = e: need to distinguish lid' = sid (vacuous) vs lid' ≠ sid
    subst he
    by_cases hEq : lid' = sid
    · -- lid' = sid: atLoopStart is' e sid is true, so premise is false
      subst hEq
      intro hContra
      exfalso; apply hContra
      simp only [atLoopStart, funUpdate, ite_true]
      rcases hKindMatch with hKM | hKM
      · exact ⟨_, _, rfl, Or.inl (by rw [hKM]), rfl⟩
      · exact ⟨_, _, rfl, Or.inr (by rw [hKM]), rfl⟩
    · -- lid' ≠ sid: use old monotoneRegInv
      simp only [totalEntries, incrScopeEntryHistory_ne_sid hEq]
      exact fun _ => hSim.monotoneRegInv e' lid' (hOldNotALS lid')
  · -- e' ≠ e: stack for e' is unchanged, translate atLoopStart condition
    intro hNALS
    have hOldNALS' : ¬ atLoopStart is e' lid' := by
      intro ⟨fr, r, hS, hK, hI⟩
      apply hNALS
      exact ⟨fr, r, by simp only [funUpdate, if_neg he]; exact hS, hK, hI⟩
    simp only [totalEntries, incrScopeEntryHistory_ne_engine he]
    exact hSim.monotoneRegInv e' lid' hOldNALS'

-- If target ∉ scopeIdsOf body, then scopeParent.go never finds it.
private def stmtListSize : List Stmt → Nat
  | [] => 0
  | .block _ :: rest => 1 + stmtListSize rest
  | .loop _ body :: rest => 1 + stmtListSize body + stmtListSize rest
  | .cond _ _ tb eb :: rest => 1 + stmtListSize tb + stmtListSize eb + stmtListSize rest

private theorem scopeParent_go_none_of_not_in (body : List Stmt) (target : ScopeId)
    (container : Option ScopeId) (hNotIn : target ∉ scopeIdsOf body)
    : scopeParent.go body target container = none := by
  match body with
  | [] => simp [scopeParent.go]
  | .block _ :: rest =>
    have : target ∉ scopeIdsOf rest := fun h => hNotIn (by simp [scopeIdsOf]; exact h)
    simp only [scopeParent.go]; exact scopeParent_go_none_of_not_in rest target container this
  | .loop lid lb :: rest =>
    have hNe : lid ≠ target := fun h =>
      hNotIn (by rw [scopeIdsOf]; exact List.mem_cons.mpr (Or.inl h.symm))
    have hNB : target ∉ scopeIdsOf lb := fun h =>
      hNotIn (by rw [scopeIdsOf]; exact List.mem_cons_of_mem _ (List.mem_append_left _ h))
    have hNR : target ∉ scopeIdsOf rest := fun h =>
      hNotIn (by rw [scopeIdsOf]; exact List.mem_cons_of_mem _ (List.mem_append_right _ h))
    simp only [scopeParent.go, hNe, ite_false]
    rw [scopeParent_go_none_of_not_in lb target (some lid) hNB]; simp
    exact scopeParent_go_none_of_not_in rest target container hNR
  | .cond thenId elseId tb eb :: rest =>
    have hNeT : thenId ≠ target := fun h =>
      hNotIn (by rw [scopeIdsOf]; exact List.mem_cons.mpr (Or.inl h.symm))
    have hNeE : elseId ≠ target := fun h =>
      hNotIn (by rw [scopeIdsOf]; exact List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl h.symm)))
    have hNTb : target ∉ scopeIdsOf tb := fun h =>
      hNotIn (by rw [scopeIdsOf]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ h))))
    have hNEb : target ∉ scopeIdsOf eb := fun h =>
      hNotIn (by rw [scopeIdsOf]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _ h))))
    have hNR : target ∉ scopeIdsOf rest := fun h =>
      hNotIn (by rw [scopeIdsOf]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ h)))
    simp only [scopeParent.go, hNeT, ite_false, hNeE]
    rw [scopeParent_go_none_of_not_in tb target (some thenId) hNTb]; simp
    rw [scopeParent_go_none_of_not_in eb target (some elseId) hNEb]; simp
    exact scopeParent_go_none_of_not_in rest target container hNR
termination_by stmtListSize body
decreasing_by all_goals simp +arith [stmtListSize]

-- A loop cannot be its own parent in a well-formed program with unique loop ids.
private theorem scopeParent_go_ne_self_aux (body : List Stmt) (sid : ScopeId)
    (container : Option ScopeId) (hUniq : UniqueScopeIds body) (hCont : container ≠ some sid)
    : scopeParent.go body sid container ≠ some sid := by
  match body with
  | [] => simp [scopeParent.go]
  | .block _ :: rest =>
    simp only [scopeParent.go]
    cases hUniq with | block _ _ hU => exact scopeParent_go_ne_self_aux rest sid container hU hCont
  | .loop lid lb :: rest =>
    cases hUniq with
    | loop _ _ _ hNotBody hNotRest hDisj hUBody hURest =>
      simp only [scopeParent.go]
      by_cases heq : lid = sid
      · subst heq; simp; exact hCont
      · simp [heq]
        have hContLid : (some lid : Option ScopeId) ≠ some sid := by simp [heq]
        have ih_lb := scopeParent_go_ne_self_aux lb sid (some lid) hUBody hContLid
        cases hgo : scopeParent.go lb sid (some lid) with
        | none => simp; exact scopeParent_go_ne_self_aux rest sid container hURest hCont
        | some p => simp; intro h; subst h; exact ih_lb hgo
  | .cond thenId elseId tb eb :: rest =>
    cases hUniq with
    | cond _ _ _ _ _ hNe hTnTb hTnEb hTnR hEnTb hEnEb hEnR hTbDisj hEbDisj hUTb hUEb hUR =>
      simp only [scopeParent.go]
      by_cases htid : thenId = sid
      · subst htid; simp; exact hCont
      · simp [htid]
        by_cases heid : elseId = sid
        · subst heid; simp; exact hCont
        · simp [heid]
          have hContT : (some thenId : Option ScopeId) ≠ some sid := by simp [htid]
          have hContE : (some elseId : Option ScopeId) ≠ some sid := by simp [heid]
          have ih_tb := scopeParent_go_ne_self_aux tb sid (some thenId) hUTb hContT
          cases hgoTb : scopeParent.go tb sid (some thenId) with
          | none =>
            simp
            have ih_eb := scopeParent_go_ne_self_aux eb sid (some elseId) hUEb hContE
            cases hgoEb : scopeParent.go eb sid (some elseId) with
            | none => simp; exact scopeParent_go_ne_self_aux rest sid container hUR hCont
            | some p => simp; intro h; subst h; exact ih_eb hgoEb
          | some p => simp; intro h; subst h; exact ih_tb hgoTb
termination_by stmtListSize body
decreasing_by all_goals simp +arith [stmtListSize]

-- tripEntries increments by 1 when entering a loop, given parent ∈ outerLoops.
theorem tripEntries_incr_self
    {spec : Program} {ss : SpecState} {e : EngineId} {sid : ScopeId} {outerLoops : List ScopeId}
    (hParent : ∀ parent, scopeParent spec.body sid = some parent → parent ∈ outerLoops)
    (hNotSelfParent : ∀ parent, scopeParent spec.body sid = some parent → parent ≠ sid)
    : tripEntries { ss with scopeEntryHistory := incrScopeEntryHistory ss e sid outerLoops } e spec.body sid =
      tripEntries ss e spec.body sid + 1 := by
  unfold tripEntries
  cases hPar : scopeParent spec.body sid with
  | none =>
    simp only [totalEntries, incrScopeEntryHistory_totalEntries]
  | some parent =>
    show incrScopeEntryHistory ss e sid outerLoops e sid (some parent)
          (incrScopeEntryHistory ss e sid outerLoops e parent none 1) =
        ss.scopeEntryHistory e sid (some parent) (ss.scopeEntryHistory e parent none 1) + 1
    have hMem := hParent parent hPar
    have hNe := hNotSelfParent parent hPar
    -- totalEntries(parent) unchanged: incrScopeEntryHistory only modifies H for innerLoop=sid, parent ≠ sid
    rw [incrScopeEntryHistory_ne_sid hNe]
    -- Now goal: incrScopeEntryHistory ... e sid (some parent) (ss.scopeEntryHistory e parent none 1)
    --         = ss.scopeEntryHistory e sid (some parent) (ss.scopeEntryHistory e parent none 1) + 1
    simp only [incrScopeEntryHistory]
    -- The if-condition holds because parent ∈ outerLoops
    simp only [true_and, ite_true]
    -- Now need: inner if-condition is true
    simp [show some parent ≠ none from by simp, show some parent ≠ some sid from by simp [hNe]]
    exact ⟨parent, hMem, rfl, by simp [totalEntries]⟩

-- tripEntries for a child of sid is 0 after sid enters (fresh H slot).
-- When scopeParent body lid' = some sid, new tripEntries reads
-- H(e, lid', some sid, new_totalEntries(sid)) where new_totalEntries = old + 1.
-- Since incrScopeEntryHistory only writes H for innerLoop=sid (not lid'),
-- this reads the OLD H at a NEW index (old_TE + 1), which was never written = 0.
theorem tripEntries_child_reset
    {spec : Program} {ss : SpecState} {e : EngineId} {sid lid' : ScopeId}
    {outerLoops : List ScopeId}
    (hSpecInv : SpecInv spec ss)
    (hNeLid : lid' ≠ sid)
    (hChildOf : scopeParent spec.body lid' = some sid)
    : tripEntries { ss with scopeEntryHistory := incrScopeEntryHistory ss e sid outerLoops } e spec.body lid' = 0 := by
  unfold tripEntries
  show (match scopeParent spec.body lid' with
    | some parent => incrScopeEntryHistory ss e sid outerLoops e lid' (some parent)
        (incrScopeEntryHistory ss e sid outerLoops e parent none 1)
    | none => incrScopeEntryHistory ss e sid outerLoops e lid' none 1) = 0
  rw [hChildOf]
  simp only []
  -- lid' ≠ sid → incrScopeEntryHistory doesn't change H for lid'
  rw [incrScopeEntryHistory_ne_sid hNeLid]
  -- totalEntries(sid) in new state = old + 1
  simp only [incrScopeEntryHistory_totalEntries]
  exact hSpecInv.zeroFuture e lid' (some sid) (ss.scopeEntryHistory e sid none 1 + 1) (by
    simp only [totalEntriesOpt, totalEntries]; omega)

-- tripEntries is unchanged for loops that are neither sid nor a child of sid
theorem tripEntries_preserved_non_child
    {spec : Program} {ss : SpecState} {e : EngineId} {sid lid' : ScopeId}
    {outerLoops : List ScopeId}
    (hNe : lid' ≠ sid)
    (hNotChild : scopeParent spec.body lid' ≠ some sid)
    : tripEntries { ss with scopeEntryHistory := incrScopeEntryHistory ss e sid outerLoops } e spec.body lid' =
      tripEntries ss e spec.body lid' := by
  simp only [tripEntries]
  cases hPar : scopeParent spec.body lid' with
  | none => simp only [totalEntries, incrScopeEntryHistory_ne_sid hNe]
  | some parent =>
    simp only []
    have hParNe : parent ≠ sid := by intro h; exact hNotChild (h ▸ hPar)
    rw [incrScopeEntryHistory_ne_sid hNe,
      show totalEntries { ss with scopeEntryHistory := incrScopeEntryHistory ss e sid outerLoops } e parent =
        totalEntries ss e parent from by simp [totalEntries, incrScopeEntryHistory_ne_sid hParNe]]

-- ---- Infrastructure for tripReg fold at loop entry ----

-- Helper: result of scopeParent.go is either the container or in scopeIdsOf body.
private theorem scopeParent_go_result_mem_or_eq
    (body : List Stmt) (target : ScopeId) (c : Option ScopeId) (s : ScopeId)
    (hGo : scopeParent.go body target c = some s)
    : c = some s ∨ s ∈ scopeIdsOf body := by
  match body with
  | [] => simp [scopeParent.go] at hGo
  | .block _ :: rest =>
    simp [scopeParent.go] at hGo
    rcases scopeParent_go_result_mem_or_eq rest target c s hGo with h | h
    · exact Or.inl h
    · exact Or.inr (by simp [scopeIdsOf]; exact h)
  | .loop lid lb :: rest =>
    simp only [scopeParent.go] at hGo
    by_cases hEq : lid = target
    · subst hEq; simp at hGo; exact Or.inl hGo
    · simp only [hEq, ite_false] at hGo
      match hInner : scopeParent.go lb target (some lid) with
      | some p =>
        rw [hInner] at hGo; simp at hGo; subst hGo
        rcases scopeParent_go_result_mem_or_eq lb target (some lid) p hInner with h | h
        · simp at h; exact Or.inr (by simp [scopeIdsOf]; exact Or.inl h.symm)
        · exact Or.inr (by simp [scopeIdsOf]; right; exact Or.inl h)
      | none =>
        rw [hInner] at hGo; simp at hGo
        rcases scopeParent_go_result_mem_or_eq rest target c s hGo with h | h
        · exact Or.inl h
        · exact Or.inr (by simp [scopeIdsOf]; right; right; exact h)
  | .cond tid eid tb eb :: rest =>
    simp only [scopeParent.go] at hGo
    by_cases htid : tid = target
    · subst htid; simp at hGo; exact Or.inl hGo
    · by_cases heid : eid = target
      · subst heid; simp [htid] at hGo; exact Or.inl hGo
      · simp only [htid, heid, ite_false] at hGo
        match hTb : scopeParent.go tb target (some tid) with
        | some p =>
          rw [hTb] at hGo; simp at hGo; subst hGo
          rcases scopeParent_go_result_mem_or_eq tb target (some tid) p hTb with h | h
          · simp at h; exact Or.inr (by simp [scopeIdsOf]; exact Or.inl h.symm)
          · exact Or.inr (by simp [scopeIdsOf]; right; right; exact Or.inl h)
        | none =>
          rw [hTb] at hGo; simp at hGo
          match hEb : scopeParent.go eb target (some eid) with
          | some p =>
            rw [hEb] at hGo; simp at hGo; subst hGo
            rcases scopeParent_go_result_mem_or_eq eb target (some eid) p hEb with h | h
            · simp at h; exact Or.inr (by simp [scopeIdsOf]; right; exact Or.inl h.symm)
            · exact Or.inr (by simp [scopeIdsOf]; right; right; right; exact Or.inl h)
          | none =>
            rw [hEb] at hGo; simp at hGo
            rcases scopeParent_go_result_mem_or_eq rest target c s hGo with h | h
            · exact Or.inl h
            · exact Or.inr (by simp [scopeIdsOf]; right; right; right; right; exact h)
termination_by sizeOf body

-- Converse direction: go body lid (some c) = some c → lid ∈ directChildScopes body.
private theorem go_container_implies_directChild
    (body : List Stmt) (lid c : ScopeId)
    (hGo : scopeParent.go body lid (some c) = some c)
    (hUniq : UniqueScopeIds body) (hNotIn : c ∉ scopeIdsOf body)
    : lid ∈ directChildScopes body := by
  match body with
  | [] => simp [scopeParent.go] at hGo
  | .block _ :: rest =>
    have hUR : UniqueScopeIds rest := by cases hUniq with | block _ _ h => exact h
    simp [scopeParent.go] at hGo; simp [directChildScopes]
    exact go_container_implies_directChild rest lid c hGo hUR (by simp [scopeIdsOf] at hNotIn; exact hNotIn)
  | .loop lid' lb :: rest =>
    have hUR : UniqueScopeIds rest := by cases hUniq with | loop _ _ _ _ _ _ _ h => exact h
    have hCNeLid' : c ≠ lid' := fun h => hNotIn (by simp [scopeIdsOf]; exact Or.inl h)
    have hCNotLb : c ∉ scopeIdsOf lb := fun h => hNotIn (by simp [scopeIdsOf]; right; exact Or.inl h)
    have hCNotRest : c ∉ scopeIdsOf rest := fun h => hNotIn (by simp [scopeIdsOf]; right; right; exact h)
    simp only [scopeParent.go] at hGo; simp only [directChildScopes, List.mem_cons]
    by_cases hEq : lid' = lid
    · exact Or.inl hEq.symm
    · simp only [hEq, ite_false] at hGo; right
      cases hInner : scopeParent.go lb lid (some lid') with
      | some p =>
        rw [hInner] at hGo; simp only [Option.some.injEq] at hGo
        rcases scopeParent_go_result_mem_or_eq lb lid (some lid') p hInner with h | h
        · simp at h; exact absurd (hGo ▸ h.symm) hCNeLid'
        · exact absurd (hGo ▸ h) hCNotLb
      | none => rw [hInner] at hGo; exact go_container_implies_directChild rest lid c hGo hUR hCNotRest
  | .cond tid eid tb eb :: rest =>
    have hUR : UniqueScopeIds rest := by cases hUniq with | cond _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => exact h
    have hCNeTid : c ≠ tid := fun h => hNotIn (by simp [scopeIdsOf]; exact Or.inl h)
    have hCNeEid : c ≠ eid := fun h => hNotIn (by simp [scopeIdsOf]; right; exact Or.inl h)
    have hCNotTb : c ∉ scopeIdsOf tb := fun h => hNotIn (by simp [scopeIdsOf]; right; right; exact Or.inl h)
    have hCNotEb : c ∉ scopeIdsOf eb :=
      fun h => hNotIn (by simp [scopeIdsOf]; right; right; right; exact Or.inl h)
    have hCNotRest : c ∉ scopeIdsOf rest :=
      fun h => hNotIn (by simp [scopeIdsOf]; right; right; right; right; exact h)
    simp only [scopeParent.go] at hGo; simp only [directChildScopes, List.mem_cons]
    by_cases htid : tid = lid
    · exact Or.inl htid.symm
    · by_cases heid : eid = lid
      · exact Or.inr (Or.inl heid.symm)
      · simp only [htid, heid, ite_false] at hGo; right; right
        cases hTb : scopeParent.go tb lid (some tid) with
        | some p =>
          rw [hTb] at hGo; simp only [Option.some.injEq] at hGo
          rcases scopeParent_go_result_mem_or_eq tb lid (some tid) p hTb with h | h
          · simp at h; exact absurd (hGo ▸ h.symm) hCNeTid
          · exact absurd (hGo ▸ h) hCNotTb
        | none =>
          rw [hTb] at hGo
          cases hEb : scopeParent.go eb lid (some eid) with
          | some p =>
            rw [hEb] at hGo; simp only [Option.some.injEq] at hGo
            rcases scopeParent_go_result_mem_or_eq eb lid (some eid) p hEb with h | h
            · simp at h; exact absurd (hGo ▸ h.symm) hCNeEid
            · exact absurd (hGo ▸ h) hCNotEb
          | none => rw [hEb] at hGo; exact go_container_implies_directChild rest lid c hGo hUR hCNotRest
termination_by sizeOf body

-- Peeling lemma: skip a statement whose scopeIdsOf doesn't contain sid.
private theorem go_skip_stmt {stmt : Stmt} {rest : List Stmt} {lid sid : ScopeId}
    (hGo : scopeParent.go (stmt :: rest) lid none = some sid)
    (hNotInStmt : sid ∉ scopeIdsOf [stmt])
    : scopeParent.go rest lid none = some sid := by
  cases stmt with
  | block _ => simp [scopeParent.go] at hGo; exact hGo
  | loop lid' lb' =>
    simp only [scopeParent.go] at hGo
    by_cases hEq : lid' = lid
    · subst hEq; simp at hGo
    · simp only [hEq, ite_false] at hGo
      cases hInner : scopeParent.go lb' lid (some lid') with
      | some p =>
        rw [hInner] at hGo; simp only [Option.some.injEq] at hGo
        rcases scopeParent_go_result_mem_or_eq lb' lid (some lid') p hInner with h | h
        · simp at h; rw [← hGo, ← h] at hNotInStmt
          exact absurd (by simp [scopeIdsOf] : lid' ∈ scopeIdsOf [Stmt.loop lid' lb']) hNotInStmt
        · rw [← hGo] at hNotInStmt
          exact absurd (by simp [scopeIdsOf]; right; exact h : p ∈ scopeIdsOf [Stmt.loop lid' lb']) hNotInStmt
      | none => rw [hInner] at hGo; exact hGo
  | cond tid eid tb eb =>
    simp only [scopeParent.go] at hGo
    by_cases htid : tid = lid
    · subst htid; simp at hGo
    · by_cases heid : eid = lid
      · subst heid; simp [htid] at hGo
      · simp only [htid, heid, ite_false] at hGo
        cases hTb : scopeParent.go tb lid (some tid) with
        | some p =>
          rw [hTb] at hGo; simp only [Option.some.injEq] at hGo
          rcases scopeParent_go_result_mem_or_eq tb lid (some tid) p hTb with h | h
          · simp at h; rw [← hGo, ← h] at hNotInStmt
            exact absurd (by simp [scopeIdsOf] : tid ∈ scopeIdsOf [Stmt.cond tid eid tb eb]) hNotInStmt
          · rw [← hGo] at hNotInStmt
            exact absurd (by simp [scopeIdsOf]; right; right; left; exact h :
              p ∈ scopeIdsOf [Stmt.cond tid eid tb eb]) hNotInStmt
        | none =>
          rw [hTb] at hGo
          cases hEb : scopeParent.go eb lid (some eid) with
          | some p =>
            rw [hEb] at hGo; simp only [Option.some.injEq] at hGo
            rcases scopeParent_go_result_mem_or_eq eb lid (some eid) p hEb with h | h
            · simp at h; rw [← hGo, ← h] at hNotInStmt
              exact absurd (by simp [scopeIdsOf] : eid ∈ scopeIdsOf [Stmt.cond tid eid tb eb]) hNotInStmt
            · rw [← hGo] at hNotInStmt
              exact absurd (by simp [scopeIdsOf]; right; right; right; exact h :
                p ∈ scopeIdsOf [Stmt.cond tid eid tb eb]) hNotInStmt
          | none => rw [hEb] at hGo; exact hGo

private theorem sid_not_in_first_stmt_scopeIdsOf {stmt : Stmt} {rest : List Stmt} {sid : ScopeId}
    (hUniq : UniqueScopeIds (stmt :: rest)) (hSidInRest : sid ∈ scopeIdsOf rest)
    : sid ∉ scopeIdsOf [stmt] := by
  intro hMem; cases hUniq with
  | block _ _ _ => simp [scopeIdsOf] at hMem
  | loop lid lb rest hNotBody hNotRest hDisj hUBody hURest =>
    simp [scopeIdsOf] at hMem; rcases hMem with rfl | hMem
    · exact hNotRest hSidInRest
    · exact hDisj sid hMem hSidInRest
  | cond tid eid tb eb rest hNe hTnTb hTnEb hTnR hEnTb hEnEb hEnR hTbDisj hEbDisj hUTb hUEb hURest =>
    simp [scopeIdsOf] at hMem; rcases hMem with rfl | rfl | hMem | hMem
    · exact hTnR hSidInRest
    · exact hEnR hSidInRest
    · exact (hTbDisj sid hMem).2 hSidInRest
    · exact hEbDisj sid hMem hSidInRest

private theorem uniqueScopeIds_rest' {stmt : Stmt} {rest : List Stmt}
    (hUniq : UniqueScopeIds (stmt :: rest)) : UniqueScopeIds rest := by
  cases hUniq with
  | block _ _ h => exact h | loop _ _ _ _ _ _ _ h => exact h
  | cond _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => exact h

-- Converse of scopeParent_of_directChild_loop.
theorem directChild_of_scopeParent_loop {body : List Stmt} {idx : Nat}
    {sid : ScopeId} {loopBody : List Stmt} {lid : ScopeId}
    (hIdx : body[idx]? = some (Stmt.loop sid loopBody))
    (hParent : scopeParent body lid = some sid)
    (hUniq : UniqueScopeIds body) (hNe : lid ≠ sid)
    : lid ∈ directChildScopes loopBody := by
  have hUniqSingle := uniqueScopeIds_of_getElem hIdx hUniq
  have hSidNotInLb : sid ∉ scopeIdsOf loopBody := by
    cases hUniqSingle with | loop _ _ _ h _ _ _ _ => exact h
  have hUniqLb : UniqueScopeIds loopBody := by
    cases hUniqSingle with | loop _ _ _ _ _ _ h _ => exact h
  suffices h : scopeParent.go loopBody lid (some sid) = some sid from
    go_container_implies_directChild loopBody lid sid h hUniqLb hSidNotInLb
  unfold scopeParent at hParent
  induction idx generalizing body with
  | zero =>
    match body, hIdx with
    | _ :: rest, hIdx =>
      simp at hIdx; obtain ⟨rfl, rfl⟩ := hIdx
      simp only [scopeParent.go, show sid ≠ lid from (Ne.symm hNe), ite_false] at hParent
      cases hInner : scopeParent.go loopBody lid (some sid) with
      | some p => rw [hInner] at hParent; simp at hParent; rw [hParent]
      | none =>
        rw [hInner] at hParent
        have hNotRest : sid ∉ scopeIdsOf rest := by
          cases hUniq with | loop _ _ _ _ h _ _ _ => exact h
        rcases scopeParent_go_result_mem_or_eq rest lid none sid hParent with h | h
        · simp at h
        · exact absurd h hNotRest
  | succ n ih =>
    match body, hIdx, hUniq with
    | _ :: rest, hIdx, hUniq =>
      simp at hIdx
      have hSidInRest : sid ∈ scopeIdsOf rest := mem_scopeIdsOf_of_getElem hIdx (by simp [scopeIdsOf])
      exact ih hIdx (go_skip_stmt hParent (sid_not_in_first_stmt_scopeIdsOf hUniq hSidInRest))
        (uniqueScopeIds_rest' hUniq)

-- If scopeParent body lid = some sid and scopeBodyOf body sid = some sb,
-- then lid is a direct child of sb.
-- This is the "global" converse of directChild_of_scopeParent_loop:
-- it works via scopeBodyOf instead of requiring an explicit getElem index.
-- The proof is by induction on stmtListSize, tracking scopeParent.go and scopeBodyOf.
private theorem directChild_of_scopeParent_go_scopeBodyOf
    (body : List Stmt) (lid sid : ScopeId) (sb : List Stmt) (container : Option ScopeId)
    (hGo : scopeParent.go body lid container = some sid)
    (hSB : scopeBodyOf body sid = some sb)
    (hUniq : UniqueScopeIds body) (hNe : lid ≠ sid)
    (hContNeSid : container ≠ some sid)
    : lid ∈ directChildScopes sb := by
  match body with
  | [] => simp [scopeParent.go] at hGo
  | .block _ :: rest =>
    simp [scopeParent.go] at hGo; simp [scopeBodyOf] at hSB
    exact directChild_of_scopeParent_go_scopeBodyOf rest lid sid sb container hGo hSB
      (by cases hUniq with | block _ _ h => exact h) hNe hContNeSid
  | .loop lid' lb :: rest =>
    simp only [scopeParent.go] at hGo; simp only [scopeBodyOf] at hSB
    by_cases hLidEq : lid' = lid
    · subst hLidEq; simp at hGo; exact absurd hGo hContNeSid
    · simp only [hLidEq, ite_false] at hGo
      -- Extract UniqueScopeIds facts before any subst on sid
      have hUniqLb : UniqueScopeIds lb := by cases hUniq with | loop _ _ _ _ _ _ h _ => exact h
      have hUniqRest : UniqueScopeIds rest := by cases hUniq with | loop _ _ _ _ _ _ _ h => exact h
      have hLidNotInLb : lid' ∉ scopeIdsOf lb := by cases hUniq with | loop _ _ _ h _ _ _ _ => exact h
      have hLidNotInRest : lid' ∉ scopeIdsOf rest := by cases hUniq with | loop _ _ _ _ h _ _ _ => exact h
      have hLbRestDisj : ∀ x, x ∈ scopeIdsOf lb → x ∉ scopeIdsOf rest := by
        cases hUniq with | loop _ _ _ _ _ h _ _ => exact fun x hx hR => h x hx hR
      by_cases hSidEq : lid' = sid
      · -- lid' = sid: scopeBodyOf returns lb (= sb after simp)
        rw [hSidEq] at hSB hGo hLidNotInLb hLidNotInRest
        simp at hSB; rw [← hSB]
        cases hInner : scopeParent.go lb lid (some sid) with
        | some p =>
          rw [hInner] at hGo; simp at hGo
          rw [hGo] at hInner
          exact go_container_implies_directChild lb lid sid hInner hUniqLb hLidNotInLb
        | none =>
          rw [hInner] at hGo
          rcases scopeParent_go_result_mem_or_eq rest lid container sid hGo with h | h
          · exact absurd h hContNeSid
          · exact absurd h hLidNotInRest
      · -- lid' ≠ sid: scopeBodyOf orElse chain
        simp only [hSidEq, ite_false] at hSB
        cases hInner : scopeParent.go lb lid (some lid') with
        | some p =>
          rw [hInner] at hGo; simp at hGo
          -- hGo : p = sid. Rewrite hInner to use sid instead of p.
          rw [hGo] at hInner
          rcases scopeParent_go_result_mem_or_eq lb lid (some lid') sid hInner with h | h
          · simp at h; exact absurd h hSidEq
          · have hSidNotInRest : sid ∉ scopeIdsOf rest := hLbRestDisj sid h
            have hSB' : scopeBodyOf lb sid = some sb := by
              rw [scopeBodyOf_none_of_not_mem hSidNotInRest] at hSB; simpa using hSB
            exact directChild_of_scopeParent_go_scopeBodyOf lb lid sid sb (some lid') hInner hSB'
              hUniqLb hNe (by simp [hSidEq])
        | none =>
          rw [hInner] at hGo
          cases hLbSB : scopeBodyOf lb sid with
          | some sb' =>
            have hSidInLb := scopeBodyOf_mem_scopeIdsOf hLbSB
            have hSidNotInRest : sid ∉ scopeIdsOf rest := hLbRestDisj sid hSidInLb
            rcases scopeParent_go_result_mem_or_eq rest lid container sid hGo with h | h
            · exact absurd h hContNeSid
            · exact absurd h hSidNotInRest
          | none =>
            simp [hLbSB, Option.orElse] at hSB
            exact directChild_of_scopeParent_go_scopeBodyOf rest lid sid sb container hGo hSB
              hUniqRest hNe hContNeSid
  | .cond tid eid tb eb :: rest =>
    simp only [scopeParent.go] at hGo; simp only [scopeBodyOf] at hSB
    by_cases hTid : tid = lid
    · subst hTid; simp at hGo; exact absurd hGo hContNeSid
    · by_cases hEid : eid = lid
      · subst hEid; simp [hTid] at hGo; exact absurd hGo hContNeSid
      · simp only [hTid, hEid, ite_false] at hGo
        -- Extract all UniqueScopeIds facts before case splits on sid
        have hTidNeEid : tid ≠ eid := by cases hUniq with | cond _ _ _ _ _ hNe' => exact hNe'
        have hTidNotInTb : tid ∉ scopeIdsOf tb := by cases hUniq with | cond _ _ _ _ _ _ h => exact h
        have hTidNotInEb : tid ∉ scopeIdsOf eb := by cases hUniq with | cond _ _ _ _ _ _ _ h => exact h
        have hTidNotInRest : tid ∉ scopeIdsOf rest := by cases hUniq with | cond _ _ _ _ _ _ _ _ h => exact h
        have hEidNotInTb : eid ∉ scopeIdsOf tb := by cases hUniq with | cond _ _ _ _ _ _ _ _ _ h => exact h
        have hEidNotInEb : eid ∉ scopeIdsOf eb := by cases hUniq with | cond _ _ _ _ _ _ _ _ _ _ h => exact h
        have hEidNotInRest : eid ∉ scopeIdsOf rest := by cases hUniq with | cond _ _ _ _ _ _ _ _ _ _ _ h => exact h
        have hTbDisj : ∀ x, x ∈ scopeIdsOf tb → x ∉ scopeIdsOf eb ∧ x ∉ scopeIdsOf rest := by
          cases hUniq with | cond _ _ _ _ _ _ _ _ _ _ _ _ h => exact h
        have hEbDisj : ∀ x, x ∈ scopeIdsOf eb → x ∉ scopeIdsOf rest := by
          cases hUniq with | cond _ _ _ _ _ _ _ _ _ _ _ _ _ h _ _ _ => exact h
        have hUniqTb : UniqueScopeIds tb := by cases hUniq with | cond _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => exact h
        have hUniqEb : UniqueScopeIds eb := by cases hUniq with | cond _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => exact h
        have hUniqRest : UniqueScopeIds rest := by cases hUniq with | cond _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => exact h
        by_cases hTidSid : tid = sid
        · -- tid = sid: scopeBodyOf returns tb (= sb)
          rw [hTidSid] at hSB hGo hTidNotInTb hTidNotInEb hTidNotInRest hTidNeEid
          simp at hSB; rw [← hSB]
          cases hTbGo : scopeParent.go tb lid (some sid) with
          | some p =>
            rw [hTbGo] at hGo; simp at hGo; rw [hGo] at hTbGo
            exact go_container_implies_directChild tb lid sid hTbGo hUniqTb hTidNotInTb
          | none =>
            rw [hTbGo] at hGo
            cases hEbGo : scopeParent.go eb lid (some eid) with
            | some p =>
              rw [hEbGo] at hGo; simp at hGo; rw [hGo] at hEbGo
              rcases scopeParent_go_result_mem_or_eq eb lid (some eid) sid hEbGo with h | h
              · simp at h; exact absurd h.symm hTidNeEid
              · exact absurd h hTidNotInEb
            | none =>
              rw [hEbGo] at hGo
              rcases scopeParent_go_result_mem_or_eq rest lid container sid hGo with h | h
              · exact absurd h hContNeSid
              · exact absurd h hTidNotInRest
        · by_cases hEidSid : eid = sid
          · -- eid = sid: scopeBodyOf returns eb (= sb)
            rw [hEidSid] at hSB hGo hEidNotInTb hEidNotInEb hEidNotInRest
            simp [hTidSid] at hSB; rw [← hSB]
            cases hTbGo : scopeParent.go tb lid (some tid) with
            | some p =>
              rw [hTbGo] at hGo; simp at hGo; rw [hGo] at hTbGo
              rcases scopeParent_go_result_mem_or_eq tb lid (some tid) sid hTbGo with h | h
              · simp at h; exact absurd h hTidSid
              · exact absurd h hEidNotInTb
            | none =>
              rw [hTbGo] at hGo
              cases hEbGo : scopeParent.go eb lid (some sid) with
              | some p =>
                rw [hEbGo] at hGo; simp at hGo; rw [hGo] at hEbGo
                exact go_container_implies_directChild eb lid sid hEbGo hUniqEb hEidNotInEb
              | none =>
                rw [hEbGo] at hGo
                rcases scopeParent_go_result_mem_or_eq rest lid container sid hGo with h | h
                · exact absurd h hContNeSid
                · exact absurd h hEidNotInRest
          · -- Neither tid nor eid equals sid
            simp only [hTidSid, hEidSid, ite_false] at hSB
            cases hTbGo : scopeParent.go tb lid (some tid) with
            | some p =>
              rw [hTbGo] at hGo; simp at hGo; rw [hGo] at hTbGo
              rcases scopeParent_go_result_mem_or_eq tb lid (some tid) sid hTbGo with h | h
              · simp at h; exact absurd h hTidSid
              · have hSidNotInEb : sid ∉ scopeIdsOf eb := (hTbDisj sid h).1
                have hSidNotInRest : sid ∉ scopeIdsOf rest := (hTbDisj sid h).2
                have hSB' : scopeBodyOf tb sid = some sb := by
                  simp [scopeBodyOf_none_of_not_mem hSidNotInEb, scopeBodyOf_none_of_not_mem hSidNotInRest] at hSB
                  simpa using hSB
                exact directChild_of_scopeParent_go_scopeBodyOf tb lid sid sb (some tid) hTbGo hSB'
                  hUniqTb hNe (by simp [hTidSid])
            | none =>
              rw [hTbGo] at hGo
              cases hEbGo : scopeParent.go eb lid (some eid) with
              | some p =>
                rw [hEbGo] at hGo; simp at hGo; rw [hGo] at hEbGo
                rcases scopeParent_go_result_mem_or_eq eb lid (some eid) sid hEbGo with h | h
                · simp at h; exact absurd h hEidSid
                · have hSidNotInTb : sid ∉ scopeIdsOf tb := fun hT => (hTbDisj sid hT).1 h |>.elim
                  have hSidNotInRest : sid ∉ scopeIdsOf rest := hEbDisj sid h
                  have hSB' : scopeBodyOf eb sid = some sb := by
                    simp [scopeBodyOf_none_of_not_mem hSidNotInTb, scopeBodyOf_none_of_not_mem hSidNotInRest] at hSB
                    simpa using hSB
                  exact directChild_of_scopeParent_go_scopeBodyOf eb lid sid sb (some eid) hEbGo hSB'
                    hUniqEb hNe (by simp [hEidSid])
              | none =>
                rw [hEbGo] at hGo
                cases hTbSB : scopeBodyOf tb sid with
                | some sb' =>
                  have hSidInTb := scopeBodyOf_mem_scopeIdsOf hTbSB
                  have hSidNotInRest : sid ∉ scopeIdsOf rest := (hTbDisj sid hSidInTb).2
                  rcases scopeParent_go_result_mem_or_eq rest lid container sid hGo with h | h
                  · exact absurd h hContNeSid
                  · exact absurd h hSidNotInRest
                | none =>
                  simp [hTbSB, Option.orElse] at hSB
                  cases hEbSB : scopeBodyOf eb sid with
                  | some sb' =>
                    have hSidInEb := scopeBodyOf_mem_scopeIdsOf hEbSB
                    have hSidNotInRest : sid ∉ scopeIdsOf rest := hEbDisj sid hSidInEb
                    rcases scopeParent_go_result_mem_or_eq rest lid container sid hGo with h | h
                    · exact absurd h hContNeSid
                    · exact absurd h hSidNotInRest
                  | none =>
                    simp [hEbSB] at hSB
                    exact directChild_of_scopeParent_go_scopeBodyOf rest lid sid sb container hGo hSB
                      hUniqRest hNe hContNeSid
termination_by stmtListSize body
decreasing_by all_goals simp +arith [stmtListSize]

theorem directChild_of_scopeParent_scopeBodyOf
    {body : List Stmt} {lid sid : ScopeId} {sb : List Stmt}
    (hP : scopeParent body lid = some sid)
    (hSB : scopeBodyOf body sid = some sb)
    (hUniq : UniqueScopeIds body) (hNe : lid ≠ sid)
    : lid ∈ directChildScopes sb :=
  directChild_of_scopeParent_go_scopeBodyOf body lid sid sb none
    (by unfold scopeParent at hP; exact hP) hSB hUniq hNe (by simp)

theorem foldRegOps_childResets
    {ab : AllocBase spec impl} {f : RegId → Nat}
    {e : EngineId} {lid' : ScopeId}
    (hInj : ∀ l1 l2, ab.tripReg e l1 = ab.tripReg e l2 → l1 = l2)
    (children : List ScopeId)
    : foldRegOps (children.map (fun child =>
        (ab.tripReg e child, ab.tripReg e child, RegOpKind.const 0))) f
          (ab.tripReg e lid') =
      if lid' ∈ children then 0
      else f (ab.tripReg e lid') := by
  induction children generalizing f with
  | nil => simp [foldRegOps]
  | cons child rest ih =>
    simp only [List.map_cons, foldRegOps, applyRegOpKind, List.mem_cons]
    by_cases hLC : lid' = child
    · subst hLC
      simp only [ite_true, true_or]
      rw [ih]; split <;> [rfl; simp [funUpdate]]
    · have hRegNe : ab.tripReg e lid' ≠ ab.tripReg e child :=
        fun h => hLC (hInj _ _ h)
      simp only [hLC, false_or]
      rw [ih]; congr 1; simp [funUpdate, hRegNe]

-- After executing scopeEntryOps, tripReg e lid' has the right value:
-- - lid' = sid: old_value + 1
-- - lid' is a child of sid (in directChildScopes): 0
-- - otherwise: unchanged
-- This is a computation on foldRegOps of the concrete ops list, and it closes the
-- loop-entry tripRegInv.
-- The proof reasons about foldRegOps on the specific scopeEntryOps list
-- with non-clobbering between monotoneReg, tripReg, and their indexed variants.
theorem foldRegOps_scopeEntryOps_tripReg
    {ab : AllocBase spec impl} {regs : RegId → Nat} {loopBody : List Stmt}
    {e : EngineId} {sid lid' : ScopeId}
    (hInj : ∀ l1 l2, ab.tripReg e l1 = ab.tripReg e l2 → l1 = l2)
    (hNoClobSR : ∀ l1 l2, ab.monotoneReg e l1 ≠ ab.tripReg e l2)
    (hSidNotChild : sid ∉ directChildScopes loopBody)
    : foldRegOps (scopeEntryOps ab.monotoneReg ab.tripReg loopBody e sid) regs (ab.tripReg e lid') =
      if lid' = sid then regs (ab.tripReg e sid) + 1
      else if lid' ∈ directChildScopes loopBody then 0
      else regs (ab.tripReg e lid') := by
  unfold scopeEntryOps
  rw [foldRegOps_append]
  simp only [foldRegOps, applyRegOpKind]
  rw [foldRegOps_childResets hInj]
  simp only [funUpdate]
  by_cases hLid : lid' = sid
  · subst hLid
    simp [Ne.symm (hNoClobSR lid' lid'), hSidNotChild]
  · have hRegNe : ab.tripReg e lid' ≠ ab.tripReg e sid :=
      fun h => hLid (hInj _ _ h)
    simp [hRegNe, hLid, Ne.symm (hNoClobSR sid lid')]

-- regOpFold tripReg at loop entry: ties foldRegOps of scopeEntryOps to tripEntries.
-- Used in both backward and forward sim loop-enter proofs (loop, condTrue, condFalse).
-- Takes the forward direction (directChild → scopeParent) as a parameter, since the proof
-- differs between loop/condTrue/condFalse contexts.
theorem regOpFold_tripReg_loop_entry
    {spec : Program} {impl : ImplProgram} {ab : AllocBase spec impl}
    {SemaInv : SpecState → ImplState → Prop}
    {ss : SpecState} {is : ImplState} {e : EngineId}
    {sid : ScopeId} {loopBody : List Stmt}
    (hSim : MatchStates spec impl ab SemaInv ss is)
    (hOldNotALS : ∀ lid', ¬ atLoopStart is e lid')
    (hSidNotChild : sid ∉ directChildScopes loopBody)
    (hSpecInv : SpecInv spec ss)
    (hUniq : UniqueScopeIds spec.body)
    (hLoopBOf : scopeBodyOf spec.body sid = some loopBody)
    (hDirectChild : ∀ lid', lid' ∈ directChildScopes loopBody → lid' ≠ sid → scopeParent spec.body lid' = some sid)
    (outerLoops : List ScopeId)
    (hParentInOuter : ∀ parent, scopeParent spec.body sid = some parent → parent ∈ outerLoops)
    (hNotSelfParent : ∀ parent, scopeParent spec.body sid = some parent → parent ≠ sid)
    : ∀ lid',
      foldRegOps (scopeEntryOps ab.monotoneReg ab.tripReg loopBody e sid) (is.registers e) (ab.tripReg e lid') =
      tripEntries { ss with scopeEntryHistory := incrScopeEntryHistory ss e sid outerLoops } e spec.body lid' := by
  intro lid'
  rw [foldRegOps_scopeEntryOps_tripReg (ab.tripRegInj _) (fun l1 l2 => Ne.symm (ab.noClob_trip_loop _ l2 l1)) hSidNotChild]
  by_cases hEq : lid' = sid
  · rw [if_pos hEq, hEq, hSim.tripRegInv e sid hOldNotALS]
    exact (tripEntries_incr_self hParentInOuter hNotSelfParent).symm
  · rw [if_neg hEq]
    by_cases hChild : lid' ∈ directChildScopes loopBody
    · rw [if_pos hChild]
      exact (tripEntries_child_reset hSpecInv hEq (hDirectChild lid' hChild hEq)).symm
    · rw [if_neg hChild]
      have hNotParent : scopeParent spec.body lid' ≠ some sid :=
        fun h => hChild (directChild_of_scopeParent_scopeBodyOf h hLoopBOf hUniq hEq)
      rw [hSim.tripRegInv e lid' hOldNotALS]
      exact (tripEntries_preserved_non_child hEq hNotParent).symm

-- Trip register invariant at loop entry (post regOps).
-- This version works for the state AFTER scopeEntryOps commit,
-- where tripReg e sid was incremented and children were reset.
theorem tripRegInv_loop_entry
    {spec : Program} {impl : ImplProgram} {ab : AllocBase spec impl}
    {SemaInv : SpecState → ImplState → Prop}
    {ss : SpecState} {is : ImplState} {e : EngineId}
    {sid : ScopeId}
    (hSim : MatchStates spec impl ab SemaInv ss is)
    (hOldNotALS : ∀ lid', ¬ atLoopStart is e lid')
    (hNewBody : List ImplStmt) (hNewKind : ImplFrameKind)
    (frame : ImplFrame) (rest : List ImplFrame)
    (hStack : (is.pc e).stack = frame :: rest)
    (hKindMatch : hNewKind = .loop sid ∨ hNewKind = .cond sid)
    (outerLoops : List ScopeId)
    (_hParentInOuter : ∀ parent, scopeParent spec.body sid = some parent → parent ∈ outerLoops)
    (_hNotSelfParent : ∀ parent, scopeParent spec.body sid = some parent → parent ≠ sid)
    : let is' := { is with
        pc := funUpdate is.pc e
          { stack := ⟨hNewBody, 0, hNewKind⟩ :: frame :: rest,
            instrIdx := 0, regOpIdx := 0, stmtRegOpIdx := 0 } }
      let ss' := { ss with scopeEntryHistory := incrScopeEntryHistory ss e sid outerLoops }
      ∀ e' lid',
      ((∀ lid'', ¬ atLoopStart is' e' lid'') →
        is.registers e' (ab.tripReg e' lid') = tripEntries ss' e' spec.body lid') := by
  dsimp only; intro e' lid' hNotALL
  by_cases he : e' = e
  · -- e' = e: atLoopStart holds for sid on this engine, so ∀ lid', ¬ atLoopStart is vacuously false
    exfalso; apply hNotALL sid; subst he
    simp only [atLoopStart, funUpdate, ite_true]
    rcases hKindMatch with hKM | hKM
    · exact ⟨_, _, rfl, Or.inl (by rw [hKM]), rfl⟩
    · exact ⟨_, _, rfl, Or.inr (by rw [hKM]), rfl⟩
  · -- e' ≠ e: PC unchanged, use old invariant
    have hOldNotALS' : ∀ lid', ¬ atLoopStart is e' lid' := by
      intro lid' h; exact hNotALL lid' (by simp only [atLoopStart, funUpdate, if_neg he] at h ⊢; exact h)
    simp only [tripEntries, incrScopeEntryHistory, he, false_and, ite_false, totalEntries]
    exact hSim.tripRegInv e' lid' hOldNotALS'

-- CPDT-style: extract the ~50-line AllocatableAt proof that appears identically
-- in both ForwardSim.case_issue and BackwardSim.case_issue.
theorem allocatableAt_of_block_instr (spec : Program) (ss : SpecState) (e : EngineId) (instr : DataPathInstrId)
    (hWf : Allocatable spec) (hSpecInv : SpecInv spec ss)
    (hUniq : UniqueScopeIds spec.body) (hUniqueInstr : UniqueInstrIds spec.engines spec.body)
    (hEngines : e ∈ spec.engines)
    (sf : Frame) (srest : List Frame) (f : EngineId → List DataPathInstrId)
    (hSpecStack : (ss.pc e).stack = sf :: srest)
    (hSpecStmt : sf.body[sf.stmtIdx]? = some (Stmt.block f))
    (hSpecInstr : (f e)[(ss.pc e).instrIdx]? = some instr)
    : AllocatableAt spec ss e instr :=
  allocatable_implies_allocatableAt spec ss e instr hWf hSpecInv
    (fun p c plid sl hPL hSL hNeSl => innermostParentScope_in_sharedLoop_body hUniq hUniqueInstr hPL hSL hNeSl)
    (fun p plid hPL => innermostParentScope_mem_scopeIdsOf hPL)
    (fun p plid sl hCF hPL hSL hNeSl => by
      have hCIB := instrInBody_block_of_mem hEngines (List.mem_of_getElem? hSpecInstr)
      have hInFrame := instrInBody_of_getElem_rest hSpecStmt hCIB
      have hSMP := hSpecStack ▸ hSpecInv.wellFormedPC e
      have hSlContains : instrInBody spec.engines ((scopeBodyOf spec.body sl).getD []) instr = true := by
        unfold backwardDep at hCF; simp [hSL] at hCF
        obtain ⟨_, _, _, ⟨s, hs, hcIn⟩, _⟩ := hCF
        exact instrInBody_of_getElem_rest hs hcIn
      have hSlNotFrame := sl_not_in_frame_loopIds hSMP hUniq hUniqueInstr
        (List.Mem.head _) hSpecStmt hCIB hSlContains
      have hOnStack := sl_on_stack hSMP hUniq hUniqueInstr rfl hInFrame hSlContains hSlNotFrame
      have hOnStackLoops : sl ∈ loopsOnStack ss e := by simp [loopsOnStack, hSpecStack]; exact hOnStack
      obtain ⟨si, hSi⟩ := enclosing_stmtIdxInLoop hOnStack
      have hSiLoops : stmtIdxInLoop (ss.pc e).stack sl = some si := by rw [hSpecStack]; exact hSi
      have hConsumerAt : ∃ s, ((scopeBodyOf spec.body sl).getD [])[si]? = some s ∧
          instrInBody spec.engines [s] instr = true := by
        cases hfk : sf.kind with
        | loop lid =>
          simp [stmtIdxInLoop, hfk] at hSi
          by_cases heq : lid = sl
          · subst heq; simp at hSi; subst hSi
            have hLBOf := smp_scopeBodyOf hSMP hUniq sf (List.Mem.head _) hfk
            simp [hLBOf]; exact ⟨Stmt.block f, hSpecStmt, hCIB⟩
          · simp [heq] at hSi; exact smp_instr_in_loop_stmt hSMP hUniq rfl hInFrame hSi
        | cond sid =>
          simp [stmtIdxInLoop, hfk] at hSi
          by_cases heq : sid = sl
          · subst heq; simp at hSi; subst hSi
            have hLBOf := smp_scopeBodyOf_loop hSMP hUniq sf (List.Mem.head _) (by rw [hfk]; rfl)
            simp [hLBOf]; exact ⟨Stmt.block f, hSpecStmt, hCIB⟩
          · simp [heq] at hSi; exact smp_instr_in_loop_stmt hSMP hUniq rfl hInFrame hSi
        | top => simp [stmtIdxInLoop, hfk] at hSi; exact smp_instr_in_loop_stmt hSMP hUniq rfl hInFrame hSi
      exact discharge_zeroBefore hSpecInv hCF hPL hSL hNeSl hUniqueInstr hUniq hOnStackLoops hSiLoops hConsumerAt)
    (fun p plid hCF hPL hSL => by
      have hCIB := instrInBody_block_of_mem hEngines (List.mem_of_getElem? hSpecInstr)
      have hInFrame := instrInBody_of_getElem_rest hSpecStmt hCIB
      have hSMP := hSpecStack ▸ hSpecInv.wellFormedPC e
      obtain ⟨si, hSi⟩ := smp_has_stmtIdxAtTop hSMP
      have hSiStack : stmtIdxAtTop (ss.pc e).stack = some si := by rw [hSpecStack]; exact hSi
      have hConsumerAt : ∃ s, spec.body[si]? = some s ∧ instrInBody spec.engines [s] instr = true := by
        cases hfk : sf.kind with
        | top =>
          simp [stmtIdxAtTop, hfk] at hSi; subst hSi
          have hBodyEq : sf.body = spec.body := by
            cases hSMP with | base _ _ => rfl | _ => simp at *
          rw [← hBodyEq]; exact ⟨Stmt.block f, hSpecStmt, hCIB⟩
        | loop _ | cond _ => simp [stmtIdxAtTop, hfk] at hSi; exact smp_instr_in_top_stmt hSMP rfl hInFrame hSi
      exact discharge_zeroBeforeTop hSpecInv hCF hPL hSL hUniqueInstr hUniq hSiStack hConsumerAt)

theorem MatchStates.of_pc_only {spec : Program} {impl : ImplProgram} {ab : AllocBase spec impl}
    {SemaInv : SpecState → ImplState → Prop}
    {ss ss' : SpecState} {is is' : ImplState} {e : EngineId}
    (hSim : MatchStates spec impl ab SemaInv ss is)
    (hDataPath : is'.dataPathState = is.dataPathState)
    (hDataPath' : ss'.dataPathState = ss.dataPathState)
    (hInflight : is'.inflight = is.inflight)
    (hInflight' : ∀ e', ss'.inflight e' = ss.inflight e')
    (hRegs : is'.registers = is.registers)
    (_hSema : is'.semaphores = is.semaphores)
    (_hRetire : ss'.rc = ss.rc)
    (hControl : ∀ e', is'.controlState e' = ss'.controlState e')
    (hHist : ss'.scopeEntryHistory = ss.scopeEntryHistory)
    (hPCne : ∀ e', e' ≠ e → is'.pc e' = is.pc e')
    (hPCne' : ∀ e', e' ≠ e → ss'.pc e' = ss.pc e')
    (hPCCorr : PCCorr ab (ss'.pc e) (is'.pc e))
    (hRegOp0 : (is'.pc e).regOpIdx = 0)
    (hAtLoop : ∀ e' lid, atLoopStart is' e' lid ↔ atLoopStart is e' lid)
    (hSemaInv : SemaInv ss' is')
    (hNoNewRegOp : ∀ frame rest ops, (is'.pc e).stack = frame :: rest →
      frame.body[frame.stmtIdx]? ≠ some (.regOp ops))
    : MatchStates spec impl ab SemaInv ss' is' where
  dataPathEq := by rw [hDataPath, hSim.dataPathEq, hDataPath']
  inflightEq := by intro e'; rw [hInflight, hSim.inflightEq, hInflight']
  controlEq := hControl
  semaInv := hSemaInv
  monotoneRegInv := monotoneRegInv_preserved_no_reg_no_hist (fun e lid => hSim.monotoneRegInv e lid) hRegs
    (by intro e' lid ol k; rw [hHist]) hAtLoop
  tripRegInv := tripRegInv_preserved_no_reg_no_hist hSim.tripRegInv hRegs
    (by intro e' lid ol k; rw [hHist]) hAtLoop
  regOpFold := by
    intro e' frame' rest' ops' hStack' hStmt'
    by_cases he : e' = e
    · subst he; exact absurd hStmt' (hNoNewRegOp frame' rest' ops' hStack')
    · rw [hPCne e' he] at hStack' ⊢; rw [hRegs]
      have hHist' : ∀ lid, totalEntries ss' e' lid = totalEntries ss e' lid := by
        intro lid; simp [totalEntries, hHist]
      have hHist'' : ∀ lid, tripEntries ss' e' spec.body lid = tripEntries ss e' spec.body lid := by
        intro lid; simp [tripEntries, totalEntries, hHist]
      obtain ⟨h1, h2⟩ := hSim.regOpFold e' frame' rest' ops' hStack' hStmt'
      exact ⟨fun lid => by rw [hHist']; exact h1 lid, fun lid => by rw [hHist'']; exact h2 lid⟩
  pcCorr := by
    intro e'; by_cases he : e' = e
    · subst he; exact hPCCorr
    · rw [hPCne e' he, hPCne' e' he]; exact hSim.pcCorr e'
  waitRegChain := by
    intro e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
    by_cases he : e' = e
    · subst he; rw [hRegOp0] at hROI; omega
    · rw [hPCne e' he] at hStack' hInstr' hROI ⊢
      rw [hRegs]; exact hSim.waitRegChain e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
  gateRegChain := by
    intro e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI
    by_cases he : e' = e
    · subst he; rw [hRegOp0] at hROI; omega
    · rw [hPCne e' he] at hStack' hInstr' hROI ⊢
      rw [hRegs]; exact hSim.gateRegChain e' frame' rest' f' instr' hStack' hStmt' hInstr' hROI

theorem perInstr_retire_semaInv (spec : Program) (impl : ImplProgram) (alloc : PerInstrAllocR spec impl)
    (e : EngineId) (instr : DataPathInstrId) (rest : List (DataPathInstrId × Phase))
    (ss0 : SpecState) (is0 : ImplState)
    (hSema : perInstrSemaInv alloc ss0 is0)
    (_ : ss0.inflight e = (instr, Phase.committed) :: rest)
    : let ss1 := specRetireUpdate ss0 e instr rest
      let is1 := { is0 with inflight := funUpdate is0.inflight e rest,
                            semaphores := funUpdate is0.semaphores (impl.updateOf instr) (is0.semaphores (impl.updateOf instr) + 1) }
      perInstrSemaInv alloc ss1 is1 := by
  simp only [perInstrSemaInv, funUpdate] at *
  intro j; rw [alloc.updateEq]
  by_cases h1 : alloc.sema j = alloc.sema instr <;> by_cases h2 : j = instr <;> simp_all
  exact absurd (alloc.semaInj _ _ h1) h2

theorem perInstr_semaInv_mono (spec : Program) (impl : ImplProgram) (alloc : PerInstrAllocR spec impl)
    (ss0 ss1 : SpecState) (is0 is1 : ImplState)
    (hRC : ss0.rc = ss1.rc) (hSema : is0.semaphores = is1.semaphores)
    (hInv : perInstrSemaInv alloc ss0 is0)
    : perInstrSemaInv alloc ss1 is1 := by
  intro i; simp only [perInstrSemaInv] at *; rw [← hSema, ← hRC]; exact hInv i
