import SemaAlloc.Spec
import Aesop
-- prove disjunctive membership by searching .inl/.inr paths.
-- Tries: assumption, apply+assumption for recursive lemma, Or.inl, Or.inr (recursing).
syntax "mem_loop " ident : tactic
macro_rules
  | `(tactic| mem_loop $rec) => `(tactic|
    first
    | assumption
    | (apply $rec <;> assumption)
    | (apply Or.inl; first | assumption | (apply $rec <;> assumption))
    | (apply Or.inr; mem_loop $rec))

-- hint lemmas: step-wise reduction of innermostParentScope.
-- These let `simp` reduce the nested match-of-match pattern that blocks automation.
@[simp] theorem innermostParentScope_nil' :
    innermostParentScope engines [] instr = none := by simp [innermostParentScope]

@[simp] theorem innermostParentScope_block' :
    innermostParentScope engines (Stmt.block f :: rest) instr =
    innermostParentScope engines rest instr := by simp [innermostParentScope]


@[simp] theorem innermostSharedScope_nil' :
    innermostSharedScope engines [] i1 i2 = none := by simp [innermostSharedScope]

@[simp] theorem innermostSharedScope_block' :
    innermostSharedScope engines (Stmt.block f :: rest) i1 i2 =
    innermostSharedScope engines rest i1 i2 := by simp [innermostSharedScope]

-- close trivially-preserved PerScopeInv fields when only pc changes.
-- After `refine ⟨inv2, inv3, inv4, inv5, inv6, ?_, ?_⟩`, replaces the trivial fields.
-- For PC-only changes, inv2-inv6 are trivially preserved since they don't depend on pc.
-- Usage: `refine ⟨hPerScopeInv.countBalance, hPerScopeInv.issueOrder, hPerScopeInv.queueOrdered, hPerScopeInv.rcMono, hPerScopeInv.rcBound, ?_, ?_⟩`
-- (This is already what the code does — the real automation target is inv7 + instrAtPC_atTm1.)

-- funUpdate simp lemmas (funUpdate now uses propositional `if x = a`)
@[simp] theorem funUpdate_same [DecidableEq α] (f : α → β) (a : α) (b : β) :
    funUpdate f a b a = b := by simp [funUpdate]

@[simp] theorem funUpdate_other [DecidableEq α] (f : α → β) (a : α) (b : β) (c : α) (h : c ≠ a) :
    funUpdate f a b c = f c := by simp [funUpdate, h]

@[simp] theorem funUpdate_apply [DecidableEq α] (f : α → β) (a : α) (b : β) (x : α) :
    funUpdate f a b x = if x = a then b else f x := by simp [funUpdate]

@[simp] theorem funUpdate_id [DecidableEq α] (f : α → β) (a : α) :
    funUpdate f a (f a) = f := by ext x; simp [funUpdate]; intro h; rw [h]

-- FrameKind helpers + simp lemmas
def FrameKind.loopId? : FrameKind → Option ScopeId
  | .loop sid => some sid
  | .cond sid => some sid
  | .top => none


@[simp] theorem FrameKind.loopId?_loop : (FrameKind.loop sid).loopId? = some sid := rfl
@[simp] theorem FrameKind.loopId?_cond : (FrameKind.cond sid).loopId? = some sid := rfl
@[simp] theorem FrameKind.loopId?_top : FrameKind.top.loopId? = none := rfl

-- PC simp lemmas
@[simp] theorem PC.stack_mk (s i) : ({ stack := s, instrIdx := i } : PC).stack = s := rfl
@[simp] theorem PC.instrIdx_mk (s i) : ({ stack := s, instrIdx := i } : PC).instrIdx = i := rfl

-- SpecState simp lemmas
@[simp] theorem SpecState.pc_mk cs ts pc inf rc lih :
    (⟨cs, ts, pc, inf, rc, lih⟩ : SpecState).pc = pc := rfl
@[simp] theorem SpecState.scopeEntryHistory_mk cs ts pc inf rc lih :
    (⟨cs, ts, pc, inf, rc, lih⟩ : SpecState).scopeEntryHistory = lih := rfl
@[simp] theorem SpecState.controlState_mk cs ts pc inf rc lih :
    (⟨cs, ts, pc, inf, rc, lih⟩ : SpecState).controlState = cs := rfl
@[simp] theorem SpecState.inflight_mk cs ts pc inf rc lih :
    (⟨cs, ts, pc, inf, rc, lih⟩ : SpecState).inflight = inf := rfl
@[simp] theorem SpecState.rc_mk cs ts pc inf rc lih :
    (⟨cs, ts, pc, inf, rc, lih⟩ : SpecState).rc = rc := rfl

-- Simp lemmas for { s with field := val } projections
@[simp] theorem SpecState.pc_with_pc (s : SpecState) pc : { s with pc := pc }.pc = pc := rfl
@[simp] theorem SpecState.datapath_with_pc (s : SpecState) pc : { s with pc := pc }.dataPathState = s.dataPathState := rfl
@[simp] theorem SpecState.hist_with_pc (s : SpecState) pc : { s with pc := pc }.scopeEntryHistory = s.scopeEntryHistory := rfl
@[simp] theorem SpecState.control_with_pc (s : SpecState) pc : { s with pc := pc }.controlState = s.controlState := rfl
@[simp] theorem SpecState.inflight_with_pc (s : SpecState) pc : { s with pc := pc }.inflight = s.inflight := rfl
@[simp] theorem SpecState.retire_with_pc (s : SpecState) pc : { s with pc := pc }.rc = s.rc := rfl

@[simp] theorem SpecState.pc_with_inflight (s : SpecState) inf : { s with inflight := inf }.pc = s.pc := rfl
@[simp] theorem SpecState.datapath_with_inflight (s : SpecState) inf : { s with inflight := inf }.dataPathState = s.dataPathState := rfl
@[simp] theorem SpecState.hist_with_inflight (s : SpecState) inf : { s with inflight := inf }.scopeEntryHistory = s.scopeEntryHistory := rfl

@[simp] theorem SpecState.pc_with_datapath (s : SpecState) ts : { s with dataPathState := ts }.pc = s.pc := rfl
@[simp] theorem SpecState.hist_with_datapath (s : SpecState) ts : { s with dataPathState := ts }.scopeEntryHistory = s.scopeEntryHistory := rfl

@[simp] theorem SpecState.pc_with_retire (s : SpecState) rc : { s with rc := rc }.pc = s.pc := rfl
@[simp] theorem SpecState.hist_with_retire (s : SpecState) rc : { s with rc := rc }.scopeEntryHistory = s.scopeEntryHistory := rfl

@[simp] theorem SpecState.pc_with_control (s : SpecState) cs : { s with controlState := cs }.pc = s.pc := rfl
@[simp] theorem SpecState.hist_with_control (s : SpecState) cs : { s with controlState := cs }.scopeEntryHistory = s.scopeEntryHistory := rfl

-- state_simp: decision procedure for state update goals
macro "state_simp" : tactic => `(tactic|
  simp only [funUpdate_apply, SpecState.pc_with_pc, SpecState.datapath_with_pc,
    SpecState.hist_with_pc, SpecState.control_with_pc, SpecState.inflight_with_pc,
    SpecState.retire_with_pc, SpecState.pc_with_inflight, SpecState.datapath_with_inflight,
    SpecState.hist_with_inflight, SpecState.pc_with_datapath, SpecState.hist_with_datapath,
    SpecState.pc_with_retire, SpecState.hist_with_retire, SpecState.pc_with_control,
    SpecState.hist_with_control,
    PC.stack_mk, PC.instrIdx_mk, ite_true, ite_false])

-- solve_sim: try to close MatchStates fields automatically for PC-only changes
macro "solve_sim_field" h:ident : tactic => `(tactic|
  first
  | exact ($h).dataPathEq
  | exact ($h).controlEq
  | exact ($h).semaEq
  | (intro e'; simp_all [($h).inflightEq, ($h).controlEq])
  | exact ($h).monotoneRegInv
  | exact ($h).pcCorr
  | exact ($h).waitRegChain
  | simp_all)

-- incrScopeEntryHistory simp lemmas
@[simp] theorem incrScopeEntryHistory_ne_engine {s : SpecState} {e e' : EngineId} {sid : ScopeId}
    {outerLoops : List ScopeId} {sid' : ScopeId} {ol : Option ScopeId} {k : Nat} (he : e' ≠ e)
    : incrScopeEntryHistory s e sid outerLoops e' sid' ol k = s.scopeEntryHistory e' sid' ol k := by
  simp [incrScopeEntryHistory, he]

@[simp] theorem incrScopeEntryHistory_ne_sid {s : SpecState} {e : EngineId} {sid sid' : ScopeId}
    {outerLoops : List ScopeId} {ol : Option ScopeId} {k : Nat} (hne : sid' ≠ sid)
    : incrScopeEntryHistory s e sid outerLoops e sid' ol k = s.scopeEntryHistory e sid' ol k := by
  simp [incrScopeEntryHistory, hne]

@[simp] theorem incrScopeEntryHistory_totalEntries {s : SpecState} {e : EngineId} {sid : ScopeId}
    {outerLoops : List ScopeId}
    : incrScopeEntryHistory s e sid outerLoops e sid none 1 = s.scopeEntryHistory e sid none 1 + 1 := by
  simp [incrScopeEntryHistory]

theorem incrScopeEntryHistory_self {s : SpecState} {e : EngineId} {sid : ScopeId}
    {outerLoops : List ScopeId}
    : incrScopeEntryHistory s e sid outerLoops e sid (some sid) (totalEntries s e sid + 1) =
      s.scopeEntryHistory e sid (some sid) (totalEntries s e sid + 1) + 1 := by
  simp [incrScopeEntryHistory, totalEntries]

theorem incrScopeEntryHistory_self_ne {s : SpecState} {e : EngineId} {sid : ScopeId}
    {outerLoops : List ScopeId} {k : Nat}
    (hk : k ≠ totalEntries s e sid + 1)
    (hNotEnc : ¬ outerLoops.any (fun outer => some sid = some outer ∧ k = totalEntries s e outer))
    : incrScopeEntryHistory s e sid outerLoops e sid (some sid) k = s.scopeEntryHistory e sid (some sid) k := by
  unfold incrScopeEntryHistory totalEntries
  simp only [and_self, ite_true]
  split
  · next h =>
    exfalso; rcases h with ⟨hEq, _⟩ | ⟨_, h⟩ | h
    · cases hEq
    · exact hk (by simp [totalEntries]; exact h)
    · exact hNotEnc h
  · rfl

-- Loop IDs on engine e's call stack (from enclosingLoopsFromStack).
def loopsOnStack (ss : SpecState) (e : EngineId) : List ScopeId :=
  enclosingLoopsFromStack (ss.pc e).stack

theorem cumExecs_succ (s : SpecState) (e : EngineId) (pl : ScopeId) (ol : Option ScopeId) (n : Nat)
    : cumExecs s e pl ol (n + 1) = cumExecs s e pl ol n + s.scopeEntryHistory e pl ol (n + 1) := by
  simp [cumExecs, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.add_comm]

theorem foldl_add_congr {f g : Nat → Nat} {n : Nat}
    (h : ∀ k, k ∈ List.range n → f (k + 1) = g (k + 1))
    : (List.range n).foldl (fun acc k => acc + f (k + 1)) 0 =
      (List.range n).foldl (fun acc k => acc + g (k + 1)) 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append,
        List.foldl_cons, List.foldl_nil, List.foldl_cons, List.foldl_nil]
    congr 1
    · exact ih (fun k hk => h k (by simp [List.mem_range] at hk ⊢; omega))
    · exact h n (by simp [List.mem_range])

theorem foldl_add_incr_one {f g : Nat → Nat} {n j : Nat} (hj : j < n)
    (hAt : f (j + 1) = g (j + 1) + 1)
    (hNe : ∀ k, k < n → k ≠ j → f (k + 1) = g (k + 1))
    : (List.range n).foldl (fun acc k => acc + f (k + 1)) 0 =
      (List.range n).foldl (fun acc k => acc + g (k + 1)) 0 + 1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases hjn : j < n
    · rw [ih hjn (fun k hk hne => hNe k (by omega) hne), hNe n (by omega) (by omega)]; omega
    · have hjeq : j = n := by omega
      subst hjeq
      rw [foldl_add_congr (fun k hk => by simp [List.mem_range] at hk; exact hNe k (by omega) (by omega))]
      rw [hAt]; omega

theorem incrScopeEntryHistory_beyond (ss : SpecState) (e : EngineId) (sid : ScopeId)
    (encLoops : List ScopeId) (ol : Option ScopeId) (k : Nat)
    (hk_top : ol = none → k > 1)
    (hk_self : ol = some sid → k > totalEntries ss e sid + 1)
    (hk_enc : ∀ outer, outer ∈ encLoops → ol = some outer → k > totalEntries ss e outer)
    : incrScopeEntryHistory ss e sid encLoops e sid ol k = ss.scopeEntryHistory e sid ol k := by
  unfold incrScopeEntryHistory totalEntries; simp only [and_self, ite_true]; split
  · next h =>
    exfalso; rcases h with ⟨hEq, hK⟩ | ⟨hEq, hK⟩ | h
    · have := hk_top hEq; omega
    · have := hk_self hEq; simp [totalEntries] at this; omega
    · obtain ⟨outer, hMem, hEq, hK⟩ := by simpa [List.any_eq_true] using h
      have := hk_enc outer hMem hEq; simp [totalEntries] at this; omega
  · rfl

theorem cumExecs_of_all_ones {s : SpecState} {e : EngineId} {pl : ScopeId} {ol : Option ScopeId} {m : Nat}
    (h : ∀ k, 1 ≤ k → k ≤ m → s.scopeEntryHistory e pl ol k = 1)
    {n : Nat} (hn : n ≤ m)
    : cumExecs s e pl ol n = n := by
  induction n with
  | zero => simp [cumExecs]
  | succ n ih =>
    rw [cumExecs_succ, ih (by omega), h (n + 1) (by omega) (by omega)]

-- All loop IDs in a statement list (deep, including nested loops).
def scopeIdsOf : List Stmt → List ScopeId
  | [] => []
  | .block _ :: rest => scopeIdsOf rest
  | .loop lid body :: rest => lid :: scopeIdsOf body ++ scopeIdsOf rest
  | .cond thenId elseId b1 b2 :: rest => thenId :: elseId :: scopeIdsOf b1 ++ scopeIdsOf b2 ++ scopeIdsOf rest

theorem scopeBodyOf_mem_scopeIdsOf : ∀ {body : List Stmt} {olid : ScopeId} {olBody : List Stmt},
    scopeBodyOf body olid = some olBody → olid ∈ scopeIdsOf body
  | [], _, _, h => by simp [scopeBodyOf] at h
  | .block _ :: rest, _, _, h => by
    simp [scopeBodyOf] at h; simp [scopeIdsOf]; exact scopeBodyOf_mem_scopeIdsOf h
  | .loop lid body' :: rest, olid, _, h => by
    simp [scopeBodyOf] at h; simp [scopeIdsOf]
    by_cases heq : lid = olid
    · exact .inl heq.symm
    · simp [heq] at h; cases hb : scopeBodyOf body' olid <;> simp [hb] at h <;>
        mem_loop scopeBodyOf_mem_scopeIdsOf
  | .cond thenId elseId b1 b2 :: rest, olid, _, h => by
    simp [scopeBodyOf] at h; simp [scopeIdsOf]
    by_cases ht : thenId = olid
    · exact .inl ht.symm
    · simp [ht] at h; by_cases he : elseId = olid
      · exact .inr (.inl he.symm)
      · simp [he] at h; cases hb1 : scopeBodyOf b1 olid <;> simp [hb1] at h
        · cases hb2 : scopeBodyOf b2 olid <;> simp [hb2] at h <;>
            mem_loop scopeBodyOf_mem_scopeIdsOf
        · mem_loop scopeBodyOf_mem_scopeIdsOf

theorem scopeBodyOf_subset : ∀ {body : List Stmt} {olid : ScopeId} {olBody : List Stmt},
    scopeBodyOf body olid = some olBody → ∀ lid, lid ∈ scopeIdsOf olBody → lid ∈ scopeIdsOf body
  | [], _, _, h => by simp [scopeBodyOf] at h
  | .block _ :: rest, _, _, h => by
    simp [scopeBodyOf] at h; simp [scopeIdsOf]; exact scopeBodyOf_subset h
  | .loop lid' body' :: rest, olid, olBody, h => by
    simp [scopeBodyOf] at h; simp [scopeIdsOf]; intro lid hlid
    by_cases heq : lid' = olid
    · subst heq; simp at h; subst h; mem_loop scopeBodyOf_subset
    · simp [heq] at h; cases hb : scopeBodyOf body' olid <;> simp [hb] at h <;>
        (try subst h) <;> mem_loop scopeBodyOf_subset
  | .cond thenId elseId b1 b2 :: rest, olid, olBody, h => by
    simp [scopeBodyOf] at h; simp [scopeIdsOf]; intro lid hlid
    by_cases ht : thenId = olid
    · subst ht; simp at h; subst h; mem_loop scopeBodyOf_subset
    · simp [ht] at h; by_cases he : elseId = olid
      · subst he; simp at h; subst h; mem_loop scopeBodyOf_subset
      · simp [he] at h; cases hb1 : scopeBodyOf b1 olid <;> simp [hb1] at h
        · cases hb2 : scopeBodyOf b2 olid <;> simp [hb2] at h <;>
            (try subst h) <;> mem_loop scopeBodyOf_subset
        · subst h; mem_loop scopeBodyOf_subset

-- No duplicate loop IDs in the AST. Assumed by top-level theorems.
-- Ensures scopeParent, scopeBodyOf, etc. are unambiguous.
inductive UniqueScopeIds : List Stmt → Prop where
  | nil : UniqueScopeIds []
  | block (f rest) : UniqueScopeIds rest → UniqueScopeIds (.block f :: rest)
  | loop (lid body rest) :
      lid ∉ scopeIdsOf body →        -- lid not reused inside its own body
      lid ∉ scopeIdsOf rest →         -- lid not reused in sibling statements
      (∀ x, x ∈ scopeIdsOf body → x ∉ scopeIdsOf rest) →  -- body and rest loop IDs disjoint
      UniqueScopeIds body →
      UniqueScopeIds rest →
      UniqueScopeIds (.loop lid body :: rest)
  | cond (thenId elseId : ScopeId) (tb eb rest) :
      thenId ≠ elseId →               -- then and else branch IDs are distinct
      thenId ∉ scopeIdsOf tb →
      thenId ∉ scopeIdsOf eb →
      thenId ∉ scopeIdsOf rest →
      elseId ∉ scopeIdsOf tb →
      elseId ∉ scopeIdsOf eb →
      elseId ∉ scopeIdsOf rest →
      (∀ x, x ∈ scopeIdsOf tb → x ∉ scopeIdsOf eb ∧ x ∉ scopeIdsOf rest) →  -- then/else/rest pairwise disjoint
      (∀ x, x ∈ scopeIdsOf eb → x ∉ scopeIdsOf rest) →
      UniqueScopeIds tb →
      UniqueScopeIds eb →
      UniqueScopeIds rest →
      UniqueScopeIds (.cond thenId elseId tb eb :: rest)

theorem uniqueScopeIds_of_getElem {body : List Stmt} {idx : Nat} {stmt : Stmt}
    (hIdx : body[idx]? = some stmt) (hUniq : UniqueScopeIds body)
    : UniqueScopeIds [stmt] := by
  induction hUniq generalizing idx with
  | nil => simp at hIdx
  | block _ _ _ ih => cases idx with | zero => simp at hIdx; subst hIdx; exact .block _ _ .nil | succ n => simp at hIdx; exact ih hIdx
  | loop lid' body' rest' hNotBody hNotRest hDisj hBody hRest ih_body ih_rest =>
    cases idx with
    | zero => simp at hIdx; obtain ⟨rfl, rfl⟩ := hIdx; exact .loop _ _ _ hNotBody (by simp [scopeIdsOf]) (by intro x _ h; simp [scopeIdsOf] at h) hBody .nil
    | succ n => simp at hIdx; exact ih_rest hIdx
  | cond thenId elseId tb eb rest hNe hTnTb hTnEb hTnR hEnTb hEnEb hEnR hTbDisj hEbDisj hUTb hUEb hUR ih_tb ih_eb ih_rest =>
    cases idx with
    | zero => simp at hIdx; obtain ⟨rfl, rfl, rfl, rfl⟩ := hIdx; exact .cond _ _ _ _ _ hNe hTnTb hTnEb (by simp [scopeIdsOf]) hEnTb hEnEb (by simp [scopeIdsOf]) (fun x hx => ⟨(hTbDisj x hx).1, by simp [scopeIdsOf]⟩) (fun _ _ h => by simp [scopeIdsOf] at h) hUTb hUEb .nil
    | succ n => simp at hIdx; exact ih_rest hIdx

-- Helper: scopeParent.go under UniqueScopeIds cannot return target itself
-- (unless that was the container to begin with).
private theorem scopeParent_go_ne_target
    {body : List Stmt} {target : ScopeId} {container : Option ScopeId}
    (hUniq : UniqueScopeIds body)
    (hGo : scopeParent.go body target container = some target)
    : container = some target := by
  induction hUniq generalizing target container with
  | nil => simp [scopeParent.go] at hGo
  | block f rest hUR ih =>
    simp [scopeParent.go] at hGo; exact ih hGo
  | loop lid lb rest hNotBody hNotRest hDisj hUBody hURest ih_body ih_rest =>
    simp [scopeParent.go] at hGo
    by_cases hLid : lid = target
    · subst hLid; simp at hGo; exact hGo
    · simp [hLid] at hGo
      cases hInner : scopeParent.go lb target (some lid) with
      | none => simp [hInner] at hGo; exact ih_rest hGo
      | some p =>
        simp [hInner] at hGo; subst hGo
        exact absurd (by simpa using ih_body hInner) hLid
  | cond thenId elseId tb eb rest hNe hTnTb hTnEb hTnR hEnTb hEnEb hEnR
      hTbDisj hEbDisj hUTb hUEb hUR ih_tb ih_eb ih_rest =>
    simp [scopeParent.go] at hGo
    by_cases hThen : thenId = target
    · subst hThen; simp at hGo; exact hGo
    · simp [hThen] at hGo
      by_cases hElse : elseId = target
      · subst hElse; simp at hGo; exact hGo
      · simp [hElse] at hGo
        cases hInnerTb : scopeParent.go tb target (some thenId) with
        | some p =>
          simp [hInnerTb] at hGo; subst hGo
          exact absurd (by simpa using ih_tb hInnerTb) hThen
        | none =>
          simp [hInnerTb] at hGo
          cases hInnerEb : scopeParent.go eb target (some elseId) with
          | some p =>
            simp [hInnerEb] at hGo; subst hGo
            exact absurd (by simpa using ih_eb hInnerEb) hElse
          | none => simp [hInnerEb] at hGo; exact ih_rest hGo

-- A loop cannot be its own parent under UniqueScopeIds.
theorem scopeParent_ne_self {body : List Stmt} {sid parent : ScopeId}
    (hUS : UniqueScopeIds body) (hP : scopeParent body sid = some parent)
    : parent ≠ sid := by
  intro heq; subst heq
  have : (none : Option ScopeId) = some parent :=
    scopeParent_go_ne_target hUS (show scopeParent.go body parent none = some parent from hP)
  simp at this

-- No duplicate instruction IDs in the AST. Assumed by top-level theorems.
-- Ensures each instruction appears in exactly one block on exactly one engine.
inductive UniqueInstrIds (engines : List EngineId) : List Stmt → Prop where
  | nil : UniqueInstrIds engines []
  | block (f rest) :
      (∀ e, (f e).Nodup) →            -- no duplicates within a single engine's list
      (∀ instr e1 e2, e1 ∈ engines → e2 ∈ engines →
        instr ∈ f e1 → instr ∈ f e2 → e1 = e2) →  -- each instr belongs to at most one engine
      (∀ instr, (findInBlock engines f instr).isSome → instrInBody engines rest instr = false) →  -- not reused in later statements
      UniqueInstrIds engines rest →
      UniqueInstrIds engines (.block f :: rest)
  | loop (lid body rest) :
      (∀ instr, instrInBody engines body instr → instrInBody engines rest instr = false) →  -- body and rest instr IDs disjoint
      UniqueInstrIds engines body →
      UniqueInstrIds engines rest →
      UniqueInstrIds engines (.loop lid body :: rest)
  | cond (thenId elseId : ScopeId) (tb eb rest) :
      (∀ instr, instrInBody engines tb instr → instrInBody engines eb instr = false) →  -- then/else instr IDs disjoint
      (∀ instr, instrInBody engines tb instr → instrInBody engines rest instr = false) →  -- then/rest disjoint
      (∀ instr, instrInBody engines eb instr → instrInBody engines rest instr = false) →  -- else/rest disjoint
      UniqueInstrIds engines tb →
      UniqueInstrIds engines eb →
      UniqueInstrIds engines rest →
      UniqueInstrIds engines (.cond thenId elseId tb eb :: rest)


theorem mem_scopeIdsOf_of_getElem {body : List Stmt} {idx : Nat} {stmt : Stmt} {lid : ScopeId}
    (hIdx : body[idx]? = some stmt) (hMem : lid ∈ scopeIdsOf [stmt])
    : lid ∈ scopeIdsOf body := by
  induction body generalizing idx with
  | nil => simp at hIdx
  | cons s rest ih =>
    cases idx with
    | zero =>
      simp at hIdx; subst hIdx
      cases s with
      | block f => simp [scopeIdsOf] at hMem
      | loop | cond => simp [scopeIdsOf, List.mem_append] at hMem ⊢; aesop
    | succ n =>
      simp [List.getElem?_cons_succ] at hIdx; have := ih hIdx
      cases s <;> simp [scopeIdsOf, List.mem_append] <;> aesop

theorem scopeBodyOf_none_of_not_mem {body : List Stmt} {lid : ScopeId}
    (h : lid ∉ scopeIdsOf body) : scopeBodyOf body lid = none := by
  match body with
  | [] => simp [scopeBodyOf]
  | .block _ :: rest =>
    simp [scopeBodyOf, scopeIdsOf] at h ⊢; exact scopeBodyOf_none_of_not_mem h
  | .loop lid' body' :: rest =>
    simp [scopeIdsOf] at h
    simp [scopeBodyOf, show lid' ≠ lid from fun heq => h.1 heq.symm,
          scopeBodyOf_none_of_not_mem h.2.1, Option.orElse]
    exact scopeBodyOf_none_of_not_mem h.2.2
  | .cond thenId elseId b1 b2 :: rest =>
    simp [scopeIdsOf] at h
    simp [scopeBodyOf, show thenId ≠ lid from fun heq => h.1 heq.symm,
          show elseId ≠ lid from fun heq => h.2.1 heq.symm,
          scopeBodyOf_none_of_not_mem h.2.2.1, scopeBodyOf_none_of_not_mem h.2.2.2.1, Option.orElse]
    exact scopeBodyOf_none_of_not_mem h.2.2.2.2
termination_by sizeOf body

private theorem scopeBodyOf_cons_of_found {s : Stmt} {rest : List Stmt} {sid : ScopeId} {sb : List Stmt}
    (hLocal : scopeBodyOf [s] sid = some sb) (_hNotRest : sid ∉ scopeIdsOf rest)
    : scopeBodyOf (s :: rest) sid = some sb := by
  cases s with
  | block f =>
    simp [scopeBodyOf] at hLocal
  | loop lid body =>
    simp [scopeBodyOf] at hLocal ⊢
    by_cases heq : lid = sid <;> simp [heq] at hLocal ⊢ <;> try exact hLocal
    cases hb : scopeBodyOf body sid <;> simp [hb] at hLocal ⊢; exact hLocal
  | cond thenId elseId tb eb =>
    simp [scopeBodyOf] at hLocal ⊢
    by_cases ht : thenId = sid <;> simp [ht] at hLocal ⊢ <;> try exact hLocal
    by_cases he : elseId = sid <;> simp [he] at hLocal ⊢ <;> try exact hLocal
    cases hb1 : scopeBodyOf tb sid <;> simp [hb1] at hLocal ⊢ <;> try exact hLocal
    cases hb2 : scopeBodyOf eb sid <;> simp [hb2] at hLocal ⊢; exact hLocal

theorem scopeBodyOf_of_getElem_general {body : List Stmt} {idx : Nat} {stmt : Stmt} {sid : ScopeId} {sb : List Stmt}
    (hIdx : body[idx]? = some stmt) (hLocal : scopeBodyOf [stmt] sid = some sb) (hUniq : UniqueScopeIds body)
    : scopeBodyOf body sid = some sb := by
  induction hUniq generalizing idx with
  | nil => simp at hIdx
  | block f rest _ ih =>
    cases idx with
    | zero => simp at hIdx; cases hIdx; simp [scopeBodyOf] at hLocal
    | succ n => simp at hIdx; simp [scopeBodyOf]; exact ih hIdx
  | loop lid' body' rest' hNotBody hNotRest hDisj hBody hRest ih_body ih_rest =>
    cases idx with
    | zero =>
      simp at hIdx; obtain ⟨rfl, rfl⟩ := hIdx
      have hMS := scopeBodyOf_mem_scopeIdsOf hLocal; simp [scopeIdsOf] at hMS
      exact scopeBodyOf_cons_of_found hLocal (by
        intro h; rcases hMS with rfl | hInBody; exact hNotRest h; exact hDisj sid hInBody h)
    | succ n =>
      simp at hIdx; have hInRest := mem_scopeIdsOf_of_getElem hIdx (scopeBodyOf_mem_scopeIdsOf hLocal)
      simp [scopeBodyOf, show lid' ≠ sid from fun h => hNotRest (h ▸ hInRest),
            scopeBodyOf_none_of_not_mem (show sid ∉ scopeIdsOf body' from fun h => hDisj sid h hInRest), Option.orElse]
      exact ih_rest hIdx
  | cond thenId elseId tb eb rest hNe hTnTb hTnEb hTnR hEnTb hEnEb hEnR hTbDisj hEbDisj _ _ _ _ _ ih_rest =>
    cases idx with
    | zero =>
      simp at hIdx; obtain ⟨rfl, rfl, rfl, rfl⟩ := hIdx
      have hMS := scopeBodyOf_mem_scopeIdsOf hLocal; simp [scopeIdsOf] at hMS
      exact scopeBodyOf_cons_of_found hLocal (by
        intro h; rcases hMS with rfl | rfl | hTb | hEb
        · exact hTnR h
        · exact hEnR h
        · exact (hTbDisj sid hTb).2 h
        · exact hEbDisj sid hEb h)
    | succ n =>
      simp at hIdx; have hInRest := mem_scopeIdsOf_of_getElem hIdx (scopeBodyOf_mem_scopeIdsOf hLocal)
      simp [scopeBodyOf, show thenId ≠ sid from fun h => hTnR (h ▸ hInRest),
            show elseId ≠ sid from fun h => hEnR (h ▸ hInRest),
            scopeBodyOf_none_of_not_mem (show sid ∉ scopeIdsOf tb from fun h => (hTbDisj sid h).2 hInRest),
            scopeBodyOf_none_of_not_mem (show sid ∉ scopeIdsOf eb from fun h => hEbDisj sid h hInRest), Option.orElse]
      exact ih_rest hIdx

theorem scopeBodyOf_of_getElem {body : List Stmt} {idx : Nat} {lid : ScopeId} {lb : List Stmt}
    (hIdx : body[idx]? = some (Stmt.loop lid lb)) (hUniq : UniqueScopeIds body)
    : scopeBodyOf body lid = some lb :=
  scopeBodyOf_of_getElem_general hIdx (by simp [scopeBodyOf]) hUniq

theorem scopeBodyOf_of_getElem_condTrue {body : List Stmt} {idx : Nat} {thenId elseId : ScopeId} {tb eb : List Stmt}
    (hIdx : body[idx]? = some (Stmt.cond thenId elseId tb eb)) (hUniq : UniqueScopeIds body)
    : scopeBodyOf body thenId = some tb :=
  scopeBodyOf_of_getElem_general hIdx (by simp [scopeBodyOf]) hUniq

theorem scopeBodyOf_of_getElem_condFalse {body : List Stmt} {idx : Nat} {thenId elseId : ScopeId} {tb eb : List Stmt}
    (hIdx : body[idx]? = some (Stmt.cond thenId elseId tb eb)) (hUniq : UniqueScopeIds body)
    : scopeBodyOf body elseId = some eb := by
  apply scopeBodyOf_of_getElem_general hIdx _ hUniq
  have hUniqStmt := uniqueScopeIds_of_getElem hIdx hUniq
  cases hUniqStmt with
  | cond _ _ _ _ _ hNe => simp [scopeBodyOf, hNe]

theorem scopeBodyOf_descend_general {body : List Stmt} {idx : Nat} {stmt : Stmt} {lid : ScopeId}
    (hIdx : body[idx]? = some stmt) (hMem : lid ∈ scopeIdsOf [stmt])
    (hUniq : UniqueScopeIds body) : scopeBodyOf body lid = scopeBodyOf [stmt] lid := by
  induction hUniq generalizing idx with
  | nil => simp at hIdx
  | block _ _ _ ih =>
    cases idx with | zero => simp at hIdx; subst hIdx; simp [scopeIdsOf] at hMem | succ n => simp at hIdx; simp [scopeBodyOf]; exact ih hIdx
  | loop lid' body' rest' hNotBody hNotRest hDisj hBody hRest ih_body ih_rest =>
    cases idx with
    | zero =>
      simp at hIdx; subst hIdx
      have hNotInRest : lid ∉ scopeIdsOf rest' := by
        intro h; simp [scopeIdsOf] at hMem
        rcases hMem with rfl | hInBody
        · exact hNotRest h
        · exact hDisj lid hInBody h
      have hRestNone := scopeBodyOf_none_of_not_mem hNotInRest
      simp [scopeIdsOf] at hMem
      rcases hMem with rfl | hInBody
      · simp [scopeBodyOf]
      · have hNeLid : lid' ≠ lid := fun h => hNotBody (h ▸ hInBody)
        simp [scopeBodyOf, hNeLid, hRestNone, Option.orElse]
    | succ n =>
      simp at hIdx
      have hInRest := mem_scopeIdsOf_of_getElem hIdx hMem
      simp [scopeBodyOf, scopeBodyOf_none_of_not_mem, Option.orElse,
            show lid' ≠ lid from fun h => hNotRest (h ▸ hInRest),
            show lid ∉ scopeIdsOf body' from fun h => hDisj lid h hInRest]
      exact ih_rest hIdx
  | cond thenId elseId tb eb rest hNe hTnTb hTnEb hTnR hEnTb hEnEb hEnR hTbDisj hEbDisj _ _ _ _ _ ih_rest =>
    cases idx with
    | zero =>
      simp at hIdx; subst hIdx
      have hNotInRest : lid ∉ scopeIdsOf rest := by
        intro h; simp [scopeIdsOf] at hMem
        rcases hMem with rfl | rfl | hTb | hEb
        · exact hTnR h
        · exact hEnR h
        · exact (hTbDisj lid hTb).2 h
        · exact hEbDisj lid hEb h
      simp [scopeIdsOf] at hMem
      rcases hMem with rfl | rfl | hTb | hEb
      · simp [scopeBodyOf]
      · simp [scopeBodyOf, hNe]
      · simp [scopeBodyOf, scopeBodyOf_none_of_not_mem, Option.orElse,
              show thenId ≠ lid from fun h => hTnTb (h ▸ hTb),
              show elseId ≠ lid from fun h => hEnTb (h ▸ hTb), (hTbDisj lid hTb).1, *]
      · simp [scopeBodyOf, scopeBodyOf_none_of_not_mem, Option.orElse,
              show thenId ≠ lid from fun h => hTnEb (h ▸ hEb),
              show elseId ≠ lid from fun h => hEnEb (h ▸ hEb),
              show lid ∉ scopeIdsOf tb from fun h => (hTbDisj lid h).1 hEb, *]
    | succ n =>
      simp at hIdx
      have hInRest := mem_scopeIdsOf_of_getElem hIdx hMem
      simp [scopeBodyOf, scopeBodyOf_none_of_not_mem, Option.orElse,
            show thenId ≠ lid from fun h => hTnR (h ▸ hInRest),
            show elseId ≠ lid from fun h => hEnR (h ▸ hInRest),
            show lid ∉ scopeIdsOf tb from fun h => (hTbDisj lid h).2 hInRest,
            show lid ∉ scopeIdsOf eb from fun h => hEbDisj lid h hInRest]
      exact ih_rest hIdx

theorem scopeBodyOf_descend_loop {body : List Stmt} {idx : Nat} {lid' : ScopeId} {lb : List Stmt} {lid : ScopeId}
    (hIdx : body[idx]? = some (Stmt.loop lid' lb)) (hMem : lid ∈ scopeIdsOf lb)
    (hUniq : UniqueScopeIds body) : scopeBodyOf body lid = scopeBodyOf lb lid := by
  have hMemStmt : lid ∈ scopeIdsOf [Stmt.loop lid' lb] := by simp [scopeIdsOf]; right; exact hMem
  have hGen := scopeBodyOf_descend_general hIdx hMemStmt hUniq
  have hUniqStmt := uniqueScopeIds_of_getElem hIdx hUniq
  cases hUniqStmt with
  | loop _ _ _ hNotBody =>
    have hNeLid : lid' ≠ lid := fun h => hNotBody (h ▸ hMem)
    rw [hGen]; simp [scopeBodyOf, hNeLid]

theorem scopeBodyOf_descend_condTrue {body : List Stmt} {idx : Nat} {thenId elseId : ScopeId} {tb eb : List Stmt} {lid : ScopeId}
    (hIdx : body[idx]? = some (Stmt.cond thenId elseId tb eb)) (hMem : lid ∈ scopeIdsOf tb)
    (hUniq : UniqueScopeIds body) : scopeBodyOf body lid = scopeBodyOf tb lid := by
  have hMemStmt : lid ∈ scopeIdsOf [Stmt.cond thenId elseId tb eb] := by
    simp [scopeIdsOf, List.mem_append]; mem_loop scopeBodyOf_mem_scopeIdsOf
  have hGen := scopeBodyOf_descend_general hIdx hMemStmt hUniq
  have hUniqStmt := uniqueScopeIds_of_getElem hIdx hUniq
  cases hUniqStmt with
  | cond _ _ _ _ _ hNe' hTnTb' hTnEb' _ hEnTb' _ _ hTbDisj' =>
    have hNeThen : thenId ≠ lid := fun h => hTnTb' (h ▸ hMem)
    have hNeElse : elseId ≠ lid := fun h => hEnTb' (h ▸ hMem)
    have hNotInEb : lid ∉ scopeIdsOf eb := (hTbDisj' lid hMem).1
    rw [hGen]; simp [scopeBodyOf, hNeThen, hNeElse, scopeBodyOf_none_of_not_mem hNotInEb]

theorem scopeBodyOf_descend_condFalse {body : List Stmt} {idx : Nat} {thenId elseId : ScopeId} {tb eb : List Stmt} {lid : ScopeId}
    (hIdx : body[idx]? = some (Stmt.cond thenId elseId tb eb)) (hMem : lid ∈ scopeIdsOf eb)
    (hUniq : UniqueScopeIds body) : scopeBodyOf body lid = scopeBodyOf eb lid := by
  have hMemStmt : lid ∈ scopeIdsOf [Stmt.cond thenId elseId tb eb] := by
    simp_all [scopeIdsOf, List.mem_append]
  have hGen := scopeBodyOf_descend_general hIdx hMemStmt hUniq
  have hUniqStmt := uniqueScopeIds_of_getElem hIdx hUniq
  cases hUniqStmt with
  | cond _ _ _ _ _ hNe' hTnTb' hTnEb' _ hEnTb' hEnEb' _ hTbDisj' =>
    have hNeThen : thenId ≠ lid := fun h => hTnEb' (h ▸ hMem)
    have hNeElse : elseId ≠ lid := fun h => hEnEb' (h ▸ hMem)
    have hNotInTb : lid ∉ scopeIdsOf tb := fun h => (hTbDisj' lid h).1 hMem
    rw [hGen]; simp [scopeBodyOf, hNeThen, hNeElse, scopeBodyOf_none_of_not_mem hNotInTb]

theorem innermostParentScope_mem_scopeIdsOf : ∀ {engines : List EngineId} {body : List Stmt} {instr : DataPathInstrId} {plid : ScopeId},
    innermostParentScope engines body instr = some plid → plid ∈ scopeIdsOf body
  | _, [], _, _, h => by simp at h
  | engines, .block _ :: rest, instr, plid, h => by
    simp at h; simp [scopeIdsOf]; exact innermostParentScope_mem_scopeIdsOf h
  | engines, .loop lid body' :: rest, instr, plid, h => by
    simp only [innermostParentScope] at h; by_cases hIn : instrInBody engines body' instr
    · simp [hIn] at h; cases hInner : innermostParentScope engines body' instr <;>
        simp [hInner] at h <;> subst h <;> simp [scopeIdsOf]
      mem_loop innermostParentScope_mem_scopeIdsOf
    · simp [hIn] at h; simp [scopeIdsOf]; mem_loop innermostParentScope_mem_scopeIdsOf
  | engines, .cond thenId elseId b1 b2 :: rest, instr, plid, h => by
    simp only [innermostParentScope] at h; by_cases hIn1 : instrInBody engines b1 instr
    · simp [hIn1] at h; cases hInner : innermostParentScope engines b1 instr <;>
        simp [hInner] at h <;> subst h <;> simp [scopeIdsOf]
      mem_loop innermostParentScope_mem_scopeIdsOf
    · simp [hIn1] at h; by_cases hIn2 : instrInBody engines b2 instr
      · simp [hIn2] at h; cases hInner : innermostParentScope engines b2 instr <;>
          simp [hInner] at h <;> subst h <;> simp [scopeIdsOf]
        mem_loop innermostParentScope_mem_scopeIdsOf
      · simp [hIn2] at h; simp [scopeIdsOf]; mem_loop innermostParentScope_mem_scopeIdsOf

theorem innermostSharedScope_mem_scopeIdsOf : ∀ {engines : List EngineId} {body : List Stmt} {i1 i2 : DataPathInstrId} {sl : ScopeId},
    innermostSharedScope engines body i1 i2 = some sl → sl ∈ scopeIdsOf body
  | _, [], _, _, _, h => by simp at h
  | engines, .block _ :: rest, i1, i2, sl, h => by
    simp at h; simp [scopeIdsOf]; exact innermostSharedScope_mem_scopeIdsOf h
  | engines, .loop lid body' :: rest, i1, i2, sl, h => by
    simp only [innermostSharedScope] at h; by_cases hBoth : (instrInBody engines body' i1 && instrInBody engines body' i2) = true
    · simp [hBoth] at h; cases hInner : innermostSharedScope engines body' i1 i2 <;>
        simp [hInner] at h <;> subst h <;> simp [scopeIdsOf]
      mem_loop innermostSharedScope_mem_scopeIdsOf
    · simp [hBoth] at h; simp [scopeIdsOf]; mem_loop innermostSharedScope_mem_scopeIdsOf
  | engines, .cond thenId elseId b1 b2 :: rest, i1, i2, sl, h => by
    simp only [innermostSharedScope] at h; by_cases hIn1 : (instrInBody engines b1 i1 && instrInBody engines b1 i2) = true
    · simp [hIn1] at h; cases hInner : innermostSharedScope engines b1 i1 i2 <;>
        simp [hInner] at h <;> subst h <;> simp [scopeIdsOf]
      mem_loop innermostSharedScope_mem_scopeIdsOf
    · simp [hIn1] at h; by_cases hIn2 : (instrInBody engines b2 i1 = true ∧ instrInBody engines b2 i2 = true)
      · simp [hIn2] at h; cases hInner : innermostSharedScope engines b2 i1 i2 <;>
          simp [hInner] at h <;> subst h <;> simp [scopeIdsOf]
        mem_loop innermostSharedScope_mem_scopeIdsOf
      · simp [hIn2] at h; simp [scopeIdsOf]; mem_loop innermostSharedScope_mem_scopeIdsOf

theorem innermostSharedScope_instrInBody_left : ∀ {engines : List EngineId} {body : List Stmt} {p c : DataPathInstrId} {sl : ScopeId},
    innermostSharedScope engines body p c = some sl → instrInBody engines body p = true
  | _, [], _, _, _, h => by simp at h
  | engines, .block f :: rest, p, c, sl, h => by
    simp at h; simp [instrInBody]; right; exact innermostSharedScope_instrInBody_left h
  | engines, .loop lid body' :: rest, p, c, sl, h => by
    simp only [innermostSharedScope] at h; simp [instrInBody]; by_cases instrInBody engines body' p && instrInBody engines body' c <;> simp_all [Bool.and_eq_true]; exact .inr (innermostSharedScope_instrInBody_left h)
  | engines, .cond thenId elseId b1 b2 :: rest, p, c, sl, h => by
    simp only [innermostSharedScope] at h; simp [instrInBody]; by_cases instrInBody engines b1 p && instrInBody engines b1 c <;> simp_all [Bool.and_eq_true]; by_cases (instrInBody engines b2 p = true ∧ instrInBody engines b2 c = true) <;> simp_all; exact .inr (innermostSharedScope_instrInBody_left h)

theorem innermostParentScope_of_sharedLoop : ∀ {engines : List EngineId} {body : List Stmt} {p c : DataPathInstrId} {sl : ScopeId},
    innermostSharedScope engines body p c = some sl →
    ∃ plid, innermostParentScope engines body p = some plid
  | _, [], _, _, _, h => by simp at h
  | engines, .block _ :: rest, p, c, sl, h => by
    simp at h; simp; exact innermostParentScope_of_sharedLoop h
  | engines, .loop lid body' :: rest, p, c, sl, h => by
    simp only [innermostSharedScope] at h; simp only [innermostParentScope]
    by_cases hInP : instrInBody engines body' p
    · simp [hInP]; cases innermostParentScope engines body' p <;> simp
    · simp [show ¬(instrInBody engines body' p && instrInBody engines body' c) = true from by simp [hInP]] at h
      simp [hInP]; exact innermostParentScope_of_sharedLoop h
  | engines, .cond thenId elseId b1 b2 :: rest, p, c, sl, h => by
    simp only [innermostSharedScope] at h; simp only [innermostParentScope]
    by_cases hInP1 : instrInBody engines b1 p
    · simp [hInP1]; cases innermostParentScope engines b1 p <;> simp
    · simp [show ¬(instrInBody engines b1 p && instrInBody engines b1 c) = true from by simp [hInP1]] at h
      by_cases hIn2Both : instrInBody engines b2 p = true ∧ instrInBody engines b2 c = true
      · simp [hIn2Both] at h; simp [hInP1, hIn2Both.1]
        cases innermostParentScope engines b2 p <;> simp
      · simp [hIn2Both] at h
        obtain ⟨plid, hPR⟩ := innermostParentScope_of_sharedLoop h
        simp [hInP1]
        by_cases hInP2 : instrInBody engines b2 p
        · simp [hInP2]; cases innermostParentScope engines b2 p <;> simp
        · simp [hInP2]; exact ⟨plid, hPR⟩

theorem innermostSharedScope_eq_none_of_parent_eq_none
    {engines : List EngineId} {body : List Stmt} {producer consumer : DataPathInstrId}
    (hParent : innermostParentScope engines body producer = none) :
    innermostSharedScope engines body producer consumer = none := by
  cases hShared : innermostSharedScope engines body producer consumer with
  | none => rfl
  | some sid =>
      obtain ⟨plid, hParent'⟩ := innermostParentScope_of_sharedLoop hShared
      rw [hParent] at hParent'
      simp at hParent'

theorem innermostParentScope_instrInBody : ∀ {engines : List EngineId} {body : List Stmt} {p : DataPathInstrId} {plid : ScopeId},
    innermostParentScope engines body p = some plid → instrInBody engines body p = true
  | _, [], _, _, h => by simp at h
  | engines, .block _ :: rest, p, plid, h => by
    simp at h; simp [instrInBody]; right; exact innermostParentScope_instrInBody h
  | engines, .loop lid body' :: rest, p, plid, h => by
    simp only [innermostParentScope] at h; simp [instrInBody]; by_cases instrInBody engines body' p <;> simp_all [innermostParentScope_instrInBody]
  | engines, .cond thenId elseId b1 b2 :: rest, p, plid, h => by
    simp only [innermostParentScope] at h; simp [instrInBody]; by_cases instrInBody engines b1 p <;> simp_all; by_cases instrInBody engines b2 p <;> simp_all [innermostParentScope_instrInBody]

theorem innermostParentScope_in_sharedLoop_body : ∀ {engines : List EngineId} {body : List Stmt}
    {p c : DataPathInstrId} {plid sl : ScopeId},
    UniqueScopeIds body →
    UniqueInstrIds engines body →
    innermostParentScope engines body p = some plid →
    innermostSharedScope engines body p c = some sl →
    sl ≠ plid →
    plid ∈ scopeIdsOf ((scopeBodyOf body sl).getD [])
  | _, [], _, _, _, _, _, _, hP, _, _ => by simp at hP
  | engines, .block _ :: rest, p, c, plid, sl, hU, hUI, hP, hS, hNe => by
    cases hU with | block _ _ hUR =>
    cases hUI with | block _ _ _ _ _ hUIR =>
    simp at hP; simp at hS; simp [scopeBodyOf]
    exact innermostParentScope_in_sharedLoop_body hUR hUIR hP hS hNe
  | engines, .loop lid body' :: rest, p, c, plid, sl, hU, hUI, hP, hS, hNe => by
    cases hU with | loop _ _ _ hNB hNR hDisj hUB hUR =>
    cases hUI with | loop _ _ _ hUIDisj hUIB hUIR =>
    simp only [innermostParentScope] at hP; simp only [innermostSharedScope] at hS
    by_cases hBoth : instrInBody engines body' p && instrInBody engines body' c
    · have hInP : instrInBody engines body' p = true := by
        revert hBoth; cases instrInBody engines body' p <;> simp
      simp [hBoth] at hS; simp [hInP] at hP
      cases hIS : innermostSharedScope engines body' p c with
      | some innerS =>
        simp [hIS] at hS
        cases hIP : innermostParentScope engines body' p with
        | some innerP =>
          simp [hIP] at hP
          have hSlB := innermostSharedScope_mem_scopeIdsOf hIS
          rw [← hS]; simp [scopeBodyOf, show lid ≠ innerS from fun h => hNB (h ▸ hSlB),
                scopeBodyOf_none_of_not_mem (fun h => hDisj _ hSlB h)]
          rw [← hP]; exact innermostParentScope_in_sharedLoop_body hUB hUIB hIP hIS (by rw [hS, hP]; exact hNe)
        | none => simp [hIP] at hP; exact absurd (innermostParentScope_of_sharedLoop hIS) (by simp [hIP])
      | none => simp [hIS] at hS; cases hIP : innermostParentScope engines body' p with
        | some innerP => simp [hIP] at hP; rw [← hS]; simp [scopeBodyOf]; rw [← hP]; exact innermostParentScope_mem_scopeIdsOf hIP
        | none => simp [hIP] at hP; exact absurd (hS.symm.trans hP) hNe
    · simp [hBoth] at hS; by_cases hInP : instrInBody engines body' p
      · exact absurd (hUIDisj p hInP) (by simp [innermostSharedScope_instrInBody_left hS])
      · simp [hInP] at hP; simp [scopeBodyOf, show lid ≠ sl from fun h => hNR (h ▸ innermostSharedScope_mem_scopeIdsOf hS),
              scopeBodyOf_none_of_not_mem (fun h => hDisj _ h (innermostSharedScope_mem_scopeIdsOf hS))]
        exact innermostParentScope_in_sharedLoop_body hUR hUIR hP hS hNe
  | engines, .cond thenId elseId b1 b2 :: rest, p, c, plid, sl, hU, hUI, hP, hS, hNe => by
    cases hU with | cond _ _ _ _ _ hNe' hTnTb hTnEb hTnR hEnTb hEnEb hEnR hTbDisj hEbDisj hUTb hUEb hUR =>
    cases hUI with | cond _ _ _ _ _ hUID12 hUID1R hUID2R hUITb hUIEb hUIR =>
    simp only [innermostParentScope] at hP; simp only [innermostSharedScope] at hS
    by_cases hInP1 : instrInBody engines b1 p
    · simp [hInP1] at hP
      have hNotB2 := hUID12 p hInP1; have hNotR := hUID1R p hInP1
      by_cases hIn1Both : instrInBody engines b1 p && instrInBody engines b1 c
      · simp [hIn1Both] at hS
        cases hIS : innermostSharedScope engines b1 p c with
        | some s1 =>
          simp [hIS] at hS
          have hSlB1 := innermostSharedScope_mem_scopeIdsOf hIS
          cases hIP : innermostParentScope engines b1 p with
          | some p1 =>
            simp [hIP] at hP
            rw [← hS]; simp [scopeBodyOf,
              show thenId ≠ s1 from fun h => hTnTb (h ▸ hSlB1),
              show elseId ≠ s1 from fun h => hEnTb (h ▸ hSlB1),
              scopeBodyOf_none_of_not_mem (fun h => (hTbDisj _ hSlB1).1 h),
              scopeBodyOf_none_of_not_mem (fun h => (hTbDisj _ hSlB1).2 h)]
            rw [← hP]; exact innermostParentScope_in_sharedLoop_body hUTb hUITb hIP hIS (by rw [hS, hP]; exact hNe)
          | none => simp [hIP] at hP; exact absurd (innermostParentScope_of_sharedLoop hIS) (by simp [hIP])
        | none => simp [hIS] at hS; cases hIP : innermostParentScope engines b1 p with
          | some p1 => simp [hIP] at hP; rw [← hS]; simp [scopeBodyOf]; rw [← hP]; exact innermostParentScope_mem_scopeIdsOf hIP
          | none => simp [hIP] at hP; exact absurd (hS.symm.trans hP) hNe
      · simp [hIn1Both] at hS; by_cases hIn2Both : instrInBody engines b2 p = true ∧ instrInBody engines b2 c = true
        · exfalso; exact absurd hIn2Both.1 (by simp [hNotB2])
        · simp [hIn2Both] at hS; exact absurd (innermostSharedScope_instrInBody_left hS) (by simp [hNotR])
    · simp [hInP1] at hP
      by_cases hInP2 : instrInBody engines b2 p
      · simp [hInP2] at hP
        have hNotR := hUID2R p hInP2
        have hNotB1Both : ¬(instrInBody engines b1 p && instrInBody engines b1 c) = true := by simp [hInP1]
        simp [hNotB1Both] at hS
        by_cases hIn2Both : instrInBody engines b2 p = true ∧ instrInBody engines b2 c = true
        · simp [hIn2Both] at hS
          cases hIS : innermostSharedScope engines b2 p c with
          | some s2 =>
            simp [hIS] at hS
            have hSlB2 := innermostSharedScope_mem_scopeIdsOf hIS
            cases hIP : innermostParentScope engines b2 p with
            | some p2 =>
              simp [hIP] at hP
              rw [← hS]; simp [scopeBodyOf,
                show thenId ≠ s2 from fun h => hTnEb (h ▸ hSlB2),
                show elseId ≠ s2 from fun h => hEnEb (h ▸ hSlB2),
                scopeBodyOf_none_of_not_mem (fun hc => (hTbDisj _ hc).1 hSlB2),
                scopeBodyOf_none_of_not_mem (fun h => hEbDisj _ hSlB2 h)]
              rw [← hP]; exact innermostParentScope_in_sharedLoop_body hUEb hUIEb hIP hIS (by rw [hS, hP]; exact hNe)
            | none => simp [hIP] at hP; exact absurd (innermostParentScope_of_sharedLoop hIS) (by simp [hIP])
          | none => simp [hIS] at hS; cases hIP : innermostParentScope engines b2 p with
            | some p2 => simp [hIP] at hP; rw [← hS]; simp [scopeBodyOf, hNe']; rw [← hP]; exact innermostParentScope_mem_scopeIdsOf hIP
            | none => simp [hIP] at hP; exact absurd (hS.symm.trans hP) hNe
        · simp [hIn2Both] at hS; exfalso; exact absurd (innermostSharedScope_instrInBody_left hS) (by simp [hNotR])
      · simp [hInP2] at hP
        have hInR := innermostParentScope_instrInBody hP
        have hNotB1Both : ¬(instrInBody engines b1 p && instrInBody engines b1 c) = true := by
          simp; intro h; exact absurd (hUID1R p h) (by simp [hInR])
        simp [hNotB1Both] at hS
        have hNotB2Both : ¬(instrInBody engines b2 p = true ∧ instrInBody engines b2 c = true) := by
          intro ⟨h, _⟩; exact absurd (hUID2R p h) (by simp [hInR])
        simp [hNotB2Both] at hS
        have hSlR := innermostSharedScope_mem_scopeIdsOf hS
        simp [scopeBodyOf,
          show thenId ≠ sl from fun h => hTnR (h ▸ hSlR),
          show elseId ≠ sl from fun h => hEnR (h ▸ hSlR),
          scopeBodyOf_none_of_not_mem (fun hc => (hTbDisj _ hc).2 hSlR),
          scopeBodyOf_none_of_not_mem (fun hc => hEbDisj _ hc hSlR)]
        exact innermostParentScope_in_sharedLoop_body hUR hUIR hP hS hNe

theorem instrInBody_of_getElem_rest {engines : List EngineId} {rest : List Stmt} {n : Nat} {stmt : Stmt} {p : DataPathInstrId}
    (hIdx : rest[n]? = some stmt) (hIn : instrInBody engines [stmt] p = true)
    : instrInBody engines rest p = true := by
  induction rest generalizing n with
  | nil => simp at hIdx
  | cons s rest' ih =>
    cases n with
    | zero => simp at hIdx; subst hIdx; cases s <;> simp_all [instrInBody]
    | succ m => simp at hIdx; have := ih hIdx; cases s <;> simp_all [instrInBody]

theorem uniqueInstrIds_of_scopeBodyOf : ∀ {engines : List EngineId} {body : List Stmt} {lid : ScopeId} {lb : List Stmt},
    UniqueInstrIds engines body → scopeBodyOf body lid = some lb → UniqueInstrIds engines lb
  | _, [], _, _, _, h => by simp [scopeBodyOf] at h
  | engines, .block _ :: rest, lid, lb, hUI, h => by
    cases hUI with | block _ _ _ _ _ hUIR =>
    simp [scopeBodyOf] at h; exact uniqueInstrIds_of_scopeBodyOf hUIR h
  | engines, .loop lid' body' :: rest, lid, lb, hUI, h => by
    cases hUI with | loop _ _ _ _ hUIB hUIR =>
    simp [scopeBodyOf] at h
    by_cases heq : lid' = lid
    · simp [heq] at h; subst h; exact hUIB
    · simp [heq] at h
      cases hb : scopeBodyOf body' lid with
      | some val => simp [hb] at h; subst h; exact uniqueInstrIds_of_scopeBodyOf hUIB hb
      | none => simp [hb] at h; exact uniqueInstrIds_of_scopeBodyOf hUIR h
  | engines, .cond thenId elseId b1 b2 :: rest, lid, lb, hUI, h => by
    cases hUI with | cond _ _ _ _ _ hD12 hD1R hD2R hUITb hUIEb hUIR =>
    simp [scopeBodyOf] at h
    by_cases ht : thenId = lid
    · simp [ht] at h; subst h; exact hUITb
    · simp [ht] at h
      by_cases he : elseId = lid
      · simp [he] at h; subst h; exact hUIEb
      · simp [he] at h
        cases hb1 : scopeBodyOf b1 lid with
        | some val => simp [hb1] at h; subst h; exact uniqueInstrIds_of_scopeBodyOf hUITb hb1
        | none =>
          simp [hb1] at h
          cases hb2 : scopeBodyOf b2 lid with
          | some val => simp [hb2] at h; subst h; exact uniqueInstrIds_of_scopeBodyOf hUIEb hb2
          | none => simp [hb2] at h; exact uniqueInstrIds_of_scopeBodyOf hUIR h

theorem uniqueInstrIds_unique_index {engines : List EngineId} {body : List Stmt}
    {p : DataPathInstrId} {i j : Nat} {si sj : Stmt}
    (hUI : UniqueInstrIds engines body)
    (hi : body[i]? = some si) (hj : body[j]? = some sj)
    (hIni : instrInBody engines [si] p = true)
    (hInj : instrInBody engines [sj] p = true)
    : i = j := by
  induction body generalizing i j with
  | nil => simp at hi
  | cons s rest ih =>
    have hUIR : UniqueInstrIds engines rest := by cases hUI <;> assumption
    -- Cross-index contradiction helper
    have hCross : ∀ {a : Nat} {sa : Stmt}, rest[a]? = some sa →
        instrInBody engines [sa] p = true → instrInBody engines [s] p = true → False := by
      intro a sa ha hIna hIns; have hR := instrInBody_of_getElem_rest ha hIna
      cases hUI with
      | block | loop => simp_all [instrInBody]
      | cond _ _ _ _ _ _ hD1R hD2R => simp [instrInBody] at hIns; rcases hIns with h | h <;> exact absurd hR (by first | simp [hD1R p h] | simp [hD2R p h])
    cases i with
    | zero => cases j with | zero => rfl | succ m => exfalso; simp at hi; subst hi; exact hCross (by simpa using hj) hInj hIni
    | succ n => cases j with
      | zero => exfalso; simp at hj; subst hj; exact hCross (by simpa using hi) hIni hInj
      | succ m => simp at hi hj; congr 1; exact ih hUIR hi hj

theorem instrInBody_of_scopeBodyOf : ∀ {engines : List EngineId} {body : List Stmt}
    {sl : ScopeId} {lb : List Stmt} {p : DataPathInstrId},
    scopeBodyOf body sl = some lb → instrInBody engines lb p = true →
    instrInBody engines body p = true
  | _, [], _, _, _, hLB, _ => by simp [scopeBodyOf] at hLB
  | engines, .block _ :: rest, sl, lb, p, hLB, hIn => by
    simp [scopeBodyOf] at hLB; simp [instrInBody]; right; exact instrInBody_of_scopeBodyOf hLB hIn
  | engines, .loop lid body' :: rest, sl, lb, p, hLB, hIn => by
    simp [scopeBodyOf] at hLB; simp [instrInBody]
    by_cases heq : lid = sl
    · simp [heq] at hLB; subst hLB; left; exact hIn
    · simp [heq] at hLB; cases hb : scopeBodyOf body' sl <;> simp [hb] at hLB
      · right; exact instrInBody_of_scopeBodyOf hLB hIn
      · subst hLB; left; exact instrInBody_of_scopeBodyOf hb hIn
  | engines, .cond thenId elseId b1 b2 :: rest, sl, lb, p, hLB, hIn => by
    simp [scopeBodyOf] at hLB; simp [instrInBody]
    by_cases ht : thenId = sl
    · simp [ht] at hLB; subst hLB; left; left; exact hIn
    · simp [ht] at hLB; by_cases he : elseId = sl
      · simp [he] at hLB; subst hLB; left; right; exact hIn
      · simp [he] at hLB; cases hb1 : scopeBodyOf b1 sl <;> simp [hb1] at hLB
        · cases hb2 : scopeBodyOf b2 sl <;> simp [hb2] at hLB
          · right; exact instrInBody_of_scopeBodyOf hLB hIn
          · subst hLB; left; right; exact instrInBody_of_scopeBodyOf hb2 hIn
        · subst hLB; left; left; exact instrInBody_of_scopeBodyOf hb1 hIn

private theorem innermostParentScope_ne_none_of_scopeBodyOf : ∀ {engines : List EngineId} {body : List Stmt}
    {sl : ScopeId} {lb : List Stmt} {p : DataPathInstrId},
    scopeBodyOf body sl = some lb → instrInBody engines lb p = true →
    ∃ plid, innermostParentScope engines body p = some plid
  | _, [], _, _, _, hLB, _ => by simp [scopeBodyOf] at hLB
  | engines, .block _ :: rest, sl, lb, p, hLB, hIn => by
    simp [scopeBodyOf] at hLB; simp
    exact innermostParentScope_ne_none_of_scopeBodyOf hLB hIn
  | engines, .loop lid body' :: rest, sl, lb, p, hLB, hIn => by
    simp only [scopeBodyOf] at hLB; simp only [innermostParentScope]
    by_cases heq : lid = sl
    · subst heq; simp at hLB; rw [← hLB] at hIn
      simp [hIn]; cases innermostParentScope engines body' p <;> simp
    · simp [heq] at hLB
      cases hb : scopeBodyOf body' sl with
      | some val =>
        simp [hb] at hLB; subst hLB
        have hInB := instrInBody_of_scopeBodyOf hb hIn; simp [hInB]
        cases innermostParentScope engines body' p <;> simp
      | none =>
        simp [hb] at hLB; by_cases hInB : instrInBody engines body' p = true
        · simp [hInB]; cases innermostParentScope engines body' p <;> simp
        · simp [show instrInBody engines body' p = false from by simp_all]
          exact innermostParentScope_ne_none_of_scopeBodyOf hLB hIn
  | engines, .cond thenId elseId b1 b2 :: rest, sl, lb, p, hLB, hIn => by
    simp only [scopeBodyOf] at hLB; simp only [innermostParentScope]
    by_cases ht : thenId = sl
    · subst ht; simp at hLB; rw [← hLB] at hIn; simp [hIn]; cases innermostParentScope engines b1 p <;> simp
    · simp [ht] at hLB
      by_cases he : elseId = sl
      · subst he; simp at hLB; rw [← hLB] at hIn
        by_cases hIn1 : instrInBody engines b1 p
        · simp [hIn1]; cases innermostParentScope engines b1 p <;> simp
        · simp [hIn1, hIn]; cases innermostParentScope engines b2 p <;> simp
      · simp [he] at hLB
        cases hb1 : scopeBodyOf b1 sl with
        | some val =>
          simp [hb1] at hLB; subst hLB
          have hInB := instrInBody_of_scopeBodyOf hb1 hIn
          by_cases hIn1 : instrInBody engines b1 p
          · simp [hIn1]; cases innermostParentScope engines b1 p <;> simp
          · simp at hIn1; simp [hInB] at hIn1
        | none =>
          simp [hb1] at hLB
          cases hb2 : scopeBodyOf b2 sl with
          | some val =>
            simp [hb2] at hLB; subst hLB
            have hInB := instrInBody_of_scopeBodyOf hb2 hIn
            by_cases hIn1 : instrInBody engines b1 p
            · simp [hIn1]; cases innermostParentScope engines b1 p <;> simp
            · simp [hIn1, hInB]; cases innermostParentScope engines b2 p <;> simp
          | none =>
            simp [hb2] at hLB; by_cases hIn1 : instrInBody engines b1 p
            · simp [hIn1]; cases innermostParentScope engines b1 p <;> simp
            · simp [hIn1]; by_cases hIn2 : instrInBody engines b2 p
              · simp [hIn2]; cases innermostParentScope engines b2 p <;> simp
              · simp [hIn2]; exact innermostParentScope_ne_none_of_scopeBodyOf hLB hIn

theorem innermostParentScope_of_scopeBodyOf : ∀ {engines : List EngineId} {body : List Stmt}
    {p : DataPathInstrId} {plid sl : ScopeId} {lb : List Stmt},
    UniqueInstrIds engines body →
    UniqueScopeIds body →
    innermostParentScope engines body p = some plid →
    scopeBodyOf body sl = some lb →
    sl ≠ plid →
    instrInBody engines lb p = true →
    innermostParentScope engines lb p = some plid
  | _, [], _, _, _, _, _, _, hPL, _, _, _ => by simp at hPL
  | engines, .block _ :: rest, p, plid, sl, lb, hUI, hUL, hPL, hLB, hNe, hInLb => by
    cases hUI with | block _ _ _ _ _ hUIR =>
    cases hUL with | block _ _ hULR =>
    simp [scopeBodyOf] at hLB; simp at hPL
    exact innermostParentScope_of_scopeBodyOf hUIR hULR hPL hLB hNe hInLb
  | engines, .loop lid body' :: rest, p, plid, sl, lb, hUI, hUL, hPL, hLB, hNe, hInLb => by
    cases hUI with | loop _ _ _ hDI hUIB hUIR =>
    cases hUL with | loop _ _ _ hNB hNR hDL hULB hULR =>
    simp only [innermostParentScope] at hPL; simp only [scopeBodyOf] at hLB
    by_cases heq : lid = sl
    · subst heq; simp at hLB; rw [← hLB] at hInLb
      simp [hInLb] at hPL
      cases hIP : innermostParentScope engines body' p with
      | some inner => simp [hIP] at hPL; rw [← hPL, ← hLB]; exact hIP
      | none => simp [hIP] at hPL; exact absurd hPL hNe
    · simp [heq] at hLB; cases hb : scopeBodyOf body' sl with
      | some val =>
        simp [hb] at hLB; rw [← hLB] at hInLb
        have hInB := instrInBody_of_scopeBodyOf hb hInLb; simp [hInB] at hPL
        cases hIP : innermostParentScope engines body' p with
        | some inner => simp [hIP] at hPL; rw [← hPL, ← hLB]; exact innermostParentScope_of_scopeBodyOf hUIB hULB hIP hb (by rw [hPL]; exact hNe) hInLb
        | none => simp [hIP] at hPL; exact absurd (innermostParentScope_ne_none_of_scopeBodyOf hb hInLb) (by simp [hIP])
      | none =>
        simp [hb] at hLB; have hInR := instrInBody_of_scopeBodyOf hLB hInLb
        simp [show instrInBody engines body' p = false from by
          by_contra h; simp at h; exact absurd hInR (by simp [hDI p h])] at hPL
        exact innermostParentScope_of_scopeBodyOf hUIR hULR hPL hLB hNe hInLb
  | engines, .cond thenId elseId b1 b2 :: rest, p, plid, sl, lb, hUI, hUL, hPL, hLB, hNe, hInLb => by
    cases hUI with | cond _ _ _ _ _ hD12 hD1R hD2R hUITb hUIEb hUIR =>
    cases hUL with | cond _ _ _ _ _ _ hTnTb hTnEb hTnR hEnTb hEnEb hEnR hTbDisj hEbDisj hULTb hULEb hULR =>
    simp only [scopeBodyOf] at hLB; simp only [innermostParentScope] at hPL
    by_cases ht : thenId = sl
    · subst ht; simp at hLB; subst hLB
      simp [hInLb] at hPL
      cases hIP : innermostParentScope engines b1 p with
      | some p1 => simp_all
      | none => simp [hIP] at hPL; exact absurd hPL hNe
    · simp [ht] at hLB; by_cases he : elseId = sl
      · subst he; simp at hLB; subst hLB; by_cases hInP1 : instrInBody engines b1 p
        · exfalso; exact absurd hInLb (by simp [hD12 p hInP1])
        · simp [hInP1, hInLb] at hPL; cases hIP : innermostParentScope engines b2 p with
          | some p2 => simp_all
          | none => simp [hIP] at hPL; exact absurd hPL hNe
      · simp [he] at hLB; cases hb1 : scopeBodyOf b1 sl with
        | some val =>
          simp [hb1] at hLB; rw [← hLB] at hInLb
          have hInB1 := instrInBody_of_scopeBodyOf hb1 hInLb; simp [hInB1] at hPL
          cases hIP : innermostParentScope engines b1 p with
          | some p1 => simp [hIP] at hPL; rw [← hPL, ← hLB]; exact innermostParentScope_of_scopeBodyOf hUITb hULTb hIP hb1 (by rw [hPL]; exact hNe) hInLb
          | none => simp [hIP] at hPL; exact absurd (innermostParentScope_ne_none_of_scopeBodyOf hb1 hInLb) (by simp [hIP])
        | none => simp [hb1] at hLB; cases hb2 : scopeBodyOf b2 sl with
          | some val =>
            simp [hb2] at hLB; rw [← hLB] at hInLb
            have hInB2 := instrInBody_of_scopeBodyOf hb2 hInLb
            by_cases hInP1 : instrInBody engines b1 p
            · simp [hInP1] at hPL; exact absurd hInB2 (by simp [hD12 p hInP1])
            · simp [hInP1, hInB2] at hPL; cases hIP : innermostParentScope engines b2 p with
              | some p2 => simp [hIP] at hPL; rw [← hPL, ← hLB]; exact innermostParentScope_of_scopeBodyOf hUIEb hULEb hIP hb2 (by rw [hPL]; exact hNe) hInLb
              | none => simp [hIP] at hPL; exact absurd (innermostParentScope_ne_none_of_scopeBodyOf hb2 hInLb) (by simp [hIP])
          | none =>
            simp [hb2] at hLB; have hInR := instrInBody_of_scopeBodyOf hLB hInLb
            by_cases hInP1 : instrInBody engines b1 p
            · simp [hInP1] at hPL; exact absurd hInR (by simp [hD1R p hInP1])
            · simp [hInP1] at hPL; by_cases hInP2 : instrInBody engines b2 p
              · simp [hInP2] at hPL; exact absurd hInR (by simp [hD2R p hInP2])
              · simp [hInP2] at hPL; exact innermostParentScope_of_scopeBodyOf hUIR hULR hPL hLB hNe hInLb

theorem innermostParentScope_at_stmt : ∀ {engines : List EngineId} {body : List Stmt}
    {p : DataPathInstrId} {plid : ScopeId} {i : Nat} {stmt : Stmt},
    UniqueInstrIds engines body →
    innermostParentScope engines body p = some plid →
    body[i]? = some stmt →
    instrInBody engines [stmt] p = true →
    plid ∈ scopeIdsOf [stmt]
  | _, [], _, _, _, _, _, hP, _, _ => by simp at hP
  | engines, .block f :: rest, p, plid, 0, stmt, hUI, hP, hIdx, hIn => by
    cases hUI with | block _ _ _ _ hD hUIR =>
    simp at hIdx; subst hIdx; simp at hP
    exact absurd (innermostParentScope_instrInBody hP) (by simp [hD p (by simp [instrInBody] at hIn; exact hIn)])
  | engines, .block f :: rest, p, plid, n + 1, stmt, hUI, hP, hIdx, hIn => by
    cases hUI with | block _ _ _ _ hD hUIR =>
    simp at hIdx; simp at hP; exact innermostParentScope_at_stmt hUIR hP hIdx hIn
  | engines, .loop lid body' :: rest, p, plid, 0, stmt, hUI, hP, hIdx, hIn => by
    cases hUI with | loop _ _ _ hD hUIB hUIR =>
    simp at hIdx; subst hIdx; simp only [innermostParentScope] at hP
    by_cases hInB : instrInBody engines body' p = true
    · simp [hInB] at hP
      cases hIP : innermostParentScope engines body' p with
      | none => simp [hIP] at hP; subst hP; simp [scopeIdsOf]
      | some inner => simp [hIP] at hP; subst hP; simp [scopeIdsOf]; right; exact innermostParentScope_mem_scopeIdsOf hIP
    · simp [hInB] at hP; exact absurd (innermostParentScope_instrInBody hP) (by simp [hD p (by simp [instrInBody] at hIn; exact hIn)])
  | engines, .loop lid body' :: rest, p, plid, n + 1, stmt, hUI, hP, hIdx, hIn => by
    cases hUI with | loop _ _ _ hD hUIB hUIR =>
    simp at hIdx; simp only [innermostParentScope] at hP
    have hInRest := instrInBody_of_getElem_rest hIdx hIn
    by_cases hInB : instrInBody engines body' p = true
    · exact absurd hInRest (by simp [hD p hInB])
    · simp [hInB] at hP; exact innermostParentScope_at_stmt hUIR hP hIdx hIn
  | engines, .cond thenId elseId b1 b2 :: rest, p, plid, 0, stmt, hUI, hP, hIdx, hIn => by
    cases hUI with | cond _ _ _ _ _ hD12 hD1R hD2R hUITb hUIEb hUIR =>
    simp at hIdx; subst hIdx; simp only [innermostParentScope] at hP
    by_cases hInB1 : instrInBody engines b1 p
    · simp [hInB1] at hP
      cases hIP : innermostParentScope engines b1 p with
      | none => simp [hIP] at hP; subst hP; simp [scopeIdsOf]
      | some p1 => simp [hIP] at hP; subst hP; simp [scopeIdsOf, innermostParentScope_mem_scopeIdsOf hIP]
    · simp [hInB1] at hP
      by_cases hInB2 : instrInBody engines b2 p
      · simp [hInB2] at hP
        cases hIP : innermostParentScope engines b2 p with
        | none => simp [hIP] at hP; subst hP; simp [scopeIdsOf]
        | some p2 => simp [hIP] at hP; subst hP; simp [scopeIdsOf, innermostParentScope_mem_scopeIdsOf hIP]
      · simp [hInB2] at hP; simp [instrInBody] at hIn; rcases hIn with h | h <;>
          exact absurd (innermostParentScope_instrInBody hP) (by first | simp [hD1R p h] | simp [hD2R p h])
  | engines, .cond thenId elseId b1 b2 :: rest, p, plid, n + 1, stmt, hUI, hP, hIdx, hIn => by
    cases hUI with | cond _ _ _ _ _ hD12 hD1R hD2R hUITb hUIEb hUIR =>
    simp at hIdx; simp only [innermostParentScope] at hP
    have hInRest := instrInBody_of_getElem_rest hIdx hIn
    by_cases hInB1 : instrInBody engines b1 p
    · exact absurd hInRest (by simp [hD1R p hInB1])
    · simp [hInB1] at hP
      by_cases hInB2 : instrInBody engines b2 p
      · exact absurd hInRest (by simp [hD2R p hInB2])
      · simp [hInB2] at hP; exact innermostParentScope_at_stmt hUIR hP hIdx hIn

private theorem findInBlock_mem_and_in {engs : List EngineId} {f : EngineId → List DataPathInstrId}
    {instr : DataPathInstrId} {eng : EngineId}
    (hfb : findInBlock engs f instr = some eng) : eng ∈ engs ∧ instr ∈ f eng := by
  induction engs with
  | nil => simp [findInBlock] at hfb
  | cons x xs ih =>
    simp [findInBlock] at hfb
    by_cases hx : instr ∈ f x
    · simp [hx] at hfb; subst hfb; exact ⟨List.Mem.head _, hx⟩
    · simp [hx] at hfb; have ⟨hm, hi⟩ := ih hfb; exact ⟨List.Mem.tail _ hm, hi⟩

theorem findInBlock_eq_of_mem {engines : List EngineId} {f : EngineId → List DataPathInstrId}
    {e : EngineId} {instr : DataPathInstrId} {eng : EngineId}
    (hE : e ∈ engines) (hIn : instr ∈ f e)
    (hFIB : findInBlock engines f instr = some eng)
    (hSingle : ∀ instr' e1 e2, e1 ∈ engines → e2 ∈ engines →
      instr' ∈ f e1 → instr' ∈ f e2 → e1 = e2)
    : eng = e := by
  have ⟨hEngMem, hInEng⟩ := findInBlock_mem_and_in hFIB
  exact hSingle instr eng e hEngMem hE hInEng hIn

/-! ## Step-reduction lemmas for instrEngine -/

theorem instrEngine_block :
    instrEngine engines (Stmt.block f :: rest) instr =
    (findInBlock engines f instr).orElse (fun _ => instrEngine engines rest instr) := by
  simp [instrEngine]; cases findInBlock engines f instr <;> simp

theorem instrEngine_loop :
    instrEngine engines (Stmt.loop lid body' :: rest) instr =
    (instrEngine engines body' instr).orElse (fun _ => instrEngine engines rest instr) := by
  simp [instrEngine]; cases instrEngine engines body' instr <;> simp

theorem instrEngine_cond :
    instrEngine engines (Stmt.cond thenId elseId tb eb :: rest) instr =
    ((instrEngine engines tb instr).orElse (fun _ => instrEngine engines eb instr)).orElse
      (fun _ => instrEngine engines rest instr) := by
  simp [instrEngine]
  cases instrEngine engines tb instr <;> simp
  cases instrEngine engines eb instr <;> simp

theorem instrEngine_none_of_not_in_body : ∀ {engines : List EngineId}
    {body : List Stmt} {instr : DataPathInstrId},
    instrInBody engines body instr = false →
    instrEngine engines body instr = none
  | _, [], _, _ => by simp [instrEngine]
  | engines, .block f :: rest, instr, h => by
    simp only [instrInBody, Bool.or_eq_false_iff] at h; rw [instrEngine_block]
    cases hfb : findInBlock engines f instr with
    | none => simp [Option.orElse]; exact instrEngine_none_of_not_in_body h.2
    | some e => simp [hfb] at h
  | engines, .loop lid body' :: rest, instr, h => by
    simp only [instrInBody, Bool.or_eq_false_iff] at h; rw [instrEngine_loop]
    simp [instrEngine_none_of_not_in_body h.1, Option.orElse]; exact instrEngine_none_of_not_in_body h.2
  | engines, .cond t e tb eb :: rest, instr, h => by
    simp only [instrInBody, Bool.or_eq_false_iff] at h; rw [instrEngine_cond]
    simp [instrEngine_none_of_not_in_body h.1.1, instrEngine_none_of_not_in_body h.1.2, Option.orElse]
    exact instrEngine_none_of_not_in_body h.2

theorem not_instrInBody_head_of_instrInBody_rest {engines : List EngineId}
    {s : Stmt} {rest : List Stmt} {instr : DataPathInstrId}
    (hUI : UniqueInstrIds engines (s :: rest))
    (hInRest : instrInBody engines rest instr = true)
    : instrInBody engines [s] instr = false := by
  by_contra hc; simp at hc; cases hUI with
  | block | loop => simp_all [instrInBody]
  | cond _ _ _ _ _ _ hDisjTR hDisjER => simp [instrInBody] at hc; rcases hc with h | h <;> simp_all

theorem instrEngine_of_getElem_rest {engines : List EngineId}
    {body : List Stmt} {n : Nat} {stmt : Stmt} {instr : DataPathInstrId} {e : EngineId}
    (hIdx : body[n]? = some stmt) (hIE : instrEngine engines [stmt] instr = some e)
    (hUI : UniqueInstrIds engines body)
    : instrEngine engines body instr = some e := by
  induction body generalizing n with
  | nil => simp at hIdx
  | cons s rest ih =>
    cases n with
    | zero =>
      simp at hIdx; subst hIdx
      cases s with
      | block f =>
        rw [instrEngine_block]; simp [instrEngine] at hIE
        cases hfb : findInBlock engines f instr
        · simp [hfb] at hIE
        · simp [Option.orElse, hfb] at hIE ⊢; exact hIE
      | loop lid body' =>
        rw [instrEngine_loop]; simp [instrEngine] at hIE
        cases hie : instrEngine engines body' instr
        · simp [hie] at hIE
        · simp [Option.orElse, hie] at hIE ⊢; exact hIE
      | cond tid eid tb eb =>
        rw [instrEngine_cond]; simp [instrEngine] at hIE
        cases hie1 : instrEngine engines tb instr
        · simp [hie1] at hIE
          cases hie2 : instrEngine engines eb instr
          · simp [hie2] at hIE
          · simp [Option.orElse, hie2] at hIE ⊢; exact hIE
        · simp [Option.orElse, hie1] at hIE ⊢; exact hIE
    | succ m =>
      simp at hIdx
      have hUIR : UniqueInstrIds engines rest := by cases hUI <;> assumption
      have ihR := ih hIdx hUIR
      have hInRest : instrInBody engines rest instr = true := by
        by_contra hc; simp at hc; exact absurd ihR (by rw [instrEngine_none_of_not_in_body hc]; simp)
      have hNotInS := not_instrInBody_head_of_instrInBody_rest hUI hInRest
      cases s with
      | block f => rw [instrEngine_block]; simp [instrInBody] at hNotInS; cases h : findInBlock engines f instr with | none => simp [Option.orElse]; exact ihR | some => simp [h] at hNotInS
      | loop lid body' => rw [instrEngine_loop]; simp [instrInBody] at hNotInS; simp [Option.orElse, instrEngine_none_of_not_in_body hNotInS]; exact ihR
      | cond tid eid tb eb => rw [instrEngine_cond]; simp [instrInBody] at hNotInS; simp [Option.orElse, instrEngine_none_of_not_in_body hNotInS.1, instrEngine_none_of_not_in_body hNotInS.2]; exact ihR

theorem uniqueInstrIds_cond_instrDisjoint' {engines : List EngineId} {body : List Stmt}
    {idx : Nat} {thenId elseId : ScopeId} {tb eb : List Stmt}
    (hUI : UniqueInstrIds engines body) (hIdx : body[idx]? = some (Stmt.cond thenId elseId tb eb))
    {instr : DataPathInstrId} (hInEb : instrInBody engines eb instr = true)
    : instrInBody engines tb instr = false := by
  induction hUI generalizing idx with
  | nil => simp at hIdx
  | block _ _ _ _ _ _ ih => cases idx <;> aesop
  | loop _ _ _ _ _ _ _ ih_rest => cases idx <;> aesop
  | cond _ _ _ _ _ hD12 _ _ _ _ _ _ _ ih_rest =>
    cases idx with
    | zero =>
      simp at hIdx; obtain ⟨rfl, rfl, rfl, rfl⟩ := hIdx
      by_contra h; simp at h
      exact absurd (hD12 instr h) (by simp; exact hInEb)
    | succ n => simp at hIdx; exact ih_rest hIdx

/-! ## instrsBefore: count instructions in blocks before a given statement index -/

def instrsBefore (engines : List EngineId) (eng : EngineId) : List Stmt → Nat → Nat
  | [], _ => 0
  | _, 0 => 0
  | Stmt.block f :: rest, n + 1 => (f eng).length + instrsBefore engines eng rest n
  | Stmt.loop _ _ :: rest, n + 1
  | Stmt.cond _ _ _ _ :: rest, n + 1 => instrsBefore engines eng rest n

/-! ### scopeParent.go helper lemmas for backward simulation -/

/-- scopeParent.go returns none when target is not in scopeIdsOf body. -/
theorem scopeParent_go_none_of_not_mem {body : List Stmt} (target : ScopeId)
    (container : Option ScopeId) (hNotIn : target ∉ scopeIdsOf body) (hUniq : UniqueScopeIds body)
    : scopeParent.go body target container = none := by
  induction hUniq generalizing target container with
  | nil => simp [scopeParent.go]
  | block _ _ _ ih =>
    simp only [scopeParent.go]; exact ih target container (by simp [scopeIdsOf] at hNotIn; exact hNotIn)
  | loop lid body' rest hNotBody hNotRest hDisj hBody hRest ih_body ih_rest =>
    simp only [scopeParent.go,
      show lid ≠ target from fun h => hNotIn (by rw [scopeIdsOf]; exact List.mem_cons.mpr (Or.inl h.symm)),
      ite_false]
    rw [ih_body target (some lid) (fun h => hNotIn (by rw [scopeIdsOf]; exact List.mem_cons_of_mem _ (List.mem_append_left _ h)))]; simp
    exact ih_rest target container (fun h => hNotIn (by rw [scopeIdsOf]; exact List.mem_cons_of_mem _ (List.mem_append_right _ h)))
  | cond thenId elseId tb eb rest _ _ _ hTnR _ _ hEnR hTbDisj hEbDisj _ _ _ ih_tb ih_eb ih_rest =>
    simp only [scopeParent.go,
      show thenId ≠ target from fun h => hNotIn (by rw [scopeIdsOf]; exact List.mem_cons.mpr (Or.inl h.symm)),
      show elseId ≠ target from fun h => hNotIn (by rw [scopeIdsOf]; exact List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl h.symm))),
      ite_false]
    rw [ih_tb target (some thenId) (fun h => hNotIn (by rw [scopeIdsOf]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ h)))))]; simp
    rw [ih_eb target (some elseId) (fun h => hNotIn (by rw [scopeIdsOf]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _ h)))))]; simp
    exact ih_rest target container (fun h => hNotIn (by rw [scopeIdsOf]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ h))))

/-- If sid appears as a direct loop at body[idx]?, scopeParent.go returns the container. -/
theorem scopeParent_go_of_direct_loop {body : List Stmt} {idx : Nat}
    {sid : ScopeId} {loopBody : List Stmt} {container : Option ScopeId}
    (hIdx : body[idx]? = some (Stmt.loop sid loopBody)) (hUniq : UniqueScopeIds body)
    : scopeParent.go body sid container = container := by
  induction hUniq generalizing idx with
  | nil => simp at hIdx
  | block _ _ _ ih =>
    cases idx with | zero => simp at hIdx | succ n => simp at hIdx; simp [scopeParent.go]; exact ih hIdx
  | loop lid' body' rest' hNotBody hNotRest hDisj hBody hRest ih_body ih_rest =>
    cases idx with
    | zero => simp at hIdx; obtain ⟨rfl, rfl⟩ := hIdx; simp [scopeParent.go]
    | succ n =>
      simp at hIdx; simp only [scopeParent.go]
      have hR : sid ∈ scopeIdsOf rest' := mem_scopeIdsOf_of_getElem hIdx (by simp [scopeIdsOf])
      simp [show lid' ≠ sid from fun h => hNotRest (h ▸ hR)]
      rw [scopeParent_go_none_of_not_mem sid (some lid') (fun h => hDisj sid h hR) hBody]; simp
      exact ih_rest hIdx
  | cond thenId elseId tb eb rest _ _ _ hTnR _ _ hEnR hTbDisj hEbDisj hUTb hUEb _ _ _ ih_rest =>
    cases idx with
    | zero => simp at hIdx
    | succ n =>
      simp at hIdx; simp only [scopeParent.go]
      have hR : sid ∈ scopeIdsOf rest := mem_scopeIdsOf_of_getElem hIdx (by simp [scopeIdsOf])
      simp [show thenId ≠ sid from fun h => hTnR (h ▸ hR), show elseId ≠ sid from fun h => hEnR (h ▸ hR)]
      rw [scopeParent_go_none_of_not_mem sid (some thenId) (fun h => (hTbDisj sid h).2 hR) hUTb]; simp
      rw [scopeParent_go_none_of_not_mem sid (some elseId) (fun h => hEbDisj sid h hR) hUEb]; simp
      exact ih_rest hIdx

/-- If thenId appears as a direct cond loop at body[idx]?, scopeParent.go returns the container. -/
theorem scopeParent_go_of_direct_cond_then {body : List Stmt} {idx : Nat}
    {thenId elseId : ScopeId} {tb eb : List Stmt} {container : Option ScopeId}
    (hIdx : body[idx]? = some (Stmt.cond thenId elseId tb eb)) (hUniq : UniqueScopeIds body)
    : scopeParent.go body thenId container = container := by
  induction hUniq generalizing idx with
  | nil => simp at hIdx
  | block _ _ _ ih =>
    cases idx with | zero => simp at hIdx | succ n => simp at hIdx; simp [scopeParent.go]; exact ih hIdx
  | loop lid' body' rest' hNotBody hNotRest hDisj hBody hRest ih_body ih_rest =>
    cases idx with
    | zero => simp at hIdx
    | succ n =>
      simp at hIdx; simp only [scopeParent.go]
      have hR : thenId ∈ scopeIdsOf rest' := mem_scopeIdsOf_of_getElem hIdx (by simp [scopeIdsOf])
      simp [show lid' ≠ thenId from fun h => hNotRest (h ▸ hR)]
      rw [scopeParent_go_none_of_not_mem thenId (some lid') (fun h => hDisj thenId h hR) hBody]; simp
      exact ih_rest hIdx
  | cond thenId' elseId' _ _ rest _ _ _ hTnR _ _ hEnR hTbDisj hEbDisj hUTb hUEb _ _ _ ih_rest =>
    cases idx with
    | zero => simp at hIdx; obtain ⟨rfl, _, _, _⟩ := hIdx; simp [scopeParent.go]
    | succ n =>
      simp at hIdx; simp only [scopeParent.go]
      have hR : thenId ∈ scopeIdsOf rest := mem_scopeIdsOf_of_getElem hIdx (by simp [scopeIdsOf])
      simp [show thenId' ≠ thenId from fun h => hTnR (h ▸ hR), show elseId' ≠ thenId from fun h => hEnR (h ▸ hR)]
      rw [scopeParent_go_none_of_not_mem thenId (some thenId') (fun h => (hTbDisj thenId h).2 hR) hUTb]; simp
      rw [scopeParent_go_none_of_not_mem thenId (some elseId') (fun h => hEbDisj thenId h hR) hUEb]; simp
      exact ih_rest hIdx

/-- If elseId appears as a direct cond loop at body[idx]?, scopeParent.go returns the container. -/
theorem scopeParent_go_of_direct_cond_else {body : List Stmt} {idx : Nat}
    {thenId elseId : ScopeId} {tb eb : List Stmt} {container : Option ScopeId}
    (hIdx : body[idx]? = some (Stmt.cond thenId elseId tb eb)) (hUniq : UniqueScopeIds body)
    : scopeParent.go body elseId container = container := by
  induction hUniq generalizing idx with
  | nil => simp at hIdx
  | block _ _ _ ih =>
    cases idx with | zero => simp at hIdx | succ n => simp at hIdx; simp [scopeParent.go]; exact ih hIdx
  | loop lid' body' rest' hNotBody hNotRest hDisj hBody hRest ih_body ih_rest =>
    cases idx with
    | zero => simp at hIdx
    | succ n =>
      simp at hIdx; simp only [scopeParent.go]
      have hR : elseId ∈ scopeIdsOf rest' := mem_scopeIdsOf_of_getElem hIdx (by simp [scopeIdsOf])
      simp [show lid' ≠ elseId from fun h => hNotRest (h ▸ hR)]
      rw [scopeParent_go_none_of_not_mem elseId (some lid') (fun h => hDisj elseId h hR) hBody]; simp
      exact ih_rest hIdx
  | cond thenId' elseId' _ _ rest _ _ _ hTnR _ _ hEnR hTbDisj hEbDisj hUTb hUEb _ _ _ ih_rest =>
    cases idx with
    | zero => simp at hIdx; obtain ⟨rfl, rfl, _, _⟩ := hIdx; simp only [scopeParent.go]; split <;> rfl
    | succ n =>
      simp at hIdx; simp only [scopeParent.go]
      have hR : elseId ∈ scopeIdsOf rest := mem_scopeIdsOf_of_getElem hIdx (by simp [scopeIdsOf])
      simp [show thenId' ≠ elseId from fun h => hTnR (h ▸ hR), show elseId' ≠ elseId from fun h => hEnR (h ▸ hR)]
      rw [scopeParent_go_none_of_not_mem elseId (some thenId') (fun h => (hTbDisj elseId h).2 hR) hUTb]; simp
      rw [scopeParent_go_none_of_not_mem elseId (some elseId') (fun h => hEbDisj elseId h hR) hUEb]; simp
      exact ih_rest hIdx

/-- Lift scopeParent.go through a loop nesting level. -/
theorem scopeParent_go_lift_loop {body : List Stmt} {idx : Nat}
    {lid : ScopeId} {subBody : List Stmt}
    {target : ScopeId} {result : ScopeId} {container : Option ScopeId}
    (hIdx : body[idx]? = some (Stmt.loop lid subBody)) (hUniq : UniqueScopeIds body)
    (hInner : scopeParent.go subBody target (some lid) = some result)
    (hTargetInSub : target ∈ scopeIdsOf subBody)
    : scopeParent.go body target container = some result := by
  induction hUniq generalizing idx with
  | nil => simp at hIdx
  | block _ _ _ ih =>
    cases idx with | zero => simp at hIdx | succ n => simp at hIdx; simp [scopeParent.go]; exact ih hIdx
  | loop lid' body' rest' hNotBody hNotRest hDisj hBody hRest ih_body ih_rest =>
    cases idx with
    | zero =>
      simp at hIdx; obtain ⟨rfl, rfl⟩ := hIdx
      simp only [scopeParent.go, show lid' ≠ target from fun h => hNotBody (h ▸ hTargetInSub), ite_false, hInner]
    | succ n =>
      simp at hIdx
      have hR : target ∈ scopeIdsOf rest' :=
        mem_scopeIdsOf_of_getElem hIdx (by simp [scopeIdsOf]; right; exact hTargetInSub)
      simp only [scopeParent.go, show lid' ≠ target from fun h => hNotRest (h ▸ hR), ite_false]
      rw [scopeParent_go_none_of_not_mem target (some lid') (fun h => hDisj target h hR) hBody]; simp
      exact ih_rest hIdx
  | cond thenId' elseId' _ _ rest _ _ _ hTnR _ _ hEnR hTbDisj hEbDisj hUTb hUEb _ _ _ ih_rest =>
    cases idx with
    | zero => simp at hIdx
    | succ n =>
      simp at hIdx
      have hR : target ∈ scopeIdsOf rest :=
        mem_scopeIdsOf_of_getElem hIdx (by simp [scopeIdsOf]; right; exact hTargetInSub)
      simp only [scopeParent.go,
        show thenId' ≠ target from fun h => hTnR (h ▸ hR),
        show elseId' ≠ target from fun h => hEnR (h ▸ hR), ite_false]
      rw [scopeParent_go_none_of_not_mem target (some thenId') (fun h => (hTbDisj target h).2 hR) hUTb]; simp
      rw [scopeParent_go_none_of_not_mem target (some elseId') (fun h => hEbDisj target h hR) hUEb]; simp
      exact ih_rest hIdx

/-- Lift scopeParent.go through a cond-then nesting level. -/
theorem scopeParent_go_lift_cond_then {body : List Stmt} {idx : Nat}
    {thenId elseId : ScopeId} {thenBody elseBody : List Stmt}
    {target : ScopeId} {result : ScopeId} {container : Option ScopeId}
    (hIdx : body[idx]? = some (Stmt.cond thenId elseId thenBody elseBody)) (hUniq : UniqueScopeIds body)
    (hInner : scopeParent.go thenBody target (some thenId) = some result)
    (hIn : target ∈ scopeIdsOf thenBody)
    : scopeParent.go body target container = some result := by
  induction hUniq generalizing idx with
  | nil => simp at hIdx
  | block _ _ _ ih =>
    cases idx with | zero => simp at hIdx | succ n => simp at hIdx; simp [scopeParent.go]; exact ih hIdx
  | loop lid' body' rest' hNotBody hNotRest hDisj hBody hRest ih_body ih_rest =>
    cases idx with
    | zero => simp at hIdx
    | succ n =>
      simp at hIdx
      have hR : target ∈ scopeIdsOf rest' :=
        mem_scopeIdsOf_of_getElem hIdx (by simp [scopeIdsOf]; right; right; left; exact hIn)
      simp only [scopeParent.go, show lid' ≠ target from fun h => hNotRest (h ▸ hR), ite_false]
      rw [scopeParent_go_none_of_not_mem target (some lid') (fun h => hDisj target h hR) hBody]; simp
      exact ih_rest hIdx
  | cond thenId' elseId' _ _ rest _ hTnTb _ hTnR hEnTb _ hEnR hTbDisj hEbDisj hUTb hUEb _ _ _ ih_rest =>
    cases idx with
    | zero =>
      simp at hIdx; obtain ⟨rfl, rfl, rfl, rfl⟩ := hIdx
      simp only [scopeParent.go,
        show thenId' ≠ target from fun h => hTnTb (h ▸ hIn),
        show elseId' ≠ target from fun h => hEnTb (h ▸ hIn), ite_false, hInner]
    | succ n =>
      simp at hIdx
      have hR : target ∈ scopeIdsOf rest :=
        mem_scopeIdsOf_of_getElem hIdx (by simp [scopeIdsOf]; right; right; left; exact hIn)
      simp only [scopeParent.go,
        show thenId' ≠ target from fun h => hTnR (h ▸ hR),
        show elseId' ≠ target from fun h => hEnR (h ▸ hR), ite_false]
      rw [scopeParent_go_none_of_not_mem target (some thenId') (fun h => (hTbDisj target h).2 hR) hUTb]; simp
      rw [scopeParent_go_none_of_not_mem target (some elseId') (fun h => hEbDisj target h hR) hUEb]; simp
      exact ih_rest hIdx

/-- Lift scopeParent.go through a cond-else nesting level. -/
theorem scopeParent_go_lift_cond_else {body : List Stmt} {idx : Nat}
    {thenId elseId : ScopeId} {thenBody elseBody : List Stmt}
    {target : ScopeId} {result : ScopeId} {container : Option ScopeId}
    (hIdx : body[idx]? = some (Stmt.cond thenId elseId thenBody elseBody)) (hUniq : UniqueScopeIds body)
    (hInner : scopeParent.go elseBody target (some elseId) = some result)
    (hIn : target ∈ scopeIdsOf elseBody)
    : scopeParent.go body target container = some result := by
  induction hUniq generalizing idx with
  | nil => simp at hIdx
  | block _ _ _ ih =>
    cases idx with | zero => simp at hIdx | succ n => simp at hIdx; simp [scopeParent.go]; exact ih hIdx
  | loop lid' body' rest' hNotBody hNotRest hDisj hBody hRest ih_body ih_rest =>
    cases idx with
    | zero => simp at hIdx
    | succ n =>
      simp at hIdx; simp only [scopeParent.go]
      have hR : target ∈ scopeIdsOf rest' :=
        mem_scopeIdsOf_of_getElem hIdx (by simp [scopeIdsOf]; right; right; right; assumption)
      simp only [show lid' ≠ target from fun h => hNotRest (h ▸ hR), ite_false]
      rw [scopeParent_go_none_of_not_mem target (some lid') (fun h => hDisj target h hR) hBody]; simp
      exact ih_rest hIdx
  | cond thenId' elseId' _ _ rest _ _ hTnEb hTnR _ hEnEb hEnR hTbDisj hEbDisj hUTb hUEb _ _ _ ih_rest =>
    cases idx with
    | zero =>
      simp at hIdx; obtain ⟨rfl, rfl, rfl, rfl⟩ := hIdx
      simp only [scopeParent.go,
        show thenId' ≠ target from fun h => hTnEb (h ▸ hIn),
        show elseId' ≠ target from fun h => hEnEb (h ▸ hIn), ite_false]
      rw [scopeParent_go_none_of_not_mem target (some thenId') (fun h => (hTbDisj target h).1 hIn) hUTb]; simp
      rw [hInner]
    | succ n =>
      simp at hIdx; simp only [scopeParent.go]
      have hR : target ∈ scopeIdsOf rest :=
        mem_scopeIdsOf_of_getElem hIdx (by simp [scopeIdsOf]; right; right; right; assumption)
      simp only [show thenId' ≠ target from fun h => hTnR (h ▸ hR),
        show elseId' ≠ target from fun h => hEnR (h ▸ hR), ite_false]
      rw [scopeParent_go_none_of_not_mem target (some thenId') (fun h => (hTbDisj target h).2 hR) hUTb]; simp
      rw [scopeParent_go_none_of_not_mem target (some elseId') (fun h => hEbDisj target h hR) hUEb]; simp
      exact ih_rest hIdx
