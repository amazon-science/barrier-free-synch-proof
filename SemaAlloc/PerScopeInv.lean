import SemaAlloc.PerScopeAlloc
import Batteries

/-! # Per-Loop Invariant Definitions

These invariants are threaded through the backward simulation for per-loop allocation.
They enable proving `depSatisfied` at issue time via `perScope_lower_bound`.
-/

/-! ## findActiveFrame and scopeKBound -/

def findActiveFrame : List Frame → Option ScopeId → Option (Frame × Bool)
  | [], _ => none
  | [f], none =>
      match f.kind with
      | .top => some (f, true)
      | _ => none
  | [_], some _ => none
  | _ :: parent :: rest, none =>
      findActiveFrame (parent :: rest) none |>.map fun (f, _) => (f, false)
  | child :: parent :: rest, some sid =>
      match child.kind with
      | .loop sid' =>
          if sid' = sid then some (child, true)
          else findActiveFrame (parent :: rest) (some sid) |>.map fun (f, _) => (f, false)
      | .cond sid' =>
          if sid' = sid then some (child, true)
          else findActiveFrame (parent :: rest) (some sid) |>.map fun (f, _) => (f, false)
      | .top =>
          findActiveFrame (parent :: rest) (some sid) |>.map fun (f, _) => (f, false)

def scopeKBound (spec : Program) (ss : SpecState) (eng : EngineId) (loop : Option ScopeId) : Nat :=
  match findActiveFrame (ss.pc eng).stack loop with
  | some (frame, isTop) =>
      instrsBefore spec.engines eng frame.body frame.stmtIdx +
        (if isTop then
          match frame.body[frame.stmtIdx]? with
          | some (Stmt.block _) => (ss.pc eng).instrIdx
          | _ => 0
        else 0)
  | none => (scopeInstrs spec.engines eng spec.body loop).length

/-! ## Helper Definitions -/

def instrInInflight (instr : DataPathInstrId) : List (DataPathInstrId × Phase) → Bool
  | [] => false
  | (i, _) :: rest => i == instr || instrInInflight instr rest

def inflightCount (instr : DataPathInstrId) : List (DataPathInstrId × Phase) → Nat
  | [] => 0
  | (i, _) :: rest => (if i == instr then 1 else 0) + inflightCount instr rest

def countOccsBefore (instr : DataPathInstrId) : List (DataPathInstrId × Phase) → Nat → Nat
  | _, 0 => 0
  | [], _ => 0
  | (i, _) :: rest, n + 1 => (if i == instr then 1 else 0) + countOccsBefore instr rest n

def entryTag (instr : DataPathInstrId) (retireFn : DataPathInstrId → Nat)
    (queue : List (DataPathInstrId × Phase)) (pos : Nat) : Nat :=
  retireFn instr + countOccsBefore instr queue pos + 1

/-! ## Helper Lemmas -/

theorem instrInInflight_ne_head {instr hd : DataPathInstrId} {ph : Phase}
    {rest : List (DataPathInstrId × Phase)} (hne : instr ≠ hd)
    : instrInInflight instr ((hd, ph) :: rest) = instrInInflight instr rest := by
  simp [instrInInflight, beq_iff_eq, Ne.symm hne]

theorem inflightCount_cons (instr hd : DataPathInstrId) (ph : Phase) (rest : List (DataPathInstrId × Phase))
    : inflightCount instr ((hd, ph) :: rest) =
      (if hd == instr then 1 else 0) + inflightCount instr rest := by
  simp [inflightCount]

theorem inflightCount_zero_of_not_mem {instr : DataPathInstrId} {l : List (DataPathInstrId × Phase)}
    (h : instrInInflight instr l = false) : inflightCount instr l = 0 := by
  induction l with
  | nil => simp [inflightCount]
  | cons hd rest ih =>
    simp [instrInInflight, Bool.or_eq_false_iff] at h; simp [inflightCount, beq_iff_eq, h.1, ih h.2]

theorem inflightCount_pos_of_mem {instr : DataPathInstrId} {l : List (DataPathInstrId × Phase)}
    (h : instrInInflight instr l = true) : inflightCount instr l ≥ 1 := by
  induction l with
  | nil => simp [instrInInflight] at h
  | cons hd rest ih =>
    simp [instrInInflight] at h; simp [inflightCount]
    rcases h with rfl | h
    · simp []
    · have := ih h; omega

@[simp] theorem countOccsBefore_zero (instr : DataPathInstrId) (queue : List (DataPathInstrId × Phase))
    : countOccsBefore instr queue 0 = 0 := by
  cases queue <;> simp [countOccsBefore]


theorem first_occ_countOccsBefore_zero {j : DataPathInstrId} {queue : List (DataPathInstrId × Phase)}
    {q : Nat} {ph : Phase}
    (hq : queue[q]? = some (j, ph))
    (hFirst : ∀ q' (ph' : Phase), q' < q → queue[q']? = some (j, ph') → False)
    : countOccsBefore j queue q = 0 := by
  induction queue generalizing q with
  | nil => simp at hq
  | cons hd rest ih =>
    obtain ⟨hd_id, hd_ph⟩ := hd
    cases q with
    | zero => simp [countOccsBefore]
    | succ n =>
      simp only [countOccsBefore]
      have hne : ¬(hd_id == j) = true := by
        intro heq; rw [beq_iff_eq] at heq
        exact hFirst 0 hd_ph (Nat.zero_lt_succ _) (by simp [heq])
      simp [hne]
      exact ih (by simp [List.getElem?_cons_succ] at hq; exact hq)
        (fun q' ph' hlt hget => hFirst (q' + 1) ph' (by omega)
          (by simp [List.getElem?_cons_succ]; exact hget))

theorem exists_first_occ {j : DataPathInstrId} {queue : List (DataPathInstrId × Phase)}
    (h : instrInInflight j queue = true)
    : ∃ (q : Nat) (ph : Phase), queue[q]? = some (j, ph) ∧
        ∀ q' (ph' : Phase), q' < q → queue[q']? = some (j, ph') → False := by
  induction queue with
  | nil => simp [instrInInflight] at h
  | cons hd rest ih =>
    obtain ⟨hd_id, hd_ph⟩ := hd
    by_cases heq : hd_id = j
    · exact ⟨0, hd_ph, by simp [heq], fun q' _ hlt => by omega⟩
    · have hRest : instrInInflight j rest = true := by
        simp [instrInInflight, beq_iff_eq, heq] at h; exact h
      obtain ⟨q, ph, hq, hFirst⟩ := ih hRest
      refine ⟨q + 1, ph, by simp [List.getElem?_cons_succ, hq], fun q' ph' hlt hget => ?_⟩
      match q' with
      | 0 => simp at hget; exact heq hget.1
      | n + 1 => exact hFirst n ph' (by omega) (by simp [List.getElem?_cons_succ] at hget; exact hget)

/-! ## Invariant Definitions -/

def CountBalance (spec : Program) (ss : SpecState) (eng : EngineId) (loop : Option ScopeId) : Prop :=
  ∀ i, i ∈ scopeInstrs spec.engines eng spec.body loop →
    ss.rc i + inflightCount i (ss.inflight eng) ≤ totalEntriesOpt ss eng loop ∧
    ss.rc i + inflightCount i (ss.inflight eng) ≥ totalEntriesOpt ss eng loop - 1

def IssueOrder (spec : Program) (ss : SpecState) (eng : EngineId) (loop : Option ScopeId) : Prop :=
  let instrs := scopeInstrs spec.engines eng spec.body loop
  ∀ i j, i ∈ instrs → j ∈ instrs →
    instrs.idxOf i < instrs.idxOf j →
    ss.rc j + inflightCount j (ss.inflight eng) = totalEntriesOpt ss eng loop →
    ss.rc i + inflightCount i (ss.inflight eng) = totalEntriesOpt ss eng loop

def QueueOrdered (spec : Program) (ss : SpecState) (eng : EngineId) (loop : Option ScopeId) : Prop :=
  let instrs := scopeInstrs spec.engines eng spec.body loop
  ∀ (p q : Nat) (ip iq : DataPathInstrId) (pp pq : Phase),
    p < q →
    (ss.inflight eng)[p]? = some (ip, pp) →
    (ss.inflight eng)[q]? = some (iq, pq) →
    ip ∈ instrs → iq ∈ instrs →
    entryTag ip ss.rc (ss.inflight eng) p <
      entryTag iq ss.rc (ss.inflight eng) q ∨
    (entryTag ip ss.rc (ss.inflight eng) p =
      entryTag iq ss.rc (ss.inflight eng) q ∧
     instrs.idxOf ip < instrs.idxOf iq)

theorem headMinRC_of_queueOrdered (spec : Program) (ss : SpecState) (eng : EngineId)
    (loop : Option ScopeId)
    (h4 : QueueOrdered spec ss eng loop)
    (P : DataPathInstrId) (ph : Phase) (rest : List (DataPathInstrId × Phase))
    (hHead : ss.inflight eng = (P, ph) :: rest)
    (j : DataPathInstrId)
    (hjRest : instrInInflight j rest = true)
    (hP : P ∈ scopeInstrs spec.engines eng spec.body loop)
    (hj : j ∈ scopeInstrs spec.engines eng spec.body loop)
    : ss.rc P ≤ ss.rc j := by
  by_cases hjP : j = P
  · subst hjP; exact Nat.le_refl _
  · obtain ⟨q, phq, hqGet, hqFirst⟩ := exists_first_occ (show instrInInflight j (ss.inflight eng) = true by
      rw [hHead]; simp [instrInInflight]; right; exact hjRest)
    have hq_pos : q ≥ 1 := by
      by_contra hc; rw [show q = 0 by omega, hHead] at hqGet; simp at hqGet; exact hjP hqGet.1.symm
    have hOrd := h4 0 q P j ph phq (by omega) (by rw [hHead]; simp) hqGet hP hj
    simp only [entryTag, countOccsBefore_zero, first_occ_countOccsBefore_zero hqGet hqFirst] at hOrd; omega

def RCMono (spec : Program) (ss : SpecState) (eng : EngineId) (loop : Option ScopeId) : Prop :=
  let instrs := scopeInstrs spec.engines eng spec.body loop
  ∀ i j, i ∈ instrs → j ∈ instrs →
    instrs.idxOf i < instrs.idxOf j →
    ss.rc j ≤ ss.rc i

def RCBound (spec : Program) (ss : SpecState) (eng : EngineId) (loop : Option ScopeId) : Prop :=
  let instrs := scopeInstrs spec.engines eng spec.body loop
  ∀ i j, i ∈ instrs → j ∈ instrs →
    ss.rc i ≤ ss.rc j + 1

def PCComplete (spec : Program) (ss : SpecState) (eng : EngineId)
    (loop : Option ScopeId) (kBound : Nat) : Prop :=
  let instrs := scopeInstrs spec.engines eng spec.body loop
  ∀ i, i ∈ instrs → instrs.idxOf i < kBound →
    ss.rc i + inflightCount i (ss.inflight eng) = totalEntriesOpt ss eng loop

/-! ## Combined Invariant -/

structure PerScopeInv (spec : Program) (impl : ImplProgram) (alloc : PerScopeAllocR spec impl)
    (ss : SpecState) (is : ImplState) : Prop where
  semaInv : ∀ loop eng, eng ∈ spec.engines → is.semaphores (alloc.perScopeSema loop eng) =
    scopeRetireSum ss.rc spec.engines eng spec.body loop
  countBalance : ∀ eng loop, eng ∈ spec.engines → CountBalance spec ss eng loop
  issueOrder : ∀ eng loop, eng ∈ spec.engines → IssueOrder spec ss eng loop
  queueOrdered : ∀ eng loop, eng ∈ spec.engines → QueueOrdered spec ss eng loop
  rcMono : ∀ eng loop, eng ∈ spec.engines → RCMono spec ss eng loop
  rcBound : ∀ eng loop, eng ∈ spec.engines → RCBound spec ss eng loop
  pcComplete : ∀ eng loop, eng ∈ spec.engines →
    PCComplete spec ss eng loop (scopeKBound spec ss eng loop) ∧
    (∀ i, i ∈ scopeInstrs spec.engines eng spec.body loop →
      (scopeInstrs spec.engines eng spec.body loop).idxOf i ≥ scopeKBound spec ss eng loop →
      ss.rc i + inflightCount i (ss.inflight eng) =
        totalEntriesOpt ss eng loop - 1)
  instrAtPC_atTm1 : ∀ eng, eng ∈ spec.engines → ∀ frame rest f instr,
    (ss.pc eng).stack = frame :: rest →
    frame.body[frame.stmtIdx]? = some (Stmt.block f) →
    (f eng)[(ss.pc eng).instrIdx]? = some instr →
    ∀ loop, instr ∈ scopeInstrs spec.engines eng spec.body loop →
      ss.rc instr + inflightCount instr (ss.inflight eng) =
        totalEntriesOpt ss eng loop - 1

theorem nodup_idxOf_eq_of_mem {l : List α} [DecidableEq α] {a b : α}
    (_hnd : l.Nodup) (ha : a ∈ l) (hb : b ∈ l) (h : l.idxOf a = l.idxOf b) : a = b := by
  have ha' := List.idxOf_lt_length_of_mem ha
  have hb' := List.idxOf_lt_length_of_mem hb
  have := List.getElem_idxOf ha'
  have := List.getElem_idxOf hb'
  have : l[l.idxOf a] = l[l.idxOf b] := by simp [h]
  simp_all

theorem findActiveFrame_isTop_eq {frame : Frame} {rest : List Frame} {loop : Option ScopeId} {fr : Frame}
    (hfa : findActiveFrame (frame :: rest) loop = some (fr, true)) : fr = frame := by
  cases rest with
  | nil =>
    cases loop with
    | none =>
      simp only [findActiveFrame] at hfa
      cases hk : frame.kind <;> rw [hk] at hfa <;> simp at hfa
      exact hfa.symm
    | some => simp [findActiveFrame] at hfa
  | cons parent rest' =>
    cases loop with
    | none =>
      simp only [findActiveFrame] at hfa
      cases hfa' : findActiveFrame (parent :: rest') none <;> simp [hfa'] at hfa
    | some sid =>
      simp only [findActiveFrame] at hfa
      match hk : frame.kind with
      | .top =>
        rw [hk] at hfa
        cases hfa' : findActiveFrame (parent :: rest') (some sid) <;> simp [hfa'] at hfa
      | .loop sid' | .cond sid' =>
        rw [hk] at hfa; simp at hfa
        by_cases h : sid' = sid
        · simp [h] at hfa; exact hfa.symm
        · cases hfa' : findActiveFrame (parent :: rest') (some sid) with
          | none => simp [h, hfa'] at hfa
          | some val => obtain ⟨vfr, vb⟩ := val; simp [h, hfa'] at hfa


theorem findActiveFrame_change_stmtIdx {frame : Frame} {rest : List Frame} {newSi : Nat}
    {loop : Option ScopeId} :
    findActiveFrame (⟨frame.body, newSi, frame.kind⟩ :: rest) loop =
      (findActiveFrame (frame :: rest) loop).map fun (fr, isTop) =>
        if isTop then (⟨frame.body, newSi, frame.kind⟩, true) else (fr, false) := by
  cases rest with
  | nil =>
    cases loop with
    | none => cases hk : frame.kind <;> simp [findActiveFrame, hk]
    | some sid => simp [findActiveFrame]
  | cons parent rest' =>
    cases loop with
    | none =>
      simp only [findActiveFrame]
      cases hfa : findActiveFrame (parent :: rest') none with
      | none => simp [Option.map]
      | some fp => obtain ⟨fr, b⟩ := fp; simp [Option.map]
    | some sid =>
      cases hk : frame.kind <;> simp only [findActiveFrame, hk]
      · cases hfa : findActiveFrame (parent :: rest') (some sid) with
        | none => simp [Option.map]
        | some fp => obtain ⟨fr, b⟩ := fp; simp [Option.map]
      all_goals (
        rename_i sid'
        by_cases h : sid' = sid
        · simp [h]
        · simp [h]; cases hfa : findActiveFrame (parent :: rest') (some sid) with
          | none => simp [Option.map]
          | some fp => obtain ⟨fr, b⟩ := fp; simp [Option.map])

theorem scopeKBound_advance {spec : Program} {ss ss' : SpecState} {eng : EngineId}
    {frame : Frame} {rest : List Frame}
    (hStack : (ss.pc eng).stack = frame :: rest)
    (hPC' : ss'.pc eng = ⟨⟨frame.body, frame.stmtIdx + 1, frame.kind⟩ :: rest, 0⟩)
    (hKB : ∀ loop, match findActiveFrame (frame :: rest) loop with
      | some (_, true) =>
        instrsBefore spec.engines eng frame.body (frame.stmtIdx + 1) +
          (match frame.body[frame.stmtIdx + 1]? with | some (Stmt.block _) => 0 | _ => 0) =
        instrsBefore spec.engines eng frame.body frame.stmtIdx +
          (match frame.body[frame.stmtIdx]? with | some (Stmt.block _) => (ss.pc eng).instrIdx | _ => 0)
      | _ => True)
    : ∀ loop, scopeKBound spec ss' eng loop = scopeKBound spec ss eng loop := by
  intro loop
  simp only [scopeKBound, hPC', hStack]
  rw [findActiveFrame_change_stmtIdx]
  cases hfa : findActiveFrame (frame :: rest) loop with
  | none => simp [Option.map]
  | some fp =>
    obtain ⟨fr, isTop⟩ := fp
    simp only [Option.map]
    cases isTop with
    | false => simp
    | true =>
      simp only [ite_true]
      have hfr := findActiveFrame_isTop_eq hfa; subst hfr
      have hKB' := hKB loop; rw [hfa] at hKB'
      exact hKB'

/-! ## scopeKBound depends only on pc -/

theorem scopeKBound_eq_of_pc_eq {spec : Program} {ss ss' : SpecState} {eng : EngineId} {loop : Option ScopeId}
    (hPC : ss'.pc eng = ss.pc eng) :
    scopeKBound spec ss' eng loop = scopeKBound spec ss eng loop := by
  simp [scopeKBound, hPC]

theorem scopeKBound_funUpdate_ne {spec : Program} {ss : SpecState} {eng eng0 : EngineId} {loop : Option ScopeId}
    {newPC : PC} (hne : eng ≠ eng0) :
    scopeKBound spec { ss with pc := funUpdate ss.pc eng0 newPC } eng loop =
      scopeKBound spec ss eng loop := by
  apply scopeKBound_eq_of_pc_eq; simp [funUpdate, hne]

theorem scopeKBound_loopEntry_self {spec : Program} {ss : SpecState} {eng : EngineId}
    {sid : ScopeId} {loopBody : List Stmt} {kind : FrameKind}
    {frame : Frame} {rest : List Frame}
    (_hStack : (ss.pc eng).stack = frame :: rest)
    (hKind : kind = .loop sid ∨ kind = .cond sid)
    : scopeKBound spec
        { ss with pc := funUpdate ss.pc eng { stack := ⟨loopBody, 0, kind⟩ :: frame :: rest, instrIdx := 0 } }
        eng (some sid) = 0 := by
  simp only [scopeKBound, funUpdate, ite_true]
  rcases hKind with rfl | rfl <;> simp only [findActiveFrame, ite_true] <;> (
    show instrsBefore _ _ _ 0 + _ = 0
    simp only [show instrsBefore spec.engines eng loopBody 0 = 0 from by cases loopBody <;> simp [instrsBefore]]
    cases h : loopBody[0]? with
    | none => rfl
    | some s => cases s <;> rfl)

theorem scopeKBound_loopEntry_other {spec : Program} {ss : SpecState} {eng : EngineId}
    {sid : ScopeId} {loopBody : List Stmt} {kind : FrameKind}
    {frame : Frame} {rest : List Frame} {loop : Option ScopeId}
    (hStack : (ss.pc eng).stack = frame :: rest)
    (hKind : kind = .loop sid ∨ kind = .cond sid)
    (hLoop : loop ≠ some sid)
    (hNotBlock : ∀ f, frame.body[frame.stmtIdx]? ≠ some (Stmt.block f))
    : scopeKBound spec
        { ss with pc := funUpdate ss.pc eng { stack := ⟨loopBody, 0, kind⟩ :: frame :: rest, instrIdx := 0 } }
        eng loop = scopeKBound spec ss eng loop := by
  simp only [scopeKBound, funUpdate, ite_true, hStack]
  have hNotBlockAux :
      (match frame.body[frame.stmtIdx]? with | some (Stmt.block _) => (ss.pc eng).instrIdx | _ => 0) = 0 := by
    cases hbs : frame.body[frame.stmtIdx]? with
    | none => rfl
    | some s => cases s with
      | block f => exact absurd hbs (hNotBlock f)
      | loop _ _ => rfl
      | cond _ _ _ _ => rfl
  cases loop with
  | none =>
    rcases hKind with rfl | rfl <;> simp only [findActiveFrame] <;> (
      cases hfa : findActiveFrame (frame :: rest) none with
      | none => simp [Option.map]
      | some fp =>
        obtain ⟨fr, isTop⟩ := fp; simp only [Option.map]
        cases isTop with
        | false => simp
        | true => have hfr := findActiveFrame_isTop_eq hfa; subst hfr; simp)
  | some sid' =>
    have hne : sid' ≠ sid := fun h => hLoop (congrArg some h)
    rcases hKind with rfl | rfl <;> simp only [findActiveFrame, show sid ≠ sid' from Ne.symm hne, ite_false] <;> (
      cases hfa : findActiveFrame (frame :: rest) (some sid') with
      | none => simp [Option.map]
      | some fp =>
        obtain ⟨fr, isTop⟩ := fp; simp only [Option.map]
        cases isTop with
        | false => simp
        | true => have hfr := findActiveFrame_isTop_eq hfa; subst hfr; simp)

/-! ## Inv7 preservation helpers -/

theorem pcComplete_of_same_kBound {spec : Program} {ss ss' : SpecState} {eng : EngineId} {loop : Option ScopeId}
    (hKB : scopeKBound spec ss' eng loop = scopeKBound spec ss eng loop)
    (hRC : ss'.rc = ss.rc)
    (hIF : ss'.inflight eng = ss.inflight eng)
    (hTE : totalEntriesOpt ss' eng loop = totalEntriesOpt ss eng loop)
    (hFwd : PCComplete spec ss eng loop (scopeKBound spec ss eng loop))
    (hBack : ∀ i, i ∈ scopeInstrs spec.engines eng spec.body loop →
      (scopeInstrs spec.engines eng spec.body loop).idxOf i ≥ scopeKBound spec ss eng loop →
      ss.rc i + inflightCount i (ss.inflight eng) = totalEntriesOpt ss eng loop - 1)
    : PCComplete spec ss' eng loop (scopeKBound spec ss' eng loop) ∧
      (∀ i, i ∈ scopeInstrs spec.engines eng spec.body loop →
        (scopeInstrs spec.engines eng spec.body loop).idxOf i ≥ scopeKBound spec ss' eng loop →
        ss'.rc i + inflightCount i (ss'.inflight eng) = totalEntriesOpt ss' eng loop - 1) := by
  rw [hKB]
  exact ⟨fun i hi hlt => by rw [hRC, hIF, hTE]; exact hFwd i hi hlt,
         fun i hi hge => by rw [hRC, hIF, hTE]; exact hBack i hi hge⟩

/-! ## Monotonicity (SemaInv depends only on rc + semaphores) -/


/-! ## Retire Preservation Theorems -/



theorem inflightCount_append (instr : DataPathInstrId) (l1 l2 : List (DataPathInstrId × Phase))
    : inflightCount instr (l1 ++ l2) = inflightCount instr l1 + inflightCount instr l2 := by
  induction l1 with
  | nil => simp [inflightCount]
  | cons hd rest ih => simp [inflightCount, ih]; omega

theorem inflightCount_singleton (instr i : DataPathInstrId) (ph : Phase)
    : inflightCount instr [(i, ph)] = if i == instr then 1 else 0 := by
  simp [inflightCount]

theorem countOccsBefore_append_left (instr : DataPathInstrId) (l1 l2 : List (DataPathInstrId × Phase)) (p : Nat)
    (hp : p < l1.length)
    : countOccsBefore instr (l1 ++ l2) p = countOccsBefore instr l1 p := by
  induction l1 generalizing p with
  | nil => simp at hp
  | cons hd rest ih =>
    cases p with
    | zero => simp [countOccsBefore]
    | succ n => simp only [countOccsBefore, List.cons_append]; congr 1
                exact ih n (by simp [List.length_cons] at hp; omega)

theorem countOccsBefore_cons (instr hd : DataPathInstrId) (ph : Phase) (rest : List (DataPathInstrId × Phase)) (n : Nat)
    : countOccsBefore instr ((hd, ph) :: rest) (n + 1) =
      (if hd == instr then 1 else 0) + countOccsBefore instr rest n := by
  simp [countOccsBefore]

theorem inflightCount_set_phase (l : List (DataPathInstrId × Phase)) (n : Nat)
    (instr : DataPathInstrId) (ph ph' : Phase) (hGet : l[n]? = some (instr, ph))
    : ∀ i, inflightCount i (l.set n (instr, ph')) = inflightCount i l := by
  intro i; induction l generalizing n with
  | nil => simp [List.set, inflightCount]
  | cons hd rest ih =>
    cases n with
    | zero => simp only [List.set, List.getElem?_cons_zero, Option.some.injEq] at hGet ⊢
              obtain ⟨rfl, _⟩ := hGet; simp [inflightCount]
    | succ m => simp only [List.set, inflightCount, List.getElem?_cons_succ] at hGet ⊢
                congr 1; exact ih m hGet

theorem countOccsBefore_set_phase (l : List (DataPathInstrId × Phase)) (n : Nat)
    (instr : DataPathInstrId) (ph ph' : Phase) (hGet : l[n]? = some (instr, ph))
    : ∀ i p, countOccsBefore i (l.set n (instr, ph')) p = countOccsBefore i l p := by
  intro i p; induction l generalizing n p with
  | nil => simp [List.set]
  | cons hd rest ih =>
    cases n with
    | zero => cases p with
              | zero => simp [countOccsBefore]
              | succ m => simp only [List.set, List.getElem?_cons_zero, Option.some.injEq] at hGet ⊢
                          obtain ⟨rfl, _⟩ := hGet; simp [countOccsBefore]
    | succ k => cases p with
                | zero => simp [countOccsBefore]
                | succ m => simp only [List.set, countOccsBefore, List.getElem?_cons_succ] at hGet ⊢
                            congr 1; exact ih k hGet m

theorem getElem_set_phase_fst (l : List (DataPathInstrId × Phase)) (n : Nat)
    (instr : DataPathInstrId) (ph ph' : Phase) (hGet : l[n]? = some (instr, ph))
    (p : Nat) (ip : DataPathInstrId) (pp : Phase)
    (hLookup : (l.set n (instr, ph'))[p]? = some (ip, pp))
    : ∃ pp', l[p]? = some (ip, pp') := by
  simp [List.getElem?_set] at hLookup
  split at hLookup
  · rename_i heq; subst heq
    split at hLookup
    · obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj hLookup); exact ⟨ph, hGet⟩
    · simp at hLookup
  · exact ⟨pp, hLookup⟩

theorem entryTag_set_phase {retireFn : DataPathInstrId → Nat} (l : List (DataPathInstrId × Phase)) (n : Nat)
    (instr : DataPathInstrId) (ph ph' : Phase) (hGet : l[n]? = some (instr, ph))
    : ∀ i p, entryTag i retireFn (l.set n (instr, ph')) p = entryTag i retireFn l p := by
  intro i p; simp [entryTag, countOccsBefore_set_phase l n instr ph ph' hGet]

/-- The net effect of retire on `rc + inflightCount` is zero for all loop members. -/
private theorem retire_net_effect (spec : Program) (loop : Option ScopeId)
    {ss0 : SpecState} {e eng : EngineId}
    {instr : DataPathInstrId} {ph : Phase} {rest : List (DataPathInstrId × Phase)}
    (hHead : ss0.inflight e = (instr, ph) :: rest)
    (hInstrEng : eng ≠ e → instr ∉ scopeInstrs spec.engines eng spec.body loop)
    {i : DataPathInstrId} (hi : i ∈ scopeInstrs spec.engines eng spec.body loop)
    : funUpdate ss0.rc instr (ss0.rc instr + 1) i +
        inflightCount i (funUpdate ss0.inflight e rest eng) =
      ss0.rc i + inflightCount i (ss0.inflight eng) := by
  by_cases he : eng = e
  · subst he; simp only [funUpdate, ite_true]
    by_cases hxi : i = instr
    · subst hxi; simp; rw [hHead]; simp [inflightCount_cons]; omega
    · simp [if_neg hxi]; rw [hHead]; simp [inflightCount_cons, beq_eq_false_iff_ne.mpr (Ne.symm hxi)]
  · have hni : i ≠ instr := fun h => by subst h; exact hInstrEng he hi
    simp [funUpdate, he, hni]

theorem countBalance_retire (spec : Program) (ss0 : SpecState) (e : EngineId)
    (eng : EngineId) (loop : Option ScopeId)
    (instr : DataPathInstrId) (ph : Phase) (rest : List (DataPathInstrId × Phase))
    (hHead : ss0.inflight e = (instr, ph) :: rest)
    (hInv2 : CountBalance spec ss0 eng loop)
    (hInstrEng : eng ≠ e → instr ∉ scopeInstrs spec.engines eng spec.body loop)
    : CountBalance spec
        { ss0 with
          inflight := funUpdate ss0.inflight e rest
          rc := funUpdate ss0.rc instr (ss0.rc instr + 1) }
        eng loop := by
  intro i hi; have hOld := hInv2 i hi
  show funUpdate ss0.rc instr (ss0.rc instr + 1) i +
      inflightCount i (funUpdate ss0.inflight e rest eng) ≤ totalEntriesOpt ss0 eng loop ∧
    funUpdate ss0.rc instr (ss0.rc instr + 1) i +
      inflightCount i (funUpdate ss0.inflight e rest eng) ≥ totalEntriesOpt ss0 eng loop - 1
  rw [retire_net_effect spec loop hHead hInstrEng hi]; exact hOld

theorem issueOrder_retire (spec : Program) (ss0 : SpecState) (e : EngineId)
    (eng : EngineId) (loop : Option ScopeId)
    (instr : DataPathInstrId) (ph : Phase) (rest : List (DataPathInstrId × Phase))
    (hHead : ss0.inflight e = (instr, ph) :: rest)
    (hInv3 : IssueOrder spec ss0 eng loop)
    (_hInv2 : CountBalance spec ss0 eng loop)
    (hInstrEng : eng ≠ e → instr ∉ scopeInstrs spec.engines eng spec.body loop)
    : IssueOrder spec
        { ss0 with
          inflight := funUpdate ss0.inflight e rest
          rc := funUpdate ss0.rc instr (ss0.rc instr + 1) }
        eng loop := by
  intro i j hi hj hIdx hJT
  change funUpdate ss0.rc instr (ss0.rc instr + 1) i +
    inflightCount i (funUpdate ss0.inflight e rest eng) = totalEntriesOpt ss0 eng loop
  change funUpdate ss0.rc instr (ss0.rc instr + 1) j +
    inflightCount j (funUpdate ss0.inflight e rest eng) = totalEntriesOpt ss0 eng loop at hJT
  rw [retire_net_effect spec loop hHead hInstrEng hj] at hJT
  rw [retire_net_effect spec loop hHead hInstrEng hi]
  exact hInv3 i j hi hj hIdx hJT

theorem queueOrdered_retire (spec : Program) (ss0 : SpecState) (e : EngineId)
    (eng : EngineId) (loop : Option ScopeId)
    (instr : DataPathInstrId) (ph : Phase) (rest : List (DataPathInstrId × Phase))
    (hHead : ss0.inflight e = (instr, ph) :: rest)
    (hInv4 : QueueOrdered spec ss0 eng loop)
    (hInstrEng : eng ≠ e → instr ∉ scopeInstrs spec.engines eng spec.body loop)
    : QueueOrdered spec
        { ss0 with
          inflight := funUpdate ss0.inflight e rest
          rc := funUpdate ss0.rc instr (ss0.rc instr + 1) }
        eng loop := by
  unfold QueueOrdered; simp only
  intro p q ip iq pp pq hpq hGetP hGetQ hMemP hMemQ
  simp only [funUpdate_apply] at hGetP hGetQ ⊢
  by_cases he : eng = e
  · simp [he] at hGetP hGetQ ⊢; subst he
    have hTagEq : ∀ (i : DataPathInstrId) (n : Nat),
        entryTag i (funUpdate ss0.rc instr (ss0.rc instr + 1)) rest n =
        entryTag i ss0.rc ((instr, ph) :: rest) (n + 1) := by
      intro i n
      simp only [entryTag, countOccsBefore_cons, funUpdate_apply]
      by_cases hi : i = instr
      · simp [hi]; omega
      · simp [hi, beq_eq_false_iff_ne.mpr (Ne.symm hi)]
    rw [hTagEq ip p, hTagEq iq q]
    have hResult := hInv4 (p+1) (q+1) ip iq pp pq (by omega)
      (by rw [hHead]; simp [List.getElem?_cons_succ]; exact hGetP)
      (by rw [hHead]; simp [List.getElem?_cons_succ]; exact hGetQ) hMemP hMemQ
    rw [hHead] at hResult; exact hResult
  · simp [he] at hGetP hGetQ ⊢
    have hInstrNotEng := hInstrEng he
    have hip : ip ≠ instr := fun h => hInstrNotEng (h ▸ hMemP)
    have hiq : iq ≠ instr := fun h => hInstrNotEng (h ▸ hMemQ)
    have hResult := hInv4 p q ip iq pp pq hpq hGetP hGetQ hMemP hMemQ
    simp only [entryTag, funUpdate_apply, hip, hiq, ite_false] at hResult ⊢; exact hResult

theorem rcMono_retire (spec : Program) (ss : SpecState) (eng : EngineId) (loop : Option ScopeId)
    (instr : DataPathInstrId) (rest : List (DataPathInstrId × Phase))
    (hHead : ss.inflight eng = (instr, Phase.committed) :: rest)
    (h2 : CountBalance spec ss eng loop)
    (h3 : IssueOrder spec ss eng loop)
    (h4 : QueueOrdered spec ss eng loop)
    (h5 : RCMono spec ss eng loop)
    (h6 : RCBound spec ss eng loop)
    : RCMono spec
        { ss with inflight := funUpdate ss.inflight eng rest,
                  rc := funUpdate ss.rc instr (ss.rc instr + 1) } eng loop := by
  have hInstrIF : instrInInflight instr (ss.inflight eng) = true := by
    rw [hHead]; simp [instrInInflight]
  intro i' j' hi' hj' hK'
  simp only [funUpdate_apply]
  by_cases hj : j' = instr <;> by_cases hi : i' = instr
  · -- i' = instr, j' = instr: idxOf contradicts itself
    rw [hi, hj] at hK'; omega
  · -- j' = instr, i' ≠ instr
    simp [hi, hj]
    have hOld := h5 i' instr hi' (hj ▸ hj') (hj ▸ hK')
    by_cases hiRC : ss.rc i' = ss.rc instr
    · by_cases hiIF : instrInInflight i' (ss.inflight eng) = true
      · -- i' in inflight, same rc: use QueueOrdered for contradiction
        have hiRest : instrInInflight i' rest = true := by
          rw [hHead] at hiIF; rw [instrInInflight_ne_head hi] at hiIF; exact hiIF
        obtain ⟨q, phq, hqGet, hqFirst⟩ := exists_first_occ hiIF
        have hCOB := first_occ_countOccsBefore_zero hqGet hqFirst
        have hq_pos : q ≥ 1 := by
          by_contra hc; have : q = 0 := by omega
          rw [this, hHead] at hqGet; simp at hqGet; exact hi hqGet.1.symm
        have h0 : (ss.inflight eng)[0]? = some (instr, Phase.committed) := by rw [hHead]; simp
        have hOrd := h4 0 q instr i' Phase.committed phq (by omega) h0 hqGet (hj ▸ hj') hi'
        simp only [entryTag, countOccsBefore_zero, hCOB] at hOrd
        rw [hj] at hK'; rw [hiRC] at hOrd; omega
      · -- i' ∉ inflight, same rc: use Inv2 + Inv3 for contradiction
        have hiIF_f : instrInInflight i' (ss.inflight eng) = false := by
          cases h : instrInInflight i' (ss.inflight eng) <;> simp_all
        have ⟨_, hiLo⟩ := h2 i' hi'
        have ⟨hInstrUp, _⟩ := h2 instr (hj ▸ hj')
        rw [inflightCount_zero_of_not_mem hiIF_f] at hiLo
        have hInstrIFC := inflightCount_pos_of_mem hInstrIF
        by_cases hIssued : ss.rc instr + inflightCount instr (ss.inflight eng) =
            totalEntriesOpt ss eng loop
        · have := h3 i' instr hi' (hj ▸ hj') (hj ▸ hK') hIssued
          rw [inflightCount_zero_of_not_mem hiIF_f] at this; simp at this; omega
        · omega
    · omega
  · -- i' = instr, j' ≠ instr: need rc(j') ≤ rc(instr) + 1, from Inv6
    simp [hj, hi]; exact h6 j' instr hj' (hi ▸ hi')
  · -- i' ≠ instr, j' ≠ instr: directly from old Inv5
    simp [hj, hi]; exact h5 i' j' hi' hj' hK'

theorem rcBound_retire (spec : Program) (ss : SpecState) (eng : EngineId) (loop : Option ScopeId)
    (instr : DataPathInstrId) (rest : List (DataPathInstrId × Phase))
    (hHead : ss.inflight eng = (instr, Phase.committed) :: rest)
    (h2 : CountBalance spec ss eng loop)
    (_h3 : IssueOrder spec ss eng loop)
    (h4 : QueueOrdered spec ss eng loop)
    (_h5 : RCMono spec ss eng loop)
    (h6 : RCBound spec ss eng loop)
    : RCBound spec
        { ss with inflight := funUpdate ss.inflight eng rest,
                  rc := funUpdate ss.rc instr (ss.rc instr + 1) } eng loop := by
  have hInstrIF : instrInInflight instr (ss.inflight eng) = true := by rw [hHead]; simp [instrInInflight]
  intro i' j' hi' hj'; simp only [funUpdate_apply]
  by_cases hi : i' = instr
  · by_cases hj : j' = instr
    · simp [hi, hj]
    · simp [hi, hj]
      by_cases hjR : instrInInflight j' rest = true
      · exact headMinRC_of_queueOrdered spec ss eng loop h4 instr Phase.committed rest hHead
          j' hjR (hi ▸ hi') hj'
      · have hjR_f : instrInInflight j' rest = false := by
          cases h : instrInInflight j' rest <;> simp_all
        have hjNotIF : instrInInflight j' (ss.inflight eng) = false := by
          rw [hHead]; simp [instrInInflight, Ne.symm hj, hjR_f]
        have ⟨_, hjLo⟩ := h2 j' hj'
        have ⟨hIUp, _⟩ := h2 instr (hi ▸ hi')
        rw [inflightCount_zero_of_not_mem hjNotIF] at hjLo
        have := inflightCount_pos_of_mem hInstrIF; omega
  · by_cases hj : j' = instr
    · simp [hi, hj]; have := h6 i' instr hi' (hj ▸ hj'); omega
    · simp [hi, hj]; exact h6 i' j' hi' hj'

/-! ## Issue Preservation Theorems -/

theorem countBalance_issue (spec : Program) (ss0 : SpecState) (e : EngineId)
    (eng : EngineId) (loop : Option ScopeId)
    (instr : DataPathInstrId)
    (hInv2 : CountBalance spec ss0 eng loop)
    (_hInv3 : IssueOrder spec ss0 eng loop)
    (hNext : instr ∈ scopeInstrs spec.engines eng spec.body loop →
      eng = e →
      ss0.rc instr + inflightCount instr (ss0.inflight eng) =
        totalEntriesOpt ss0 eng loop - 1)
    (hLater : ∀ j, j ∈ scopeInstrs spec.engines eng spec.body loop →
      (scopeInstrs spec.engines eng spec.body loop).idxOf instr <
        (scopeInstrs spec.engines eng spec.body loop).idxOf j →
      eng = e →
      ss0.rc j + inflightCount j (ss0.inflight eng) =
        totalEntriesOpt ss0 eng loop - 1)
    (hT : eng = e → totalEntriesOpt ss0 eng loop ≥ 1)
    : CountBalance spec
        { ss0 with
          inflight := funUpdate ss0.inflight e (ss0.inflight e ++ [(instr, Phase.issued)]) }
        eng loop := by
  intro i hi
  have hOld := hInv2 i hi
  have hTEq : totalEntriesOpt
      { controlState := ss0.controlState, dataPathState := ss0.dataPathState, pc := ss0.pc,
        inflight := funUpdate ss0.inflight e (ss0.inflight e ++ [(instr, Phase.issued)]),
        rc := ss0.rc, scopeEntryHistory := ss0.scopeEntryHistory }
      eng loop = totalEntriesOpt ss0 eng loop := by simp [totalEntriesOpt, totalEntries]
  rw [hTEq]; simp only [funUpdate_apply]
  by_cases he : eng = e
  · subst he
    simp only [ite_true, inflightCount_append, inflightCount_singleton]
    by_cases hii : instr == i
    · have hbeq := beq_iff_eq.mp hii; subst hbeq; simp
      have hN := hNext hi rfl; have hT1 := hT rfl; constructor <;> omega
    · simp [hii]; exact ⟨hOld.1, by omega⟩
  · simp [he]; exact ⟨hOld.1, by omega⟩

theorem issueOrder_issue (spec : Program) (ss0 : SpecState) (e : EngineId)
    (eng : EngineId) (loop : Option ScopeId)
    (instr : DataPathInstrId)
    (hInv3 : IssueOrder spec ss0 eng loop)
    (_hInv2 : CountBalance spec ss0 eng loop)
    (hNext : instr ∈ scopeInstrs spec.engines eng spec.body loop →
      eng = e →
      ∀ j, j ∈ scopeInstrs spec.engines eng spec.body loop →
        (scopeInstrs spec.engines eng spec.body loop).idxOf j <
          (scopeInstrs spec.engines eng spec.body loop).idxOf instr →
        ss0.rc j + inflightCount j (ss0.inflight eng) =
          totalEntriesOpt ss0 eng loop)
    (hInstrAtTm1 : instr ∈ scopeInstrs spec.engines eng spec.body loop →
      eng = e →
      ss0.rc instr + inflightCount instr (ss0.inflight eng) =
        totalEntriesOpt ss0 eng loop - 1)
    (hT : eng = e → totalEntriesOpt ss0 eng loop ≥ 1)
    : IssueOrder spec
        { ss0 with
          inflight := funUpdate ss0.inflight e (ss0.inflight e ++ [(instr, Phase.issued)]) }
        eng loop := by
  unfold IssueOrder; simp only
  intro i j hi hj hIdx hjT
  have hTEq : totalEntriesOpt
      { controlState := ss0.controlState, dataPathState := ss0.dataPathState, pc := ss0.pc,
        inflight := funUpdate ss0.inflight e (ss0.inflight e ++ [(instr, Phase.issued)]),
        rc := ss0.rc, scopeEntryHistory := ss0.scopeEntryHistory }
      eng loop = totalEntriesOpt ss0 eng loop := by simp [totalEntriesOpt, totalEntries]
  rw [hTEq] at hjT ⊢
  simp only [funUpdate_apply] at hjT ⊢
  by_cases he : eng = e
  · subst he
    simp only [ite_true, inflightCount_append, inflightCount_singleton] at hjT ⊢
    by_cases hji : instr == j
    · have hjeq := beq_iff_eq.mp hji; subst hjeq
      have hiT := hNext hj rfl i hi hIdx
      by_cases hii : instr == i
      · have hieq := beq_iff_eq.mp hii; subst hieq; omega
      · simp [hii]; exact hiT
    · simp [hji] at hjT
      by_cases hii : instr == i
      · have hieq := beq_iff_eq.mp hii; subst hieq; simp
        have hinstrT := hInv3 instr j hi hj hIdx hjT
        have hAtTm1 := hInstrAtTm1 hi rfl
        have hT1 := hT rfl; omega
      · simp [hii]; exact hInv3 i j hi hj hIdx hjT
  · simp only [he, ite_false] at hjT ⊢; exact hInv3 i j hi hj hIdx hjT

theorem queueOrdered_issue (spec : Program) (ss0 : SpecState) (e : EngineId)
    (eng : EngineId) (loop : Option ScopeId)
    (instr : DataPathInstrId)
    (hInv4 : QueueOrdered spec ss0 eng loop)
    (hTailMax : ∀ (p : Nat) (ip : DataPathInstrId) (pp : Phase),
      (ss0.inflight e)[p]? = some (ip, pp) →
      ip ∈ scopeInstrs spec.engines eng spec.body loop →
      instr ∈ scopeInstrs spec.engines eng spec.body loop →
      eng = e →
      entryTag ip ss0.rc (ss0.inflight e) p <
        entryTag instr ss0.rc (ss0.inflight e ++ [(instr, Phase.issued)]) (ss0.inflight e).length ∨
      (entryTag ip ss0.rc (ss0.inflight e) p =
        entryTag instr ss0.rc (ss0.inflight e ++ [(instr, Phase.issued)]) (ss0.inflight e).length ∧
       (scopeInstrs spec.engines eng spec.body loop).idxOf ip <
        (scopeInstrs spec.engines eng spec.body loop).idxOf instr))
    : QueueOrdered spec
        { ss0 with
          inflight := funUpdate ss0.inflight e (ss0.inflight e ++ [(instr, Phase.issued)]) }
        eng loop := by
  unfold QueueOrdered; simp only
  intro p q ip iq pp pq hpq hGetP hGetQ hMemP hMemQ
  simp only [funUpdate_apply] at hGetP hGetQ ⊢
  by_cases he : eng = e
  · subst he
    simp only [ite_true] at hGetP hGetQ ⊢
    have hET : ∀ (x : DataPathInstrId) (n : Nat), n < (ss0.inflight eng).length →
        entryTag x ss0.rc (ss0.inflight eng ++ [(instr, Phase.issued)]) n =
        entryTag x ss0.rc (ss0.inflight eng) n :=
      fun x n hn => by simp [entryTag, countOccsBefore_append_left x _ _ n hn]
    by_cases hqOld : q < (ss0.inflight eng).length
    · have hpOld := Nat.lt_trans hpq hqOld
      rw [hET ip p hpOld, hET iq q hqOld]
      exact hInv4 p q ip iq pp pq hpq
        (by rwa [List.getElem?_append_left hpOld] at hGetP)
        (by rwa [List.getElem?_append_left hqOld] at hGetQ) hMemP hMemQ
    · have hqLen : q = (ss0.inflight eng).length := by
        have := (List.getElem?_eq_some_iff.mp hGetQ).1; simp at this; omega
      subst hqLen
      have hpOld : p < (ss0.inflight eng).length := by omega
      rw [hET ip p hpOld]
      have hiqEq : iq = instr := by
        have : (ss0.inflight eng ++ [(instr, Phase.issued)])[(ss0.inflight eng).length]? =
            some (instr, Phase.issued) := by rw [List.getElem?_append_right (Nat.le_refl _)]; simp
        rw [this] at hGetQ; cases hGetQ; rfl
      rw [hiqEq] at hMemQ ⊢
      exact hTailMax p ip pp (by rwa [List.getElem?_append_left hpOld] at hGetP) hMemP hMemQ rfl
  · simp only [show (eng = e) = False from propext ⟨he, False.elim⟩, ite_false] at hGetP hGetQ ⊢
    exact hInv4 p q ip iq pp pq hpq hGetP hGetQ hMemP hMemQ

theorem rcMono_issue (spec : Program) (ss0 : SpecState) (e : EngineId)
    (eng : EngineId) (loop : Option ScopeId)
    (instr : DataPathInstrId)
    (hInv5 : RCMono spec ss0 eng loop)
    : RCMono spec
        { ss0 with
          inflight := funUpdate ss0.inflight e (ss0.inflight e ++ [(instr, Phase.issued)]) }
        eng loop := hInv5

theorem rcBound_issue (spec : Program) (ss0 : SpecState) (e : EngineId)
    (eng : EngineId) (loop : Option ScopeId)
    (instr : DataPathInstrId)
    (hInv6 : RCBound spec ss0 eng loop)
    : RCBound spec
        { ss0 with
          inflight := funUpdate ss0.inflight e (ss0.inflight e ++ [(instr, Phase.issued)]) }
        eng loop := hInv6

/-! ## Loop Entry Preservation (loopEnter / condTrue / condFalse) -/

private theorem totalEntriesOpt_incrScopeEntryHistory_ne
    {ss0 : SpecState} {e eng : EngineId} {loop : Option ScopeId} {sid : ScopeId}
    {encLoops : List ScopeId} (hLoop : ¬(loop = some sid ∧ eng = e))
    : totalEntriesOpt { ss0 with scopeEntryHistory := incrScopeEntryHistory ss0 e sid encLoops } eng loop =
        totalEntriesOpt ss0 eng loop := by
  simp only [totalEntriesOpt, totalEntries]
  cases loop with
  | none => simp
  | some s =>
    by_cases heng : eng = e
    · subst heng; by_cases hs : s = sid
      · exfalso; exact hLoop ⟨by rw [hs], rfl⟩
      · simp [incrScopeEntryHistory_ne_sid hs]
    · simp [incrScopeEntryHistory_ne_engine heng]

theorem countBalance_loopEntry (spec : Program) (ss0 : SpecState) (e : EngineId)
    (eng : EngineId) (loop : Option ScopeId) (sid : ScopeId)
    (encLoops : List ScopeId)
    (hInv2 : CountBalance spec ss0 eng loop)
    (hAllAtT : loop = some sid → eng = e →
      ∀ i, i ∈ scopeInstrs spec.engines eng spec.body loop →
        ss0.rc i + inflightCount i (ss0.inflight eng) = totalEntriesOpt ss0 eng loop)
    : CountBalance spec
        { ss0 with scopeEntryHistory := incrScopeEntryHistory ss0 e sid encLoops }
        eng loop := by
  intro i hi
  have hOld := hInv2 i hi
  show ss0.rc i + inflightCount i (ss0.inflight eng) ≤
      totalEntriesOpt { ss0 with scopeEntryHistory := incrScopeEntryHistory ss0 e sid encLoops } eng loop ∧
    ss0.rc i + inflightCount i (ss0.inflight eng) ≥
      totalEntriesOpt { ss0 with scopeEntryHistory := incrScopeEntryHistory ss0 e sid encLoops } eng loop - 1
  by_cases hLoop : loop = some sid ∧ eng = e
  · obtain ⟨hsc, heng⟩ := hLoop; subst heng
    have hTNew : totalEntriesOpt { ss0 with scopeEntryHistory := incrScopeEntryHistory ss0 eng sid encLoops } eng (some sid) =
        totalEntriesOpt ss0 eng (some sid) + 1 := by simp [totalEntriesOpt, totalEntries]
    rw [hsc, hTNew]
    have hAtT := hAllAtT hsc rfl i hi; rw [hsc] at hAtT; constructor <;> omega
  · rw [totalEntriesOpt_incrScopeEntryHistory_ne hLoop]; exact hOld

theorem issueOrder_loopEntry (spec : Program) (ss0 : SpecState) (e : EngineId)
    (eng : EngineId) (loop : Option ScopeId) (sid : ScopeId)
    (encLoops : List ScopeId)
    (hInv3 : IssueOrder spec ss0 eng loop)
    (hAllAtT : loop = some sid → eng = e →
      ∀ i, i ∈ scopeInstrs spec.engines eng spec.body loop →
        ss0.rc i + inflightCount i (ss0.inflight eng) = totalEntriesOpt ss0 eng loop)
    : IssueOrder spec
        { ss0 with scopeEntryHistory := incrScopeEntryHistory ss0 e sid encLoops }
        eng loop := by
  unfold IssueOrder; simp only
  intro i j hi hj hIdx hjT
  show ss0.rc i + inflightCount i (ss0.inflight eng) =
    totalEntriesOpt { ss0 with scopeEntryHistory := incrScopeEntryHistory ss0 e sid encLoops } eng loop
  by_cases hLoop : loop = some sid ∧ eng = e
  · obtain ⟨hsc, heng⟩ := hLoop; subst heng
    have hTNew : totalEntriesOpt { ss0 with scopeEntryHistory := incrScopeEntryHistory ss0 eng sid encLoops } eng (some sid) =
        totalEntriesOpt ss0 eng (some sid) + 1 := by simp [totalEntriesOpt, totalEntries]
    rw [hsc] at hjT ⊢; rw [hTNew] at hjT ⊢
    have hjAtT := hAllAtT hsc rfl j hj; rw [hsc] at hjAtT; omega
  · rw [totalEntriesOpt_incrScopeEntryHistory_ne hLoop] at hjT ⊢; exact hInv3 i j hi hj hIdx hjT

theorem queueOrdered_loopEntry (spec : Program) (ss0 : SpecState) (e : EngineId)
    (eng : EngineId) (loop : Option ScopeId) (sid : ScopeId)
    (encLoops : List ScopeId)
    (hInv4 : QueueOrdered spec ss0 eng loop)
    : QueueOrdered spec
        { ss0 with scopeEntryHistory := incrScopeEntryHistory ss0 e sid encLoops }
        eng loop := hInv4

theorem rcMono_loopEntry (spec : Program) (ss0 : SpecState) (e : EngineId)
    (eng : EngineId) (loop : Option ScopeId) (sid : ScopeId)
    (encLoops : List ScopeId)
    (hInv5 : RCMono spec ss0 eng loop)
    : RCMono spec
        { ss0 with scopeEntryHistory := incrScopeEntryHistory ss0 e sid encLoops }
        eng loop := hInv5

theorem rcBound_loopEntry (spec : Program) (ss0 : SpecState) (e : EngineId)
    (eng : EngineId) (loop : Option ScopeId) (sid : ScopeId)
    (encLoops : List ScopeId)
    (hInv6 : RCBound spec ss0 eng loop)
    : RCBound spec
        { ss0 with scopeEntryHistory := incrScopeEntryHistory ss0 e sid encLoops }
        eng loop := hInv6

/-! ## Inv7 Preservation -/

theorem pcComplete_retire (spec : Program) (ss0 : SpecState) (e : EngineId)
    (eng : EngineId) (loop : Option ScopeId) (kBound : Nat)
    (instr : DataPathInstrId) (ph : Phase) (rest : List (DataPathInstrId × Phase))
    (hHead : ss0.inflight e = (instr, ph) :: rest)
    (hInv7 : PCComplete spec ss0 eng loop kBound)
    (hInv7Back : ∀ i, i ∈ scopeInstrs spec.engines eng spec.body loop →
      (scopeInstrs spec.engines eng spec.body loop).idxOf i ≥ kBound →
      ss0.rc i + inflightCount i (ss0.inflight eng) =
        totalEntriesOpt ss0 eng loop - 1)
    (hInstrEng : eng ≠ e → instr ∉ scopeInstrs spec.engines eng spec.body loop)
    : PCComplete spec
        { ss0 with inflight := funUpdate ss0.inflight e rest,
                   rc := funUpdate ss0.rc instr (ss0.rc instr + 1) }
        eng loop kBound ∧
      (∀ i, i ∈ scopeInstrs spec.engines eng spec.body loop →
        (scopeInstrs spec.engines eng spec.body loop).idxOf i ≥ kBound →
        (funUpdate ss0.rc instr (ss0.rc instr + 1)) i +
          inflightCount i (funUpdate ss0.inflight e rest eng) =
          totalEntriesOpt ss0 eng loop - 1) := by
  exact ⟨fun i hi hlt => by rw [retire_net_effect spec loop hHead hInstrEng hi]; exact hInv7 i hi hlt,
         fun i hi hge => by rw [retire_net_effect spec loop hHead hInstrEng hi]; exact hInv7Back i hi hge⟩


/-! ## kBound Determination Lemmas -/

theorem pcComplete_allAtT_of_kBound_ge_length
    (spec : Program) (ss : SpecState) (eng : EngineId) (loop : Option ScopeId)
    (kBound : Nat)
    (hInv7 : PCComplete spec ss eng loop kBound)
    (hKGe : kBound ≥ (scopeInstrs spec.engines eng spec.body loop).length)
    : ∀ i, i ∈ scopeInstrs spec.engines eng spec.body loop →
      ss.rc i + inflightCount i (ss.inflight eng) = totalEntriesOpt ss eng loop :=
  fun i hi => hInv7 i hi (by have := List.idxOf_lt_length_of_mem hi; omega)

theorem pcComplete_kBound_eq_of_at_Tm1
    (spec : Program) (ss : SpecState) (eng : EngineId) (loop : Option ScopeId)
    (kBound : Nat) (instr : DataPathInstrId)
    (hInv7 : PCComplete spec ss eng loop kBound)
    (_hInv7Back : ∀ i, i ∈ scopeInstrs spec.engines eng spec.body loop →
      (scopeInstrs spec.engines eng spec.body loop).idxOf i ≥ kBound →
      ss.rc i + inflightCount i (ss.inflight eng) = totalEntriesOpt ss eng loop - 1)
    (hMem : instr ∈ scopeInstrs spec.engines eng spec.body loop)
    (hAtTm1 : ss.rc instr + inflightCount instr (ss.inflight eng) =
      totalEntriesOpt ss eng loop - 1)
    (hT : totalEntriesOpt ss eng loop ≥ 1)
    : (scopeInstrs spec.engines eng spec.body loop).idxOf instr ≥ kBound := by
  by_contra hlt; exact absurd (hInv7 instr hMem (by omega)) (by omega)



/-! ## findActiveFrame returns none when loop not on stack -/

private theorem enclosingLoopsFromStack_tail {child : Frame} {rest : List Frame} {sid : ScopeId}
    (hNotIn : sid ∉ enclosingLoopsFromStack (child :: rest))
    : sid ∉ enclosingLoopsFromStack rest := by
  intro hIn; apply hNotIn; simp only [enclosingLoopsFromStack]
  cases child.kind with
  | loop _ | cond _ => exact List.mem_cons_of_mem _ hIn
  | top => exact hIn

theorem instrsBefore_length_eq_scopeInstrs_none {engines : List EngineId} {eng : EngineId}
    {body : List Stmt}
    : instrsBefore engines eng body body.length = (scopeInstrs engines eng body none).length := by
  induction body with
  | nil => simp [instrsBefore]
  | cons s rest ih => cases s <;> simp [instrsBefore, List.length_append, ih]

theorem findActiveFrame_none_of_not_in_enclosing {stack : List Frame} {sid : ScopeId}
    (hNotIn : sid ∉ enclosingLoopsFromStack stack)
    : findActiveFrame stack (some sid) = none := by
  induction stack with
  | nil => simp [findActiveFrame]
  | cons child rest ih =>
    have hNotIn' : sid ∉ enclosingLoopsFromStack rest :=
      enclosingLoopsFromStack_tail hNotIn
    cases rest with
    | nil => simp [findActiveFrame]
    | cons parent rest' =>
      simp only [findActiveFrame]
      cases hk : child.kind with
      | loop sid' | cond sid' =>
        have hne : sid' ≠ sid := by
          intro heq; subst heq
          exact hNotIn (by simp only [enclosingLoopsFromStack, hk]; exact List.Mem.head _)
        simp [hne, ih hNotIn']
      | top => simp [ih hNotIn']

theorem scopeKBound_eq_length_of_not_on_stack {spec : Program} {ss : SpecState} {eng : EngineId} {sid : ScopeId}
    (hNotIn : sid ∉ enclosingLoopsFromStack (ss.pc eng).stack)
    : scopeKBound spec ss eng (some sid) = (scopeInstrs spec.engines eng spec.body (some sid)).length := by
  simp [scopeKBound, findActiveFrame_none_of_not_in_enclosing hNotIn]
