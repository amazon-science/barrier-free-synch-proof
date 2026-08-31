import SemaAlloc.Utilities
import Batteries

/-! # PC Position to scopeInstrs Index

This file defines `scopeInstrs` (the flat list of instructions for an engine in a loop)
and `instrsBefore` (counting instructions in blocks before a given stmtIdx), then proves
that the `idxOf` of an instruction in `scopeInstrs` equals `instrsBefore + instrIdx`.
-/

namespace PCBound

/-- Collect all instruction IDs for engine `eng` from blocks at the top level of `body`. -/
def scopeInstrsNone (engines : List EngineId) (eng : EngineId) : List Stmt → List DataPathInstrId
  | [] => []
  | Stmt.block f :: rest => f eng ++ scopeInstrsNone engines eng rest
  | Stmt.loop _ _ :: rest => scopeInstrsNone engines eng rest
  | Stmt.cond _ _ _ _ :: rest => scopeInstrsNone engines eng rest

/-- `scopeInstrs engines eng body loop` returns the flat list of instruction IDs
    for engine `eng` in the given loop. For `loop = none` (top level), it collects
    `f eng` for each `Stmt.block f` in `body`. For `loop = some sid`, it finds the
    loop body via `findLoopBody` and collects there. -/
def scopeInstrs (engines : List EngineId) (eng : EngineId)
    (body : List Stmt) (loop : Option ScopeId) : List DataPathInstrId :=
  match loop with
  | none => scopeInstrsNone engines eng body
  | some sid => scopeInstrsNone engines eng (findLoopBody body sid)

-- instrsBefore moved to ASTLemmas.lean

-- Simp lemmas for scopeInstrsNone
@[simp] theorem scopeInstrsNone_nil (engines : List EngineId) (eng : EngineId) :
    scopeInstrsNone engines eng [] = [] := rfl

@[simp] theorem scopeInstrsNone_block (engines : List EngineId) (eng : EngineId)
    (f : EngineId → List DataPathInstrId) (rest : List Stmt) :
    scopeInstrsNone engines eng (Stmt.block f :: rest) = f eng ++ scopeInstrsNone engines eng rest := rfl

@[simp] theorem scopeInstrsNone_loop (engines : List EngineId) (eng : EngineId)
    (lid : ScopeId) (body : List Stmt) (rest : List Stmt) :
    scopeInstrsNone engines eng (Stmt.loop lid body :: rest) = scopeInstrsNone engines eng rest := rfl

@[simp] theorem scopeInstrsNone_cond (engines : List EngineId) (eng : EngineId)
    (tid eid : ScopeId) (tb eb : List Stmt) (rest : List Stmt) :
    scopeInstrsNone engines eng (Stmt.cond tid eid tb eb :: rest) = scopeInstrsNone engines eng rest := rfl

-- Simp lemmas for instrsBefore
@[simp] theorem instrsBefore_nil (engines : List EngineId) (eng : EngineId) (n : Nat) :
    instrsBefore engines eng [] n = 0 := by cases n <;> rfl

@[simp] theorem instrsBefore_zero (engines : List EngineId) (eng : EngineId) (body : List Stmt) :
    instrsBefore engines eng body 0 = 0 := by cases body <;> rfl

@[simp] theorem instrsBefore_block_succ (engines : List EngineId) (eng : EngineId)
    (f : EngineId → List DataPathInstrId) (rest : List Stmt) (n : Nat) :
    instrsBefore engines eng (Stmt.block f :: rest) (n + 1) =
      (f eng).length + instrsBefore engines eng rest n := rfl

@[simp] theorem instrsBefore_loop_succ (engines : List EngineId) (eng : EngineId)
    (lid : ScopeId) (body : List Stmt) (rest : List Stmt) (n : Nat) :
    instrsBefore engines eng (Stmt.loop lid body :: rest) (n + 1) =
      instrsBefore engines eng rest n := rfl

@[simp] theorem instrsBefore_cond_succ (engines : List EngineId) (eng : EngineId)
    (tid eid : ScopeId) (tb eb : List Stmt) (rest : List Stmt) (n : Nat) :
    instrsBefore engines eng (Stmt.cond tid eid tb eb :: rest) (n + 1) =
      instrsBefore engines eng rest n := rfl

-- scopeInstrs simplification
@[simp] theorem scopeInstrs_none (engines : List EngineId) (eng : EngineId) (body : List Stmt) :
    scopeInstrs engines eng body none = scopeInstrsNone engines eng body := rfl


theorem findInBlock_isSome_of_mem (engines : List EngineId) (eng : EngineId)
    (f : EngineId → List DataPathInstrId) (instr : DataPathInstrId)
    (hEngMem : eng ∈ engines) (hInstr : instr ∈ f eng) :
    (findInBlock engines f instr).isSome = true := by
  induction engines with
  | nil => exact absurd hEngMem List.not_mem_nil
  | cons e es ih =>
    simp [findInBlock]
    cases List.mem_cons.mp hEngMem with
    | inl heq => subst heq; simp [hInstr]
    | inr hMem =>
      by_cases hIn : instr ∈ f e
      · simp [hIn]
      · simp [hIn]; exact ih hMem

/-- If `instr ∈ scopeInstrsNone engines eng body`, then `instrInBody engines body instr = true`. -/
theorem instrInBody_of_mem_scopeInstrsNone (engines : List EngineId) (eng : EngineId)
    (body : List Stmt) (instr : DataPathInstrId) (hEngMem : eng ∈ engines)
    (h : instr ∈ scopeInstrsNone engines eng body) :
    instrInBody engines body instr = true := by
  induction body with
  | nil => simp at h
  | cons s rest ih =>
    cases s with
    | block g =>
      simp [List.mem_append] at h; simp [instrInBody]
      rcases h with hL | hR
      · left; exact findInBlock_isSome_of_mem engines eng g instr hEngMem hL
      · right; exact ih hR
    | loop _ _ | cond _ _ _ _ => simp at h; simp [instrInBody]; right; exact ih h

/-- Key lemma: an instruction appearing in `f eng` at position `instrIdx` where
    `Stmt.block f` is at position `stmtIdx` in `body` is a member of `scopeInstrsNone`. -/
theorem mem_scopeInstrsNone_of_block
    (engines : List EngineId) (eng : EngineId) (body : List Stmt)
    (stmtIdx instrIdx : Nat) (f : EngineId → List DataPathInstrId) (instr : DataPathInstrId)
    (hStmt : body[stmtIdx]? = some (Stmt.block f))
    (hInstr : (f eng)[instrIdx]? = some instr) :
    instr ∈ scopeInstrsNone engines eng body := by
  induction body generalizing stmtIdx with
  | nil => simp at hStmt
  | cons s rest ih =>
    cases stmtIdx with
    | zero =>
      cases s <;> simp at hStmt
      cases hStmt; simp [List.mem_append]; left; exact List.mem_of_getElem? hInstr
    | succ n =>
      cases s with
      | block g => simp at hStmt; simp [List.mem_append]; right; exact ih n hStmt
      | loop _ _ | cond _ _ _ _ => simp at hStmt; simp; exact ih n hStmt

/-- The main structural lemma (loop = none case):
    If `body[stmtIdx]? = some (Stmt.block f)` and `(f eng)[instrIdx]? = some instr`,
    then `(scopeInstrsNone engines eng body).idxOf instr = instrsBefore engines eng body stmtIdx + instrIdx`.

    This connects the PC position to the index in the flat instruction list. -/
theorem scopeInstrsNone_idxOf_eq
    (engines : List EngineId) (eng : EngineId) (body : List Stmt)
    (stmtIdx instrIdx : Nat) (f : EngineId → List DataPathInstrId) (instr : DataPathInstrId)
    (hStmt : body[stmtIdx]? = some (Stmt.block f))
    (hInstr : (f eng)[instrIdx]? = some instr)
    (hUI : UniqueInstrIds engines body)
    (hEngMem : eng ∈ engines)
    (hNodup : (scopeInstrsNone engines eng body).Nodup) :
    (scopeInstrsNone engines eng body).idxOf instr =
      instrsBefore engines eng body stmtIdx + instrIdx := by
  induction body generalizing stmtIdx with
  | nil => simp at hStmt
  | cons s rest ih =>
    cases stmtIdx with
    | zero =>
      -- instr is in the current (first) block
      cases s with
      | block g =>
        simp at hStmt; cases hStmt
        simp only [instrsBefore, scopeInstrsNone, Nat.zero_add]
        -- Goal: (f eng ++ scopeInstrsNone engines eng rest).idxOf instr = instrIdx
        have hMem : instr ∈ f eng := List.mem_of_getElem? hInstr
        rw [List.idxOf_append, if_pos hMem]
        -- Now: (f eng).idxOf instr = instrIdx
        have hNodupL : (f eng).Nodup := by
          have h : (f eng ++ scopeInstrsNone engines eng rest).Nodup := hNodup
          exact (List.nodup_append.mp h).1
        have hlt : instrIdx < (f eng).length := (List.getElem?_eq_some_iff.mp hInstr).1
        have heq : (f eng)[instrIdx] = instr := (List.getElem?_eq_some_iff.mp hInstr).2
        rw [← heq]; exact hNodupL.idxOf_getElem instrIdx hlt
      | loop _ _ | cond _ _ _ _ => simp at hStmt
    | succ n =>
      -- instr is in a later block
      cases s with
      | block g =>
        simp at hStmt
        simp only [instrsBefore, scopeInstrsNone]
        -- Goal: (g eng ++ scopeInstrsNone engines eng rest).idxOf instr
        --       = (g eng).length + instrsBefore engines eng rest n + instrIdx
        have hMemRest : instr ∈ scopeInstrsNone engines eng rest :=
          mem_scopeInstrsNone_of_block engines eng rest n instrIdx f instr hStmt hInstr
        cases hUI with
        | block =>
          rename_i _ _ hUIR hDisj
          have hNotInG : instr ∉ g eng := by
            intro hMem
            have hInBody := instrInBody_of_mem_scopeInstrsNone engines eng rest instr hEngMem hMemRest
            have hFIB := findInBlock_isSome_of_mem engines eng g instr hEngMem hMem
            have := hDisj instr hFIB
            simp [this] at hInBody
          rw [List.idxOf_append, if_neg hNotInG]
          have hNodupRest : (scopeInstrsNone engines eng rest).Nodup := by
            have h : (g eng ++ scopeInstrsNone engines eng rest).Nodup := hNodup
            exact (List.nodup_append.mp h).2.1
          have ihResult := ih n hStmt hUIR hNodupRest
          omega
      | loop _ _ | cond _ _ _ _ =>
        simp at hStmt; simp only [instrsBefore, scopeInstrsNone]
        (cases hUI; exact ih n hStmt (by assumption) hNodup)

end PCBound
