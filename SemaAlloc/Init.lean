import SemaAlloc.PerScopeBackwardSim
import SemaAlloc.PerScopeForwardSim

/-! # Initial State Definitions and Invariant Proofs

All init-state theorems in one place. These prove that the initial states
satisfy MatchStates, ImplInv, SpecInv, PerScopeInv, and NotAtRegOp.
-/

def initSpecState (spec : Program) (initDataPath : DataPathState) (initControl : EngineId → ControlState) : SpecState where
  controlState := initControl
  dataPathState := initDataPath
  pc := fun _ => { stack := [⟨spec.body, 0, .top⟩], instrIdx := 0 }
  inflight := fun _ => []
  rc := fun _ => 0
  scopeEntryHistory := fun _ _ _ _ => 0

def initImplState (impl : ImplProgram) (initDataPath : DataPathState) (initControl : EngineId → ControlState) : ImplState where
  controlState := initControl
  dataPathState := initDataPath
  pc := fun _ => { stack := [⟨impl.body, 0, .top⟩], instrIdx := 0, regOpIdx := 0, stmtRegOpIdx := 0 }
  inflight := fun _ => []
  registers := fun _ _ => 0
  semaphores := fun _ => 0

theorem initMatchStates (spec : Program) (impl : ImplProgram) (alloc : PerInstrAllocR spec impl)
    (initDataPath : DataPathState) (initControl : EngineId → ControlState)
    : MatchStates spec impl alloc.toAllocBase (perInstrSemaInv alloc)
        (initSpecState spec initDataPath initControl)
        (initImplState impl initDataPath initControl) where
  dataPathEq := rfl; inflightEq := fun _ => rfl; controlEq := fun _ => rfl
  semaInv := fun _ => rfl
  monotoneRegInv := by
    intro e lid _; simp [initImplState, totalEntries, initSpecState]
  tripRegInv := by
    intro e lid _
    simp [initImplState, tripEntries, initSpecState, totalEntries]
    split <;> rfl
  regOpFold := by
    intro e frame rest ops hStack hStmt
    simp [initImplState] at hStack
    obtain ⟨rfl, rfl⟩ := hStack
    exact absurd hStmt (bodyMatch_no_regOp alloc.bodyMatch)
  pcCorr := fun _ => ⟨.cons _ _ [] []
    ⟨by simp [frameKindCorr], ⟨_, alloc.bodyMatch, by simp⟩,
     fun h => by simp [atRegOp] at h, fun _ => by simp⟩
    .nil (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h), rfl⟩
  waitRegChain := by intros; simp_all [initImplState]
  gateRegChain := by intros; simp_all [initImplState]

theorem initImplInv (impl : ImplProgram) (initDataPath : DataPathState) (initControl : EngineId → ControlState)
    : ImplInv impl (initImplState impl initDataPath initControl) where
  regOpBound := by intros; simp_all [initImplState]
  stmtRegOpBound := by intros; simp_all [initImplState]
  topKindOnly := by
    intro _ _ frame rest hS; simp [initImplState] at hS
    obtain ⟨rfl, rfl⟩ := hS; rfl

theorem initNotAtRegOp (impl : ImplProgram) (initDataPath : DataPathState) (initControl : EngineId → ControlState)
    : NotAtRegOp (initImplState impl initDataPath initControl) := by
  intro e fr r hS; simp [initImplState] at hS; obtain ⟨rfl, _⟩ := hS; simp [atRegOp]

theorem initSpecInv (spec : Program) (initDataPath : DataPathState) (initControl : EngineId → ControlState)
    : SpecInv spec (initSpecState spec initDataPath initControl) := by
  refine specInv_init spec _ ?_ ?_ ?_ (fun _ => StackMatchesProgram.base 0 0) ?_ <;>
    intros <;> simp [initSpecState, totalEntries, loopsOnStack, enclosingLoopsFromStack]

theorem initPerScopeMatchStates (spec : Program) (impl : ImplProgram) (alloc : PerScopeAllocR spec impl)
    (initDataPath : DataPathState) (initControl : EngineId → ControlState)
    : MatchStates spec impl alloc.toAllocBase (perScopeSemaInv spec alloc)
        (initSpecState spec initDataPath initControl)
        (initImplState impl initDataPath initControl) where
  dataPathEq := rfl; inflightEq := fun _ => rfl; controlEq := fun _ => rfl
  semaInv := by
    intro loop eng _
    simp only [initImplState, initSpecState, scopeRetireSum]
    induction (scopeInstrs spec.engines eng spec.body loop) with
    | nil => simp [List.foldl]
    | cons _ _ ih => simp only [List.foldl]; exact ih
  monotoneRegInv := by
    intro e lid _; simp [initImplState, totalEntries, initSpecState]
  tripRegInv := by
    intro e lid _
    simp [initImplState, tripEntries, initSpecState, totalEntries]
    split <;> rfl
  regOpFold := by
    intro e frame rest ops hStack hStmt
    simp [initImplState] at hStack
    obtain ⟨rfl, rfl⟩ := hStack
    exact absurd hStmt (bodyMatch_no_regOp alloc.bodyMatch)
  pcCorr := fun _ => ⟨.cons _ _ [] []
    ⟨by simp [frameKindCorr], ⟨_, alloc.bodyMatch, by simp⟩,
     fun h => by simp [atRegOp] at h, fun _ => by simp⟩
    .nil (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h), rfl⟩
  waitRegChain := by intros; simp_all [initImplState]
  gateRegChain := by intros; simp_all [initImplState]

theorem initPerScopeInv (spec : Program) (impl : ImplProgram) (alloc : PerScopeAllocR spec impl)
    (initDataPath : DataPathState) (initControl : EngineId → ControlState)
    : PerScopeInv spec impl alloc
        (initSpecState spec initDataPath initControl)
        (initImplState impl initDataPath initControl) where
  semaInv := (initPerScopeMatchStates spec impl alloc initDataPath initControl).semaInv
  countBalance := by
    intro _ loop _ _ _
    simp only [initSpecState, inflightCount, totalEntriesOpt, totalEntries]; cases loop <;> simp
  issueOrder := by
    intro _ loop _ _ _ _ _ _ hj
    simp only [initSpecState, inflightCount, totalEntriesOpt, totalEntries] at hj ⊢
    cases loop <;> omega
  queueOrdered := by intro _ _ _ _ _ _ _ _ _ _ hp; simp [initSpecState] at hp
  rcMono := by intro _ _ _ _ _ _ _ _; simp [initSpecState]
  rcBound := by intro _ _ _ _ _ _ _; simp [initSpecState]
  pcComplete := by
    intro _ loop _
    refine ⟨?_, fun _ _ _ => by
      simp only [initSpecState, inflightCount, totalEntriesOpt, totalEntries]; cases loop <;> simp⟩
    intro i hi h
    cases loop with
    | some _ => simp only [initSpecState, inflightCount, totalEntriesOpt, totalEntries]
    | none =>
      exfalso; simp only [scopeKBound, initSpecState, findActiveFrame] at h
      cases hb : spec.body with
      | nil => simp [hb] at hi
      | cons s _ => simp [hb] at h; cases s <;> simp at h
  instrAtPC_atTm1 := by
    intro _ _ _ _ _ _ _ _ _ loop _
    simp only [initSpecState, inflightCount, totalEntriesOpt, totalEntries]; cases loop <;> simp
