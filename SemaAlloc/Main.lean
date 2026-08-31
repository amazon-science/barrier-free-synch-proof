import SemaAlloc.Init

/-! # Top-Level Bisimulation Theorem

We prove a bisimulation between the specification and implementation
transition systems for the per-loop semaphore allocation.

MatchStates includes `dataPathEq : is.dataPathState = ss.dataPathState`, so the
bisimulation immediately implies that the reachable DataPathState sets are
identical (trace equivalence and reachable-state equivalence follow).

Detailed definitions of all structures referenced here (Program, ImplProgram,
PerScopeAllocR, SpecState, ImplState, SpecStep, ImplStep, MatchStates, SpecInv, PerScopeInv,
ImplInv, etc.) can be found in their respective files:
  - Spec.lean: Program, SpecState, SpecStep, SpecStar
  - Impl.lean: ImplProgram, ImplState, ImplStep, ImplPlusAny
  - PerScopeAlloc.lean: PerScopeAllocR (the per-loop allocation relation)
  - MatchStates.lean: MatchStates, ImplInv, AllocBase
  - SpecInv.lean: SpecInv
  - PerScopeInv.lean: PerScopeInv
  - PerScopeLemmas.lean: perScopeSemaInv
  - Allocatable.lean: Allocatable
  - PerInstrAlloc.lean: BodyMatch, AllocBase
-/

/-! ## Bisimulation Definition -/

/-- A bisimulation between Spec and Impl with witness relation R. -/
structure Bisimulation (spec : Program) (impl : ImplProgram)
    (R : SpecState → ImplState → Prop)
    (ss₀ : SpecState) (is₀ : ImplState) : Prop where
  /-- The initial states are related -/
  init : R ss₀ is₀
  /-- Liveness direction: a specification step (SpecStep) must be matched by 1 or more (ImplPlusAny) implementation steps. -/
  fwd : ∀ ss is e ss', R ss is → SpecStep spec e ss ss' →
    ∃ is', ImplPlusAny impl is is' ∧ R ss' is'
  /-- Safety direction: An implementation step (ImplStep) must be matched by 0 or more (SpecStar) spec steps-/
  bwd : ∀ ss is e is', R ss is → ImplStep impl e is is' →
    ∃ ss', SpecStar spec ss ss' ∧ R ss' is'

/-! ## The Bisimulation Relation -/

/-- The combined bisimulation relation for per-loop allocation. -/
def BisimRel (spec : Program) (impl : ImplProgram) (alloc : PerScopeAllocR spec impl)
    (ss : SpecState) (is : ImplState) : Prop :=
  MatchStates spec impl alloc.toAllocBase (perScopeSemaInv spec alloc) ss is ∧
  SpecInv spec ss ∧
  PerScopeInv spec impl alloc ss is ∧
  ImplInv impl is

/-! ## Well-formedness and Initialization Hypotheses -/

/-- All assumptions and initial-state data needed for the per-scope bisimulation.
    - `hWf : Allocatable spec` — static well-formedness of the dependency graph: every dependency is "allocatable" (falls into ProducerIsParent, SameIter, or PrevIter). See Allocatable.lean.
    - `hUniq : UniqueScopeIds spec.body` — all loop identifiers in the AST are distinct (no reuse of loop/cond IDs). See Utilities.lean.
    - `hUniqueInstr : UniqueInstrIds spec.engines spec.body` — all instruction identifiers are distinct across all engines and all blocks in the AST. See Utilities.lean.
    - `initDataPath : DataPathState` — the initial (opaque) datapath/memory state, which is the same in the Spec and the Impl.
    - `initControl : EngineId → ControlState` — the initial per-engine control state (determines loop trip counts and branch decisions), which is the same in the Spec and the Impl.
-/
structure PerScopeBisimSetup (spec : Program) : Type where
  hWf : Allocatable spec
  hUniq : UniqueScopeIds spec.body
  hUniqueInstr : UniqueInstrIds spec.engines spec.body
  initDataPath : DataPathState
  initControl : EngineId → ControlState

namespace PerScopeBisimSetup

-- The `SpecState` produced by these init datapath and control states
def specInit (hPSBS : PerScopeBisimSetup spec) : SpecState :=
  initSpecState spec hPSBS.initDataPath hPSBS.initControl

-- The `ImplState` produced by these init datapath and control states
def implInit (hPSBS : PerScopeBisimSetup spec) (impl : ImplProgram) : ImplState :=
  initImplState impl hPSBS.initDataPath hPSBS.initControl

end PerScopeBisimSetup


/-! ## Top-Level Bisimulation Theorem -/

/-- The per-loop semaphore allocation is a bisimulation.

    BisimRel is preserved at every step of both transition systems.
    Since MatchStates asserts DataPathState equality, this implies the reachable DataPathState sets are
    identical from any common initial state — i.e., the implementation produces exactly the same observable
    behaviors as the specification.

    **Hypotheses:**
    - `spec : Program` — the specification program.
    - `impl : ImplProgram` — the implementation program
    - `alloc : PerScopeAllocR spec impl` — witnesses that impl is a valid per-loop allocation of spec.
    - `hPSBS : PerScopeBisimSetup spec` - all intialization and static well-formedness hypotheses for the allocation.
-/
theorem perScope_bisimulation
    (spec : Program)
    (impl : ImplProgram)
    (alloc : PerScopeAllocR spec impl)
    (hPSBS : PerScopeBisimSetup spec) :
    Bisimulation spec impl (BisimRel spec impl alloc)
      hPSBS.specInit
      (hPSBS.implInit impl) := by

  rcases hPSBS with
    ⟨hWf, hUniq, hUniqueInstr, initDataPath, initControl⟩

  constructor

  · exact
      ⟨initPerScopeMatchStates spec impl alloc initDataPath initControl,
       initSpecInv spec initDataPath initControl,
       initPerScopeInv spec impl alloc initDataPath initControl,
       initImplInv impl initDataPath initControl⟩

  · intro ss is e ss' ⟨hSim, hSpecInv, hPerScopeInv, hImplInv⟩ hStep
    have hEngines : e ∈ spec.engines := hStep.mem_engines

    -- Drain any pending regOps (impl-only steps, spec unchanged)
    obtain ⟨is₁, hDrain, hSim₁, hImplInv₁, hNARO₁, hPerScopeInv₁⟩ :=
      drain_all_regOps spec impl alloc ss is hSim hImplInv hPerScopeInv

    -- Apply the existing forward step theorem
    obtain ⟨is₂, hFwdStar, hSim₂, _hNARO₂⟩ :=
      perScope_forward_sim_step spec impl alloc e ss ss' is₁
        hSim₁ hImplInv₁ hNARO₁ hWf hSpecInv hUniq hUniqueInstr
        hEngines hPerScopeInv₁ hStep

    have hSpecInv' :=
      specInv_step spec e ss ss' hUniq hSpecInv hStep

    have hImplInv₂ :=
      implInv_starAny impl is₁ is₂ hImplInv₁ hFwdStar.to_star

    have hPerScopeGoal :=
      perScopeInv_spec_step spec impl alloc e ss ss' hStep
        hPerScopeInv₁ hSpecInv hUniqueInstr hUniq

    have hPerScopeInv' : PerScopeInv spec impl alloc ss' is₂ := {
      semaInv := hSim₂.semaInv
      countBalance := hPerScopeGoal.1
      issueOrder := hPerScopeGoal.2.1
      queueOrdered := hPerScopeGoal.2.2.1
      rcMono := hPerScopeGoal.2.2.2.1
      rcBound := hPerScopeGoal.2.2.2.2.1
      pcComplete := hPerScopeGoal.2.2.2.2.2.1
      instrAtPC_atTm1 := hPerScopeGoal.2.2.2.2.2.2
    }

    exact
      ⟨is₂, hDrain.trans_plus hFwdStar,
       hSim₂, hSpecInv', hPerScopeInv', hImplInv₂⟩

  · intro ss is e is' ⟨hSim, hSpecInv, hPerScopeInv, hImplInv⟩ hStep

    have hEngines : e ∈ spec.engines :=
      congrArg ProgramBase.engines alloc.baseEq ▸ hStep.mem_engines

    have hImplInv' :=
      implInv_step impl e is is' hImplInv hStep

    rcases perScope_backward_sim_step spec impl alloc e ss is is'
      hSim hStep hWf hSpecInv hUniq hUniqueInstr hEngines hPerScopeInv with
      ⟨ss', hSpecStep, hSim'⟩ | hSim'

    · -- Real step: spec took a step
      have hSpecInv' :=
        specInv_step spec e ss ss' hUniq hSpecInv hSpecStep

      have hPerScopeGoal :=
        perScopeInv_spec_step spec impl alloc e ss ss' hSpecStep
          hPerScopeInv hSpecInv hUniqueInstr hUniq

      have hPerScopeInv' : PerScopeInv spec impl alloc ss' is' := {
        semaInv := hSim'.semaInv
        countBalance := hPerScopeGoal.1
        issueOrder := hPerScopeGoal.2.1
        queueOrdered := hPerScopeGoal.2.2.1
        rcMono := hPerScopeGoal.2.2.2.1
        rcBound := hPerScopeGoal.2.2.2.2.1
        pcComplete := hPerScopeGoal.2.2.2.2.2.1
        instrAtPC_atTm1 := hPerScopeGoal.2.2.2.2.2.2
      }

      exact
        ⟨ss', .step ⟨e, hSpecStep⟩ .refl,
         hSim', hSpecInv', hPerScopeInv', hImplInv'⟩

    · -- Silent step: impl took a regOp/internal step, spec unchanged
      have hPerScopeInv' : PerScopeInv spec impl alloc ss is' := {
        semaInv := hSim'.semaInv
        countBalance := hPerScopeInv.countBalance
        issueOrder := hPerScopeInv.issueOrder
        queueOrdered := hPerScopeInv.queueOrdered
        rcMono := hPerScopeInv.rcMono
        rcBound := hPerScopeInv.rcBound
        pcComplete := hPerScopeInv.pcComplete
        instrAtPC_atTm1 := hPerScopeInv.instrAtPC_atTm1
      }

      exact
        ⟨ss, .refl,
         hSim', hSpecInv, hPerScopeInv', hImplInv'⟩
