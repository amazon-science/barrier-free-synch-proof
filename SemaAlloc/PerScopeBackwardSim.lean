import SemaAlloc.PerScopeInvStep

-- per-loop backward simulation star (direct induction with PerScopeInv threading)
theorem perScope_backward_sim_star (spec : Program) (impl : ImplProgram) (alloc : PerScopeAllocR spec impl)
    (ss : SpecState) (is is' : ImplState)
    (hSim : MatchStates spec impl alloc.toAllocBase (perScopeSemaInv spec alloc) ss is)
    (hStar : ImplStarAny impl is is')
    (hWf : Allocatable spec) (hSpecInv : SpecInv spec ss)
    (hUniq : UniqueScopeIds spec.body) (hUniqueInstr : UniqueInstrIds spec.engines spec.body)
    (hPerScopeInv : PerScopeInv spec impl alloc ss is)
    : ∃ ss', SpecStar spec ss ss' ∧ MatchStates spec impl alloc.toAllocBase (perScopeSemaInv spec alloc) ss' is' := by
  induction hStar generalizing ss with
  | refl => exact ⟨ss, SpecStar.refl, hSim⟩
  | step hStep hRest ih =>
    obtain ⟨e, hStep⟩ := hStep
    have hEngines : e ∈ spec.engines := congrArg ProgramBase.engines alloc.baseEq ▸ hStep.mem_engines
    rcases perScope_backward_sim_step spec impl alloc e ss _ _ hSim hStep hWf hSpecInv hUniq hUniqueInstr hEngines hPerScopeInv with
      ⟨ss', hSpecStep, hSim'⟩ | hSim'
    · have hSpecInv' := specInv_step spec e ss ss' hUniq hSpecInv hSpecStep
      -- PerScopeInv preservation through spec step (Inv2-7 for ss')
      have hPres := perScopeInv_spec_step spec impl alloc e ss ss' hSpecStep hPerScopeInv hSpecInv hUniqueInstr hUniq
      obtain ⟨hInv2', hInv3', hInv4', hInv5', hInv6', hInv7', hPC'⟩ := hPres
      obtain ⟨ss'', hStar', hSim''⟩ := ih ss' hSim' hSpecInv'
        ⟨hSim'.semaInv, hInv2', hInv3', hInv4', hInv5', hInv6', hInv7', hPC'⟩
      exact ⟨ss'', SpecStar.step ⟨e, hSpecStep⟩ hStar', hSim''⟩
    · exact ih ss hSim' hSpecInv ⟨hSim'.semaInv, hPerScopeInv.countBalance, hPerScopeInv.issueOrder, hPerScopeInv.queueOrdered, hPerScopeInv.rcMono, hPerScopeInv.rcBound, hPerScopeInv.pcComplete, hPerScopeInv.instrAtPC_atTm1⟩
