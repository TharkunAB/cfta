  obtain ⟨bound, outcome, running, resources, histories, _arityResources, arityHistories⟩ :=
    run_finite_complete_resources_with_history_arity holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel inventory caller memos before metadata seed ceiling packet bounded known
      selectionMembers selectionLength initialMass reserved arity
  have outputCanonical : ∀ output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome,
      Canonical output.cache.core := by
    intro output member
    exact (histories 0 output member).canonical_output canonical
  refine ⟨bound, outcome, running, resources, histories, outputCanonical, ?_⟩
  intro extra output member ambient marker fuel uv after term pending handle bucket value
    discharged observed checked stored decoded
  exact (arityHistories extra output member).render_sound rfl canonical discharged ambient marker fuel uv
    after term pending observed checked handle bucket value stored decoded
