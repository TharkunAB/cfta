      formulas solver recursiveFuel inventory caller memos before metadata seed ceiling packet bounded known
      selectionMembers selectionLength initialMass reserved
  obtain ⟨arityBound, arityOutcome, arityRunning, _arityResources, strengthened⟩ :=
    run_finite_complete_resources_arity holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel inventory caller memos before metadata seed ceiling packet bounded known
      selectionMembers selectionLength initialMass reserved arity
  have oldAt := running arityBound
  have newAt := arityRunning historyBound
  have fuelSame : arityBound + historyBound = historyBound + arityBound := by omega
  rw [fuelSame] at newAt
  have outcomeSame : arityOutcome = outcome := newAt.symm.trans oldAt
  rw [outcomeSame] at strengthened
  have outputHeaps : ∀ output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome,
      ArityHeap output.caller.checked.native.machine.heap := by
    obtain ⟨_reached, _next, _final, _post, _bounded, _known, _arity, shape⟩ := strengthened
    cases outcome with
    | complete outputs reached saved =>
        intro output member
        exact (shape.2.2 output member).2
    | stopped outputs reason endpoint =>
        intro output member
        exact (shape.2 output member).2
  have historiesAt : ∀ extra output, output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome →
      ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver
        (historyBound + arityBound + extra) recursiveFuel inventory caller memos metadata before seed ceiling
        (SourcePruningEnumerationRestart.decision stop order metadata before) output := by
    intro extra output member
    simpa only [Nat.add_assoc] using histories (arityBound + extra) output member
  refine ⟨historyBound + arityBound, outcome, ?_, resources, historiesAt, strengthened, ?_⟩
  · intro extra
    simpa only [Nat.add_assoc] using running (arityBound + extra)
  · intro extra output member
    exact (historiesAt extra output member).with_arity_of_output_heap (outputHeaps output member)
