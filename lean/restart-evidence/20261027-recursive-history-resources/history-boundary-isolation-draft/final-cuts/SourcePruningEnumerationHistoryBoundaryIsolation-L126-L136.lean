/-- The same output cannot satisfy full structural discharge while that original marker remains. -/
theorem ResourceHistory.not_discharged
    (history : ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel
      recursiveFuel inventory caller memos metadata before seed ceiling next output)
    (held heldHandle : Nat) (value : Node)
    (actualNext : next = SourcePruningEnumerationRestart.decision stop order metadata before)
    (isolated : IsolatedPending held heldHandle before.core)
    (decoded : lookupNode caller.checked.native.machine.heap heldHandle = some value)
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true) :
    ¬SourcePruningEnumerationRendering.Discharged output.cache.core :=
  (history.isolated_boundary held heldHandle value actualNext isolated decoded boundary).1.not_discharged
