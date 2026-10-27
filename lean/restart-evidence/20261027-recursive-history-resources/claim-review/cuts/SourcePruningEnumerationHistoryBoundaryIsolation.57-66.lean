theorem ResourceHistory.isolated_boundary
    (history : ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel
      recursiveFuel inventory caller memos metadata before seed ceiling next output)
    (held heldHandle : Nat) (value : Node)
    (actualNext : next = SourcePruningEnumerationRestart.decision stop order metadata before)
    (isolated : IsolatedPending held heldHandle before.core)
    (decoded : lookupNode caller.checked.native.machine.heap heldHandle = some value)
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true) :
    IsolatedPending held heldHandle output.cache.core ∧
      lookupNode output.caller.checked.native.machine.heap heldHandle = some value := by
