theorem run_related
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (related : EnumerationFlatState.Related flat earlier)
    (completed : UnionFind.findRoot representativeFuel earlier.representatives uv = some found)
    (checkEmpty : Bool) (nativeFuel p h : Nat) (beforeCaller : Caller width)
    (incoming : Node) (incomingScs : List EnumerationState.Suspended) (queries : Queries) :
    EnumerationFlatNativeFold.ResultRelated
      (run checkEmpty nativeFuel p h beforeCaller flat uv incoming incomingScs queries)
      (SourcePruningEnumerationIncomingNode.run checkEmpty representativeFuel nativeFuel p h
        beforeCaller earlier uv incoming incomingScs queries) := by
  obtain ⟨rootSame, _sizeSame, retained⟩ :=
    FlatUnionFind.findRoot_represents related.representatives completed
  have readRelated : EnumerationFlatState.Related flat
      {earlier with representatives := found.forest} :=
    EnumerationFlatState.related_forests related related.valid retained
  simp only [run, SourcePruningEnumerationIncomingNode.run, completed, ← rootSame, related.values]
  cases stored : earlier.values[found.representative]? with
  | none => exact ⟨rfl, rfl, readRelated, .cons (.error EnumerationState.Error.invalidSlot) .nil⟩
  | some value =>
    cases value with
    | eliminated => exact ⟨rfl, rfl, readRelated, .cons (.error EnumerationState.Error.invalidIntersection) .nil⟩
    | enumerated fragment => exact ⟨rfl, rfl, readRelated, .cons (.error EnumerationState.Error.invalidIntersection) .nil⟩
    | unenumerated oldNode oldScs =>
      cases oldNode with
      | none =>
        cases encoded : encodeNode incoming with
        | none => exact ⟨rfl, rfl, readRelated, trivial⟩
        | some handle => exact ⟨rfl, rfl, readRelated, finish_related readRelated _ _ _ _ _⟩
      | some oldHandle =>
        dsimp only
        cases decoded : lookupNode beforeCaller.checked.native.machine.heap oldHandle with
        | none => exact ⟨rfl, rfl, readRelated, trivial⟩
        | some old =>
          dsimp only
          generalize SourceEqualityNativeDemand.execute nativeFuel
            (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain incoming old))
            beforeCaller.checked = actual
          cases actual with
          | failed fault checked => exact ⟨rfl, rfl, readRelated, rfl⟩
          | yielded control checked => exact ⟨rfl, rfl, readRelated, rfl⟩
          | constraintError fault checked => exact ⟨rfl, rfl, readRelated, rfl⟩
          | blocked reason control checked => exact ⟨rfl, rfl, readRelated, rfl⟩
          | done query queried =>
            dsimp only
            generalize (if checkEmpty then
              SourcePruningEnumerationEnabledEmpty.check p h query queried beforeCaller.fourth queries
              else (.done false queried beforeCaller.fourth, queries)) = phase
            obtain ⟨outcome, savedQueries⟩ := phase
            cases outcome with
            | failed fault checked saved => exact ⟨rfl, rfl, readRelated, rfl⟩
            | done answer checked saved =>
              dsimp only
              cases encoded : encodeNode (if answer then .empty else query) with
              | none => exact ⟨rfl, rfl, readRelated, trivial⟩
              | some handle => exact ⟨rfl, rfl, readRelated, finish_related readRelated _ _ _ _ _⟩

/-- Every related input supplies one stable sufficient earlier representative bound. -/
theorem run_stable
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (related : EnumerationFlatState.Related flat earlier) (uv : Nat) :
    ∃ representativeFuel, ∀ extra checkEmpty nativeFuel p h (beforeCaller : Caller width)
      incoming incomingScs queries,
      EnumerationFlatNativeFold.ResultRelated
        (run checkEmpty nativeFuel p h beforeCaller flat uv incoming incomingScs queries)
        (SourcePruningEnumerationIncomingNode.run checkEmpty (representativeFuel + extra) nativeFuel p h
          beforeCaller earlier uv incoming incomingScs queries) := by
  obtain ⟨fuel, found, stable, _rootSame, _sizeSame, _retained⟩ :=
    FlatUnionFind.find_stable related.representatives uv
  exact ⟨fuel, fun extra checkEmpty nativeFuel p h beforeCaller incoming incomingScs queries =>
    run_related related (stable extra) checkEmpty nativeFuel p h beforeCaller incoming incomingScs queries⟩

end MicroCFTA.EnumerationFlatNativeIncoming
