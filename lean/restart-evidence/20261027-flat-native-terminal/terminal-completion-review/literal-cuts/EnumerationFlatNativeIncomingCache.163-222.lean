theorem run_stable
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (related : Related flat earlier) (checkEmpty : Bool) (nativeFuel p h : Nat)
    (beforeCaller : Caller width) (target : Nat) (incoming : Node)
    (incomingScs : List EnumerationState.Suspended) (queries : Queries) :
    ∃ representativeFuel indexFuel, ∀ extraRepresentative extraIndex,
      EnumerationFlatNativeCachedFold.ResultRelated
        (run checkEmpty nativeFuel p h beforeCaller flat target incoming incomingScs queries)
        (SourcePruningEnumerationIncomingCacheAdapter.run checkEmpty
          (representativeFuel + extraRepresentative) nativeFuel p h (indexFuel + extraIndex)
          beforeCaller earlier target incoming incomingScs queries) := by
  obtain ⟨r, found, stable, _rootSame, _sizeSame, _retained⟩ :=
    FlatUnionFind.find_stable related.core.representatives target
  have rawRelated := EnumerationFlatNativeIncoming.run_related related.core
    (stable 0) checkEmpty nativeFuel p h beforeCaller incoming incomingScs queries
  simp only [Nat.add_zero] at rawRelated
  have oldStable : ∀ extra, SourcePruningEnumerationIncomingNode.run checkEmpty
      (r + extra) nativeFuel p h beforeCaller earlier.core target incoming incomingScs queries =
      SourcePruningEnumerationIncomingNode.run checkEmpty r nativeFuel p h
        beforeCaller earlier.core target incoming incomingScs queries := by
    intro extra
    simp only [SourcePruningEnumerationIncomingNode.run, stable extra,
      show UnionFind.findRoot r earlier.core.representatives target = some found from by
        simpa only [Nat.add_zero] using stable 0]
  generalize flatRun : EnumerationFlatNativeIncoming.run checkEmpty nativeFuel p h
    beforeCaller flat.core target incoming incomingScs queries = left at rawRelated ⊢
  generalize oldRun : SourcePruningEnumerationIncomingNode.run checkEmpty r nativeFuel p h
    beforeCaller earlier.core target incoming incomingScs queries = right at rawRelated oldStable ⊢
  obtain ⟨leftResult, reachedCaller, savedQueries, readFlat⟩ := left
  obtain ⟨rightResult, oldCaller, oldQueries, readEarlier⟩ := right
  obtain ⟨callerSame, queriesSame, reads, rows⟩ := rawRelated
  dsimp only at callerSame queriesSame
  subst oldCaller oldQueries
  obtain ⟨k, counts⟩ := EnumerationFlatNativeIndex.count_stable reads.representatives incomingScs
  refine ⟨r, k, ?_⟩
  intro extraRepresentative extraIndex
  simp only [run, SourcePruningEnumerationIncomingCacheAdapter.run, flatRun, oldStable extraRepresentative]
  refine ⟨⟨rfl, rfl, reads, rows⟩, ?_⟩
  cases leftResult with
  | error first =>
    cases rightResult with
    | error second => trivial
    | ok value => cases rows
  | ok leftValue =>
    cases rightResult with
    | error fault => cases leftValue <;> cases rows
    | ok rightValue =>
      cases leftValue with
      | none =>
        cases rightValue with
        | none => trivial
        | some raw => cases rows
      | some leftRows =>
        cases rightValue with
        | none => cases rows
        | some rightRows =>
          exact adapt_related related reads _ (k + extraIndex) target incomingScs
            (counts extraIndex 1) rows

end MicroCFTA.EnumerationFlatNativeIncomingCache
