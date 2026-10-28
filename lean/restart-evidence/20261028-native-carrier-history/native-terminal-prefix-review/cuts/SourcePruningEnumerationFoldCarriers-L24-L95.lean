    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol EnumGuard)
    (target : Nat) (queries : Queries)
    (result : Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourceCurrentAllocatedConjunctionWorker.Outcome width)
      (Option (List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol EnumGuard)))))
    (afterCaller : Caller width) (savedQueries : Queries)
    (after : EnumerationState.State Symbol EnumGuard)
    (total : UnionFind.Total before.representatives)
    (related : ∀ source ∈ sources, UnionFind.SameClass before.representatives target source)
    (references : ReferencesCarry before)
    (observed : run checkEmpty nativeFuel p h sources beforeCaller before target queries =
      (result, afterCaller, savedQueries, after)) :
    UnionFind.Total after.representatives ∧ PreservesCarriers before after ∧ ReferencesCarry after := by
  induction sources generalizing beforeCaller before queries with
  | nil =>
      simp only [run, Prod.mk.injEq] at observed
      rcases observed with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨total, .refl before, references⟩
  | cons source rest ih =>
      rcases dispatchObserved : SourcePruningEnumerationDispatch.dispatch checkEmpty nativeFuel p h
        beforeCaller before source target queries with ⟨dispatchResult, reachedCaller, saved⟩
      cases dispatchResult with
      | error fault =>
          simp only [run, dispatchObserved, Prod.mk.injEq] at observed
          rcases observed with ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨total, .refl before, references⟩
      | ok possible =>
          cases possible with
          | none =>
              simp only [run, dispatchObserved, Prod.mk.injEq] at observed
              rcases observed with ⟨rfl, rfl, rfl, rfl⟩
              exact ⟨total, .refl before, references⟩
          | some action =>
              cases rawObserved : ExceptT.run (action before) with
              | nil =>
                  simp only [run, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
                  rcases observed with ⟨rfl, rfl, rfl, rfl⟩
                  exact ⟨total, .refl before, references⟩
              | cons head tail =>
                  cases head with
                  | error failure =>
                      simp only [run, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
                      rcases observed with ⟨rfl, rfl, rfl, rfl⟩
                      exact ⟨total, .refl before, references⟩
                  | ok pair =>
                      rcases pair with ⟨ignored, middle⟩
                      cases ignored
                      cases tail with
                      | nil =>
                          obtain ⟨forest, middleTotal, middleCarriers, middleReferences⟩ :=
                            SourcePruningEnumerationDispatch.dispatch_carriers checkEmpty nativeFuel p h
                              beforeCaller before source target queries action reachedCaller saved middle
                              total (related source (by simp)) references dispatchObserved rawObserved
                          have tailRelated : ∀ other ∈ rest,
                              UnionFind.SameClass middle.representatives target other := by
                            intro other member
                            rw [forest]
                            exact related other (List.mem_cons_of_mem source member)
                          simp only [run, dispatchObserved, rawObserved] at observed
                          obtain ⟨afterTotal, tailCarriers, afterReferences⟩ :=
                            ih reachedCaller middle saved middleTotal tailRelated middleReferences observed
                          exact ⟨afterTotal, middleCarriers.trans tailCarriers, afterReferences⟩
                      | cons second remaining =>
                          simp only [run, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
                          rcases observed with ⟨rfl, rfl, rfl, rfl⟩
                          exact ⟨total, .refl before, references⟩

end MicroCFTA.SourcePruningEnumerationFold

namespace MicroCFTA.SourcePruningEnumerationCachedAdapter
