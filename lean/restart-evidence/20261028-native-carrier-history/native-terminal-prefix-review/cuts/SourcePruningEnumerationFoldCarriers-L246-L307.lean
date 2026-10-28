theorem candidate_carriers
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (caller : Caller width) (before : Cached) (target : Nat) (queries : Queries)
    (total : UnionFind.Total before.core.representatives)
    (related : ∀ source ∈ sources, UnionFind.SameClass before.core.representatives target source)
    (references : ReferencesCarry before.core) (after : Cached)
    (candidate : (run checkEmpty nativeFuel p h sources caller before target queries).2 = some after) :
    UnionFind.Total after.core.representatives ∧ PreservesCarriers before.core after.core ∧
      ReferencesCarry after.core := by
  induction sources generalizing caller before queries with
  | nil =>
      simp only [run, Option.some.injEq] at candidate
      subst after
      exact ⟨total, .refl before.core, references⟩
  | cons source rest ih =>
      have headCarriers := SourcePruningEnumerationCachedAdapter.run_carriers
        checkEmpty nativeFuel p h caller before source target queries total
          (related source (by simp)) references
      rcases headObserved : SourcePruningEnumerationCachedAdapter.run checkEmpty nativeFuel p h
        caller before source target queries with ⟨outcome, reachedCaller, saved, headCache⟩
      rw [headObserved] at headCarriers
      dsimp only at headCarriers
      cases outcome with
      | error fault => simp only [run, headObserved] at candidate; cases candidate
      | ok possible =>
          cases possible with
          | none => simp only [run, headObserved] at candidate; cases candidate
          | some raw =>
              cases raw with
              | nil =>
                  simp only [run, headObserved] at candidate
                  exact (headCarriers.2 after candidate).2
              | cons row tail =>
                  cases row with
                  | error fault =>
                      simp only [run, headObserved] at candidate
                      exact (headCarriers.2 after candidate).2
                  | ok payload =>
                      rcases payload with ⟨ignored, core⟩
                      cases ignored
                      cases tail with
                      | cons next later =>
                          simp only [run, headObserved] at candidate
                          exact (headCarriers.2 after candidate).2
                      | nil =>
                          have coreCarriers := headCarriers.1 core rfl
                          have tailRelated : ∀ other ∈ rest,
                              UnionFind.SameClass core.representatives target other := by
                            intro other member
                            rw [coreCarriers.1]
                            exact related other (List.mem_cons_of_mem source member)
                          cases headCache with
                          | none => simp only [run, headObserved] at candidate; cases candidate
                          | some recovered =>
                              simp only [run, headObserved] at candidate
                              obtain ⟨afterTotal, tailCarriers, afterReferences⟩ :=
                                ih reachedCaller (EnumerationExpandableIndex.frame core recovered) saved
                                  coreCarriers.2.1 tailRelated coreCarriers.2.2.2 candidate
                              exact ⟨afterTotal, coreCarriers.2.2.1.trans tailCarriers, afterReferences⟩

end MicroCFTA.SourcePruningEnumerationCachedFold
