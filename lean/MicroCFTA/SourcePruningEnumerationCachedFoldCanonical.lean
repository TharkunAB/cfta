import MicroCFTA.SourcePruningEnumerationFoldCanonical
import MicroCFTA.SourcePruningEnumerationCachedAdapterCanonical

namespace MicroCFTA.SourcePruningEnumerationCachedFold
open EnumerationState EnumerationValidity InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {width : Nat}

/-- Every actual attached fold cache is canonical, including a rejected prefix cache. -/
theorem candidate_canonical
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (caller : Caller width) (before : Cached) (target : Nat) (queries : Queries)
    (valid : Canonical before.core) (after : Cached)
    (candidate : (run checkEmpty nativeFuel p h sources caller before target queries).2 = some after) :
    Canonical after.core := by
  induction sources generalizing caller before queries with
  | nil =>
      simp only [run, Option.some.injEq] at candidate
      subst after
      exact valid
  | cons source rest ih =>
      have headCanonical := SourcePruningEnumerationCachedAdapter.run_canonical
        checkEmpty nativeFuel p h caller before source target queries valid
      rcases headObserved : SourcePruningEnumerationCachedAdapter.run checkEmpty nativeFuel p h
        caller before source target queries with ⟨outcome, reachedCaller, saved, headCache⟩
      rw [headObserved] at headCanonical
      dsimp only at headCanonical
      cases outcome with
      | error fault => simp only [run, headObserved] at candidate; cases candidate
      | ok possible =>
          cases possible with
          | none => simp only [run, headObserved] at candidate; cases candidate
          | some raw =>
              cases raw with
              | nil =>
                  simp only [run, headObserved] at candidate
                  exact headCanonical.2 after candidate
              | cons row tail =>
                  cases row with
                  | error fault =>
                      simp only [run, headObserved] at candidate
                      exact headCanonical.2 after candidate
                  | ok payload =>
                      rcases payload with ⟨ignored, core⟩
                      cases ignored
                      cases tail with
                      | cons next later =>
                          simp only [run, headObserved] at candidate
                          exact headCanonical.2 after candidate
                      | nil =>
                          have coreValid := headCanonical.1 core rfl
                          cases headCache with
                          | none => simp only [run, headObserved] at candidate; cases candidate
                          | some recovered =>
                              simp only [run, headObserved] at candidate
                              exact ih reachedCaller (EnumerationExpandableIndex.frame core recovered)
                                saved coreValid candidate

end MicroCFTA.SourcePruningEnumerationCachedFold
