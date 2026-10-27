import MicroCFTA.SourcePruningEnumerationDispatchProper
import MicroCFTA.SourcePruningEnumerationCachedFold

/-!
# ProperState suspended tries at every actual native fold endpoint

Singleton actions advance the proper state.
Every other outcome retains the reached prefix state.
No conclusion requires or asserts Safe.
-/
namespace MicroCFTA.SourcePruningEnumerationFold
open EnumerationState EnumerationCorrectness EnumerationProgress
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {EnumGuard : Type} {width : Nat}

/-- Every fixed-bound fold outcome retains proper tries at its actual outer core. -/
theorem run_proper
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol EnumGuard)
    (target : Nat) (queries : Queries)
    (result : Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourceCurrentAllocatedConjunctionWorker.Outcome width)
      (Option (List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol EnumGuard)))))
    (afterCaller : Caller width) (savedQueries : Queries)
    (after : EnumerationState.State Symbol EnumGuard)
    (proper : ProperState before)
    (observed : run checkEmpty nativeFuel p h sources beforeCaller before target queries =
      (result, afterCaller, savedQueries, after)) : ProperState after := by
  induction sources generalizing beforeCaller before queries with
  | nil =>
      simp only [run, Prod.mk.injEq] at observed
      rcases observed with ⟨rfl, rfl, rfl, rfl⟩
      exact proper
  | cons source rest ih =>
      rcases dispatchObserved : SourcePruningEnumerationDispatch.dispatch checkEmpty nativeFuel p h
        beforeCaller before source target queries with ⟨dispatchResult, reachedCaller, saved⟩
      cases dispatchResult with
      | error fault =>
          simp only [run, dispatchObserved, Prod.mk.injEq] at observed
          rcases observed with ⟨rfl, rfl, rfl, rfl⟩
          exact proper
      | ok possible =>
          cases possible with
          | none =>
              simp only [run, dispatchObserved, Prod.mk.injEq] at observed
              rcases observed with ⟨rfl, rfl, rfl, rfl⟩
              exact proper
          | some action =>
              cases rawObserved : ExceptT.run (action before) with
              | nil =>
                  simp only [run, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
                  rcases observed with ⟨rfl, rfl, rfl, rfl⟩
                  exact proper
              | cons head tail =>
                  cases head with
                  | error failure =>
                      simp only [run, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
                      rcases observed with ⟨rfl, rfl, rfl, rfl⟩
                      exact proper
                  | ok pair =>
                      rcases pair with ⟨ignored, middle⟩
                      cases ignored
                      cases tail with
                      | nil =>
                          have middleProper := SourcePruningEnumerationDispatch.dispatch_proper
                            checkEmpty nativeFuel p h beforeCaller before source target queries action
                            reachedCaller saved middle proper dispatchObserved rawObserved
                          simp only [run, dispatchObserved, rawObserved] at observed
                          exact ih reachedCaller middle saved middleProper observed
                      | cons second remaining =>
                          simp only [run, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
                          rcases observed with ⟨rfl, rfl, rfl, rfl⟩
                          exact proper

end MicroCFTA.SourcePruningEnumerationFold

namespace MicroCFTA.SourcePruningEnumerationCachedFold
open EnumerationState EnumerationProgress
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {width : Nat}

/-- Cache erasure transfers properity to the actual bounded cached-fold outer core. -/
theorem proper
    [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (beforeCaller : Caller width) (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (target : Nat) (queries : Queries) (valid : ProperState before.core) :
    ProperState (run checkEmpty nativeFuel p h sources beforeCaller before target queries).1.2.2.2 := by
  exact SourcePruningEnumerationFold.run_proper checkEmpty nativeFuel p h sources
    beforeCaller before.core target queries
    (run checkEmpty nativeFuel p h sources beforeCaller before target queries).1.1
    (run checkEmpty nativeFuel p h sources beforeCaller before target queries).1.2.1
    (run checkEmpty nativeFuel p h sources beforeCaller before target queries).1.2.2.1
    (run checkEmpty nativeFuel p h sources beforeCaller before target queries).1.2.2.2
    valid (erase checkEmpty nativeFuel p h sources beforeCaller before target queries).symm

end MicroCFTA.SourcePruningEnumerationCachedFold
