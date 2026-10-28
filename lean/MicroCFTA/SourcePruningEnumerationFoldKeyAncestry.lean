import MicroCFTA.SourcePruningEnumerationCachedAdapterKeyAncestry
import MicroCFTA.SourcePruningEnumerationCachedFold

/-!
# Historical key shapes through actual native folds

Each successful dispatcher singleton supplies the next core.
Every attached cache retains keys from the original carrier.
-/
namespace MicroCFTA.SourcePruningEnumerationFold
open EnumerationState EnumerationCorrectness SourcePruningEnumerationKeyAncestry
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {EnumGuard : Type} {width : Nat}
variable {carrier : List (List (List (List Nat)))}

/-- Every fixed-bound fold retains the carrier at its actual outer core. -/
theorem run_key_ancestry
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol EnumGuard)
    (target : Nat) (queries : Queries)
    (result : Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourceCurrentAllocatedConjunctionWorker.Outcome width)
      (Option (List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol EnumGuard)))))
    (afterCaller : Caller width) (savedQueries : Queries)
    (after : EnumerationState.State Symbol EnumGuard)
    (proper : KeyAncestry carrier before)
    (observed : run checkEmpty nativeFuel p h sources beforeCaller before target queries =
      (result, afterCaller, savedQueries, after)) : KeyAncestry carrier after := by
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
                          have middleProper := SourcePruningEnumerationDispatch.dispatch_key_ancestry
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
open EnumerationState SourcePruningEnumerationKeyAncestry InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {width : Nat}
variable {carrier : List (List (List (List Nat)))}

/-- Every actual attached fold cache retains the carrier, including rejection. -/
theorem candidate_key_ancestry
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (caller : Caller width) (before : Cached) (target : Nat) (queries : Queries)
    (valid : KeyAncestry carrier before.core) (after : Cached)
    (candidate : (run checkEmpty nativeFuel p h sources caller before target queries).2 = some after) :
    KeyAncestry carrier after.core := by
  induction sources generalizing caller before queries with
  | nil =>
      simp only [run, Option.some.injEq] at candidate
      subst after
      exact valid
  | cons source rest ih =>
      have headProper := SourcePruningEnumerationCachedAdapter.run_key_ancestry
        checkEmpty nativeFuel p h caller before source target queries valid
      rcases headObserved : SourcePruningEnumerationCachedAdapter.run checkEmpty nativeFuel p h
        caller before source target queries with ⟨outcome, reachedCaller, saved, headCache⟩
      rw [headObserved] at headProper
      dsimp only at headProper
      cases outcome with
      | error fault => simp only [run, headObserved] at candidate; cases candidate
      | ok possible =>
          cases possible with
          | none => simp only [run, headObserved] at candidate; cases candidate
          | some raw =>
              cases raw with
              | nil =>
                  simp only [run, headObserved] at candidate
                  exact headProper.2 after candidate
              | cons row tail =>
                  cases row with
                  | error fault =>
                      simp only [run, headObserved] at candidate
                      exact headProper.2 after candidate
                  | ok payload =>
                      rcases payload with ⟨ignored, core⟩
                      cases ignored
                      cases tail with
                      | cons next later =>
                          simp only [run, headObserved] at candidate
                          exact headProper.2 after candidate
                      | nil =>
                          have coreProper := headProper.1 core rfl
                          cases headCache with
                          | none => simp only [run, headObserved] at candidate; cases candidate
                          | some recovered =>
                              simp only [run, headObserved] at candidate
                              exact ih reachedCaller (EnumerationExpandableIndex.frame core recovered)
                                saved coreProper candidate

end MicroCFTA.SourcePruningEnumerationCachedFold
