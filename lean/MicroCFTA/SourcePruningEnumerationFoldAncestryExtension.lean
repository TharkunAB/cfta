import MicroCFTA.SourcePruningEnumerationCachedAdapterAncestryExtension
import MicroCFTA.SourcePruningEnumerationCachedFold

/-!
# Recursion ancestry through actual native folds

Each successful dispatcher singleton supplies the next core.
All-slot extensions compose and expansion ancestry remains exact.
-/
namespace MicroCFTA.SourcePruningEnumerationFold
open EnumerationState EnumerationCorrectness SourcePruningEnumerationAncestryExtension
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {EnumGuard : Type} {width : Nat}

/-- Every actual fold extends all slots and retains expansion ancestry at its outer core. -/
theorem run_ancestry_extension
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol EnumGuard)
    (target : Nat) (queries : Queries)
    (result : Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourceCurrentAllocatedConjunctionWorker.Outcome width)
      (Option (List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol EnumGuard)))))
    (afterCaller : Caller width) (savedQueries : Queries)
    (after : EnumerationState.State Symbol EnumGuard)
    (observed : run checkEmpty nativeFuel p h sources beforeCaller before target queries =
      (result, afterCaller, savedQueries, after)) :
    Extends before after ∧ after.expansionAncestry = before.expansionAncestry := by
  induction sources generalizing beforeCaller before queries with
  | nil =>
      simp only [run, Prod.mk.injEq] at observed
      rcases observed with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨Extends.refl before, rfl⟩
  | cons source rest ih =>
      rcases dispatchObserved : SourcePruningEnumerationDispatch.dispatch checkEmpty nativeFuel p h
        beforeCaller before source target queries with ⟨dispatchResult, reachedCaller, saved⟩
      cases dispatchResult with
      | error fault =>
          simp only [run, dispatchObserved, Prod.mk.injEq] at observed
          rcases observed with ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨Extends.refl before, rfl⟩
      | ok possible =>
          cases possible with
          | none =>
              simp only [run, dispatchObserved, Prod.mk.injEq] at observed
              rcases observed with ⟨rfl, rfl, rfl, rfl⟩
              exact ⟨Extends.refl before, rfl⟩
          | some action =>
              cases rawObserved : ExceptT.run (action before) with
              | nil =>
                  simp only [run, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
                  rcases observed with ⟨rfl, rfl, rfl, rfl⟩
                  exact ⟨Extends.refl before, rfl⟩
              | cons head tail =>
                  cases head with
                  | error failure =>
                      simp only [run, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
                      rcases observed with ⟨rfl, rfl, rfl, rfl⟩
                      exact ⟨Extends.refl before, rfl⟩
                  | ok pair =>
                      rcases pair with ⟨ignored, middle⟩
                      cases ignored
                      cases tail with
                      | nil =>
                          have middleFields := SourcePruningEnumerationDispatch.dispatch_ancestry_extension
                            checkEmpty nativeFuel p h beforeCaller before source target queries action
                            reachedCaller saved middle dispatchObserved rawObserved
                          simp only [run, dispatchObserved, rawObserved] at observed
                          have tailFields := ih reachedCaller middle saved observed
                          exact ⟨middleFields.1.trans tailFields.1, tailFields.2.trans middleFields.2⟩
                      | cons second remaining =>
                          simp only [run, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
                          rcases observed with ⟨rfl, rfl, rfl, rfl⟩
                          exact ⟨Extends.refl before, rfl⟩

end MicroCFTA.SourcePruningEnumerationFold

namespace MicroCFTA.SourcePruningEnumerationCachedFold
open EnumerationState SourcePruningEnumerationAncestryExtension InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {width : Nat}

/-- Every actual attached fold cache extends all slots, including rejection. -/
theorem candidate_ancestry_extension
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (caller : Caller width) (before : Cached) (target : Nat) (queries : Queries)
    (after : Cached)
    (candidate : (run checkEmpty nativeFuel p h sources caller before target queries).2 = some after) :
    Extends before.core after.core ∧ after.core.expansionAncestry = before.core.expansionAncestry := by
  induction sources generalizing caller before queries with
  | nil =>
      simp only [run, Option.some.injEq] at candidate
      subst after
      exact ⟨Extends.refl before.core, rfl⟩
  | cons source rest ih =>
      have headFields := SourcePruningEnumerationCachedAdapter.run_ancestry_extension
        checkEmpty nativeFuel p h caller before source target queries
      rcases headObserved : SourcePruningEnumerationCachedAdapter.run checkEmpty nativeFuel p h
        caller before source target queries with ⟨outcome, reachedCaller, saved, headCache⟩
      rw [headObserved] at headFields
      dsimp only at headFields
      cases outcome with
      | error fault => simp only [run, headObserved] at candidate; cases candidate
      | ok possible =>
          cases possible with
          | none => simp only [run, headObserved] at candidate; cases candidate
          | some raw =>
              cases raw with
              | nil =>
                  simp only [run, headObserved] at candidate
                  exact headFields.2 after candidate
              | cons row tail =>
                  cases row with
                  | error fault =>
                      simp only [run, headObserved] at candidate
                      exact headFields.2 after candidate
                  | ok payload =>
                      rcases payload with ⟨ignored, core⟩
                      cases ignored
                      cases tail with
                      | cons next later =>
                          simp only [run, headObserved] at candidate
                          exact headFields.2 after candidate
                      | nil =>
                          have coreFields := headFields.1 core rfl
                          cases headCache with
                          | none => simp only [run, headObserved] at candidate; cases candidate
                          | some recovered =>
                              simp only [run, headObserved] at candidate
                              have tailFields := ih reachedCaller (EnumerationExpandableIndex.frame core recovered)
                                saved candidate
                              exact ⟨coreFields.1.trans tailFields.1, tailFields.2.trans coreFields.2⟩

end MicroCFTA.SourcePruningEnumerationCachedFold
