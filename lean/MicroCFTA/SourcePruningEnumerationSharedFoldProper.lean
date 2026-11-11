import MicroCFTA.SourcePruningEnumerationSharedDispatchProper
import MicroCFTA.SourcePruningEnumerationSharedTerminalScalarBounds
import MicroCFTA.SourcePruningEnumerationCachedAdapterProper

/-!
# Proper pending paths at actual shared fold outcomes

Successful singleton actions advance the outer state.
Other head outcomes retain the reached prefix state.
Attached caches retain proper paths after empty-row rejection.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedCachedTerminal
open EnumerationState EnumerationCorrectness EnumerationProgress
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {width : Nat}

/-- Every fixed-bound fold outcome retains proper tries at its actual outer core. -/
theorem rawFold_proper
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol Constraint)
    (target : Nat) (queries : Queries)
    (result : Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourcePruningEnumerationSharedEnabledEmpty.Outcome width)
      (Option (List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol Constraint)))))
    (afterCaller : Caller width) (savedQueries : Queries)
    (after : EnumerationState.State Symbol Constraint)
    (proper : ProperState before)
    (observed : rawFold checkEmpty nativeFuel p h sources beforeCaller before target queries =
      (result, afterCaller, savedQueries, after)) : ProperState after := by
  induction sources generalizing beforeCaller before queries with
  | nil =>
      simp only [rawFold, Prod.mk.injEq] at observed
      rcases observed with ⟨rfl, rfl, rfl, rfl⟩
      exact proper
  | cons source rest ih =>
      rcases dispatchObserved : SourcePruningEnumerationSharedDispatch.dispatch checkEmpty nativeFuel p h
        beforeCaller before source target queries with ⟨dispatchResult, reachedCaller, saved⟩
      cases dispatchResult with
      | error fault =>
          simp only [rawFold, dispatchObserved, Prod.mk.injEq] at observed
          rcases observed with ⟨rfl, rfl, rfl, rfl⟩
          exact proper
      | ok possible =>
          cases possible with
          | none =>
              simp only [rawFold, dispatchObserved, Prod.mk.injEq] at observed
              rcases observed with ⟨rfl, rfl, rfl, rfl⟩
              exact proper
          | some action =>
              cases rawObserved : ExceptT.run (action before) with
              | nil =>
                  simp only [rawFold, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
                  rcases observed with ⟨rfl, rfl, rfl, rfl⟩
                  exact proper
              | cons head tail =>
                  cases head with
                  | error failure =>
                      simp only [rawFold, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
                      rcases observed with ⟨rfl, rfl, rfl, rfl⟩
                      exact proper
                  | ok pair =>
                      rcases pair with ⟨ignored, middle⟩
                      cases ignored
                      cases tail with
                      | nil =>
                          have middleProper := SourcePruningEnumerationSharedDispatch.dispatch_proper
                            checkEmpty nativeFuel p h beforeCaller before source target queries action
                            reachedCaller saved middle proper dispatchObserved rawObserved
                          simp only [rawFold, dispatchObserved, rawObserved] at observed
                          exact ih reachedCaller middle saved middleProper observed
                      | cons second remaining =>
                          simp only [rawFold, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
                          rcases observed with ⟨rfl, rfl, rfl, rfl⟩
                          exact proper


/-- Every actual singleton core and every attached cache retain proper suspended tries. -/
private theorem cachedAdapter_proper
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat) (caller : Caller width) (before : Cached)
    (source target : Nat) (queries : Queries) (valid : ProperState before.core) :
    (∀ returned, (cachedAdapter checkEmpty nativeFuel p h caller before source target queries).1 =
      .ok (some [.ok ((), returned)]) → ProperState returned) ∧
    (∀ after, (cachedAdapter checkEmpty nativeFuel p h caller before source target queries).2.2.2 = some after →
      ProperState after.core) := by
  rcases dispatched : SourcePruningEnumerationSharedDispatch.dispatch checkEmpty nativeFuel p h
    caller before.core source target queries with ⟨outcome, reachedCaller, saved⟩
  cases outcome with
  | error fault =>
      simp only [cachedAdapter, dispatched]
      constructor <;> intro after impossible <;> cases impossible
  | ok possible =>
      cases possible with
      | none =>
          simp only [cachedAdapter, dispatched]
          constructor <;> intro after impossible <;> cases impossible
      | some action =>
          simp only [cachedAdapter, dispatched]
          have rows : ∀ returned, ExceptT.run (action before.core) = [.ok ((), returned)] →
              ProperState returned := by
            intro returned completed
            exact SourcePruningEnumerationSharedDispatch.dispatch_proper checkEmpty nativeFuel p h
              caller before.core source target queries action reachedCaller saved returned
              valid dispatched completed
          constructor
          · intro returned same
            exact rows returned (Option.some.inj (Except.ok.inj same))
          · intro after adapted
            exact SourcePruningEnumerationCachedAdapter.adapt_proper valid rows adapted

/-- Cache erasure retains proper pending paths at the actual cached-fold outer core. -/
theorem fold_proper
    [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (beforeCaller : Caller width) (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (target : Nat) (queries : Queries) (valid : ProperState before.core) :
    ProperState (fold checkEmpty nativeFuel p h sources beforeCaller before target queries).1.2.2.2 := by
  exact rawFold_proper checkEmpty nativeFuel p h sources
    beforeCaller before.core target queries
    (fold checkEmpty nativeFuel p h sources beforeCaller before target queries).1.1
    (fold checkEmpty nativeFuel p h sources beforeCaller before target queries).1.2.1
    (fold checkEmpty nativeFuel p h sources beforeCaller before target queries).1.2.2.1
    (fold checkEmpty nativeFuel p h sources beforeCaller before target queries).1.2.2.2
    valid (fold_erase checkEmpty nativeFuel p h sources beforeCaller before target queries).symm

/-- Every actual attached fold cache is proper, including a rejected prefix cache. -/
theorem fold_candidate_proper
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (caller : Caller width) (before : Cached) (target : Nat) (queries : Queries)
    (valid : ProperState before.core) (after : Cached)
    (candidate : (fold checkEmpty nativeFuel p h sources caller before target queries).2 = some after) :
    ProperState after.core := by
  induction sources generalizing caller before queries with
  | nil =>
      simp only [fold, Option.some.injEq] at candidate
      subst after
      exact valid
  | cons source rest ih =>
      have headProper := cachedAdapter_proper
        checkEmpty nativeFuel p h caller before source target queries valid
      rcases headObserved : cachedAdapter checkEmpty nativeFuel p h
        caller before source target queries with ⟨outcome, reachedCaller, saved, headCache⟩
      rw [headObserved] at headProper
      dsimp only at headProper
      cases outcome with
      | error fault => simp only [fold, headObserved] at candidate; cases candidate
      | ok possible =>
          cases possible with
          | none => simp only [fold, headObserved] at candidate; cases candidate
          | some raw =>
              cases raw with
              | nil =>
                  simp only [fold, headObserved] at candidate
                  exact headProper.2 after candidate
              | cons row tail =>
                  cases row with
                  | error fault =>
                      simp only [fold, headObserved] at candidate
                      exact headProper.2 after candidate
                  | ok payload =>
                      rcases payload with ⟨ignored, core⟩
                      cases ignored
                      cases tail with
                      | cons next later =>
                          simp only [fold, headObserved] at candidate
                          exact headProper.2 after candidate
                      | nil =>
                          have coreProper := headProper.1 core rfl
                          cases headCache with
                          | none => simp only [fold, headObserved] at candidate; cases candidate
                          | some recovered =>
                              simp only [fold, headObserved] at candidate
                              exact ih reachedCaller (EnumerationExpandableIndex.frame core recovered)
                                saved coreProper candidate


end MicroCFTA.SourcePruningEnumerationSharedCachedTerminal
