import MicroCFTA.SourcePruningEnumerationCachedFold
import MicroCFTA.SourcePruningEnumerationDispatchShape
import MicroCFTA.SourcePruningEnumerationSuspendedMass

/-!
# Scalar cache bounds at actual terminal fold observations

An actual dispatch singleton keeps its input or assimilates two pending slots.
Both cases preserve the counter and total suspended mass. A rejected action
retains the current fold prefix. These observers require no future admission.
-/
namespace MicroCFTA.SourcePruningEnumerationFold
open EnumerationState EnumerationCorrectness InternedConstructorTemplates
open SourcePruningEnumerationPrefixAdmission (suspendedBound)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Raw" => List (Except EnumerationState.Error (Unit × Core))
variable {width : Nat}
local notation "Observation" => Except
  (SourceEqualityNativeDemand.Outcome width Node ⊕ SourceCurrentAllocatedConjunctionWorker.Outcome width)
  (Option Raw)
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- An actual dispatch singleton preserves the counter and every suspended occurrence. -/
theorem dispatch_counter_mass
    (checkEmpty : Bool) (nativeFuel p h : Nat) (beforeCaller : Caller width) (before : Core)
    (source target : Nat) (queries : Queries) (action : EnumerateM Symbol Constraint Unit)
    (afterCaller : Caller width) (savedQueries : Queries) (after : Core)
    (selected : SourcePruningEnumerationDispatch.dispatch checkEmpty nativeFuel p h
      beforeCaller before source target queries = (.ok (some action), afterCaller, savedQueries))
    (completed : ExceptT.run (action before) = [.ok ((), after)]) :
    after.counter = before.counter ∧ suspendedBound after = suspendedBound before := by
  rcases SourcePruningEnumerationDispatchShape.singleton checkEmpty nativeFuel p h
    beforeCaller before source target queries action afterCaller savedQueries after selected completed with
    rfl | ⟨different, sourceNode, targetNode, merged, sourceScs, targetScs, sourceStored, targetStored, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, SourcePruningEnumerationSuspendedMass.assimilated_mass before source target
      sourceNode targetNode merged sourceScs targetScs sourceStored targetStored (Ne.symm different)⟩

/-- Every actual returned fold prefix preserves counter and suspended mass, for every result tag. -/
theorem observed_counter_mass
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (beforeCaller : Caller width) (before : Core) (target : Nat) (queries : Queries)
    (result : Observation) (afterCaller : Caller width) (savedQueries : Queries) (after : Core)
    (observed : run checkEmpty nativeFuel p h sources beforeCaller before target queries =
      (result, afterCaller, savedQueries, after)) :
    after.counter = before.counter ∧ suspendedBound after = suspendedBound before := by
  induction sources generalizing beforeCaller before queries with
  | nil =>
      simp only [run, Prod.mk.injEq] at observed
      rcases observed with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨rfl, rfl⟩
  | cons source rest ih =>
      rcases dispatchObserved : SourcePruningEnumerationDispatch.dispatch checkEmpty nativeFuel p h
        beforeCaller before source target queries with ⟨dispatchResult, reachedCaller, saved⟩
      cases dispatchResult with
      | error fault =>
          simp only [run, dispatchObserved, Prod.mk.injEq] at observed
          rcases observed with ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨rfl, rfl⟩
      | ok possible =>
          cases possible with
          | none =>
              simp only [run, dispatchObserved, Prod.mk.injEq] at observed
              rcases observed with ⟨rfl, rfl, rfl, rfl⟩
              exact ⟨rfl, rfl⟩
          | some action =>
              cases rawObserved : ExceptT.run (action before) with
              | nil =>
                  simp only [run, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
                  rcases observed with ⟨rfl, rfl, rfl, rfl⟩
                  exact ⟨rfl, rfl⟩
              | cons first tail =>
                  cases first with
                  | error error =>
                      simp only [run, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
                      rcases observed with ⟨rfl, rfl, rfl, rfl⟩
                      exact ⟨rfl, rfl⟩
                  | ok pair =>
                      rcases pair with ⟨valueUnit, middle⟩
                      cases valueUnit
                      cases tail with
                      | nil =>
                          have headBounds := dispatch_counter_mass checkEmpty nativeFuel p h beforeCaller
                            before source target queries action reachedCaller saved middle dispatchObserved rawObserved
                          simp only [run, dispatchObserved, rawObserved] at observed
                          have tailBounds := ih reachedCaller middle saved observed
                          exact ⟨tailBounds.1.trans headBounds.1, tailBounds.2.trans headBounds.2⟩
                      | cons second remaining =>
                          simp only [run, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
                          rcases observed with ⟨rfl, rfl, rfl, rfl⟩
                          exact ⟨rfl, rfl⟩

end MicroCFTA.SourcePruningEnumerationFold

namespace MicroCFTA.SourcePruningEnumerationCachedFold
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationPrefixAdmission (suspendedBound)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Raw" => List (Except EnumerationState.Error (Unit × Core))
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- An actual returned cache preserves the original counter and suspended mass, including raw rejection. -/
theorem observed_cache_bounds
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (beforeCaller : Caller width) (before : Cached) (target : Nat) (queries : Queries)
    (after : Cached)
    (observed : (run checkEmpty nativeFuel p h sources beforeCaller before target queries).2 = some after) :
    after.core.counter = before.core.counter ∧ suspendedBound after.core = suspendedBound before.core := by
  induction sources generalizing beforeCaller before queries with
  | nil =>
      simp only [run, Option.some.injEq] at observed
      subst after
      exact ⟨rfl, rfl⟩
  | cons source rest ih =>
      rcases dispatchObserved : SourcePruningEnumerationDispatch.dispatch checkEmpty nativeFuel p h
        beforeCaller before.core source target queries with ⟨dispatchResult, reachedCaller, saved⟩
      cases dispatchResult with
      | error fault =>
          simp only [run, SourcePruningEnumerationCachedAdapter.run, dispatchObserved] at observed
          cases observed
      | ok possible =>
          cases possible with
          | none =>
              simp only [run, SourcePruningEnumerationCachedAdapter.run, dispatchObserved] at observed
              cases observed
          | some action =>
              cases rawObserved : ExceptT.run (action before.core) with
              | nil =>
                  simp only [run, SourcePruningEnumerationCachedAdapter.run, dispatchObserved,
                    rawObserved, SourcePruningEnumerationCachedAdapter.adapt, Option.some.injEq] at observed
                  subst after
                  exact ⟨rfl, rfl⟩
              | cons first tail =>
                  cases first with
                  | error error =>
                      simp only [run, SourcePruningEnumerationCachedAdapter.run, dispatchObserved,
                        rawObserved, SourcePruningEnumerationCachedAdapter.adapt] at observed
                      cases observed
                  | ok pair =>
                      rcases pair with ⟨valueUnit, middle⟩
                      cases valueUnit
                      cases tail with
                      | nil =>
                          have headBounds := SourcePruningEnumerationFold.dispatch_counter_mass
                            checkEmpty nativeFuel p h beforeCaller before.core source target queries action
                            reachedCaller saved middle dispatchObserved rawObserved
                          cases cacheObserved : SourcePruningEnumerationCachedAdapter.adapt
                              reachedCaller.checked.native.machine.heap before source target [.ok ((), middle)] with
                          | none =>
                              simp only [run, SourcePruningEnumerationCachedAdapter.run, dispatchObserved,
                                rawObserved, cacheObserved] at observed
                              cases observed
                          | some recovered =>
                              simp only [run, SourcePruningEnumerationCachedAdapter.run, dispatchObserved,
                                rawObserved, cacheObserved] at observed
                              have tailBounds := ih reachedCaller (EnumerationExpandableIndex.frame middle recovered) saved observed
                              exact ⟨tailBounds.1.trans headBounds.1, tailBounds.2.trans headBounds.2⟩
                      | cons second remaining =>
                          simp only [run, SourcePruningEnumerationCachedAdapter.run, dispatchObserved,
                            rawObserved, SourcePruningEnumerationCachedAdapter.adapt] at observed
                          cases observed

/-- A full actual successful observation retains both scalar bounds at its outer prefix and returned cache. -/
theorem observed_bounds
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (beforeCaller : Caller width) (before : Cached) (target : Nat) (queries : Queries)
    (raw : Raw) (afterCaller : Caller width) (savedQueries : Queries) (outer : Core) (after : Cached)
    (observed : run checkEmpty nativeFuel p h sources beforeCaller before target queries =
      ((.ok (some raw), afterCaller, savedQueries, outer), some after)) :
    outer.counter = before.core.counter ∧ suspendedBound outer = suspendedBound before.core ∧
    after.core.counter = before.core.counter ∧ suspendedBound after.core = suspendedBound before.core := by
  have erased := erase checkEmpty nativeFuel p h sources beforeCaller before target queries
  rw [observed] at erased
  have outerBounds := SourcePruningEnumerationFold.observed_counter_mass checkEmpty nativeFuel p h
    sources beforeCaller before.core target queries (.ok (some raw)) afterCaller savedQueries outer erased.symm
  have cacheBounds := observed_cache_bounds checkEmpty nativeFuel p h sources beforeCaller before target queries
    after (by rw [observed])
  exact ⟨outerBounds.1, outerBounds.2, cacheBounds.1, cacheBounds.2⟩

end MicroCFTA.SourcePruningEnumerationCachedFold
