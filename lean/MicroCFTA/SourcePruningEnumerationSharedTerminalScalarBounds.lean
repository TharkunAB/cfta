import MicroCFTA.SourcePruningEnumerationSharedDispatchScalarBounds
import MicroCFTA.SourcePruningEnumerationSharedIncomingScalarBounds
import MicroCFTA.SourcePruningEnumerationTerminalPrefixBounds


/-!
# Scalar cache bounds at actual terminal fold observations

An actual dispatch singleton keeps its input or assimilates two pending slots.
Both cases preserve the counter and total suspended mass. A rejected action
retains the current fold prefix. These observers require no future admission.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedCachedTerminal
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
  (SourceEqualityNativeDemand.Outcome width Node ⊕ SourcePruningEnumerationSharedEnabledEmpty.Outcome width)
  (Option Raw)
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- An actual dispatch singleton preserves the counter and every suspended occurrence. -/
theorem dispatch_counter_mass
    (checkEmpty : Bool) (nativeFuel p h : Nat) (beforeCaller : Caller width) (before : Core)
    (source target : Nat) (queries : Queries) (action : EnumerateM Symbol Constraint Unit)
    (afterCaller : Caller width) (savedQueries : Queries) (after : Core)
    (selected : SourcePruningEnumerationSharedDispatch.dispatch checkEmpty nativeFuel p h
      beforeCaller before source target queries = (.ok (some action), afterCaller, savedQueries))
    (completed : ExceptT.run (action before) = [.ok ((), after)]) :
    after.counter = before.counter ∧ suspendedBound after = suspendedBound before := by
  rcases SourcePruningEnumerationSharedDispatchScalarBounds.singleton checkEmpty nativeFuel p h
    beforeCaller before source target queries action afterCaller savedQueries after selected completed with
    rfl | ⟨different, sourceNode, targetNode, merged, sourceScs, targetScs, sourceStored, targetStored, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, SourcePruningEnumerationSuspendedMass.assimilated_mass before source target
      sourceNode targetNode merged sourceScs targetScs sourceStored targetStored (Ne.symm different)⟩

/-- The raw singleton core is the exact returned outer fold core. -/
theorem rawFold_singleton_core
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (beforeCaller : Caller width) (before : Core) (target : Nat) (queries : Queries)
    (returned : Core) (afterCaller : Caller width) (savedQueries : Queries) (outer : Core)
    (observed : rawFold checkEmpty nativeFuel p h sources beforeCaller before target queries =
      (.ok (some [.ok ((), returned)]), afterCaller, savedQueries, outer)) :
    returned = outer := by
  induction sources generalizing beforeCaller before queries with
  | nil =>
    simp only [rawFold, Prod.mk.injEq, Except.ok.injEq, Option.some.injEq,
      List.cons.injEq, and_true, true_and] at observed
    rcases observed with ⟨rfl, _callerSame, _querySame, rfl⟩
    rfl
  | cons source rest ih =>
    rcases dispatchObserved : SourcePruningEnumerationSharedDispatch.dispatch checkEmpty nativeFuel p h
        beforeCaller before source target queries with ⟨dispatchResult, reachedCaller, saved⟩
    cases dispatchResult with
    | error fault => simp only [rawFold, dispatchObserved] at observed; cases observed
    | ok possible =>
      cases possible with
      | none => simp only [rawFold, dispatchObserved] at observed; cases observed
      | some action =>
        cases rawObserved : ExceptT.run (action before) with
        | nil => simp only [rawFold, dispatchObserved, rawObserved] at observed; cases observed
        | cons first tail =>
          cases first with
          | error fault => simp only [rawFold, dispatchObserved, rawObserved] at observed; cases observed
          | ok pair =>
            rcases pair with ⟨valueUnit, middle⟩
            cases valueUnit
            cases tail with
            | cons second remaining =>
              simp only [rawFold, dispatchObserved, rawObserved] at observed
              cases observed
            | nil =>
              simp only [rawFold, dispatchObserved, rawObserved] at observed
              exact ih reachedCaller middle saved observed

/-- Every actual returned fold prefix preserves counter and suspended mass, for every result tag. -/
theorem rawFold_observed_counter_mass
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (beforeCaller : Caller width) (before : Core) (target : Nat) (queries : Queries)
    (result : Observation) (afterCaller : Caller width) (savedQueries : Queries) (after : Core)
    (observed : rawFold checkEmpty nativeFuel p h sources beforeCaller before target queries =
      (result, afterCaller, savedQueries, after)) :
    after.counter = before.counter ∧ suspendedBound after = suspendedBound before := by
  induction sources generalizing beforeCaller before queries with
  | nil =>
      simp only [rawFold, Prod.mk.injEq] at observed
      rcases observed with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨rfl, rfl⟩
  | cons source rest ih =>
      rcases dispatchObserved : SourcePruningEnumerationSharedDispatch.dispatch checkEmpty nativeFuel p h
        beforeCaller before source target queries with ⟨dispatchResult, reachedCaller, saved⟩
      cases dispatchResult with
      | error fault =>
          simp only [rawFold, dispatchObserved, Prod.mk.injEq] at observed
          rcases observed with ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨rfl, rfl⟩
      | ok possible =>
          cases possible with
          | none =>
              simp only [rawFold, dispatchObserved, Prod.mk.injEq] at observed
              rcases observed with ⟨rfl, rfl, rfl, rfl⟩
              exact ⟨rfl, rfl⟩
          | some action =>
              cases rawObserved : ExceptT.run (action before) with
              | nil =>
                  simp only [rawFold, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
                  rcases observed with ⟨rfl, rfl, rfl, rfl⟩
                  exact ⟨rfl, rfl⟩
              | cons first tail =>
                  cases first with
                  | error error =>
                      simp only [rawFold, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
                      rcases observed with ⟨rfl, rfl, rfl, rfl⟩
                      exact ⟨rfl, rfl⟩
                  | ok pair =>
                      rcases pair with ⟨valueUnit, middle⟩
                      cases valueUnit
                      cases tail with
                      | nil =>
                          have headBounds := dispatch_counter_mass checkEmpty nativeFuel p h beforeCaller
                            before source target queries action reachedCaller saved middle dispatchObserved rawObserved
                          simp only [rawFold, dispatchObserved, rawObserved] at observed
                          have tailBounds := ih reachedCaller middle saved observed
                          exact ⟨tailBounds.1.trans headBounds.1, tailBounds.2.trans headBounds.2⟩
                      | cons second remaining =>
                          simp only [rawFold, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
                          rcases observed with ⟨rfl, rfl, rfl, rfl⟩
                          exact ⟨rfl, rfl⟩

end MicroCFTA.SourcePruningEnumerationSharedCachedTerminal


namespace MicroCFTA.SourcePruningEnumerationSharedCachedTerminal
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
theorem fold_observed_cache_bounds
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (beforeCaller : Caller width) (before : Cached) (target : Nat) (queries : Queries)
    (after : Cached)
    (observed : (fold checkEmpty nativeFuel p h sources beforeCaller before target queries).2 = some after) :
    after.core.counter = before.core.counter ∧ suspendedBound after.core = suspendedBound before.core := by
  induction sources generalizing beforeCaller before queries with
  | nil =>
      simp only [fold, Option.some.injEq] at observed
      subst after
      exact ⟨rfl, rfl⟩
  | cons source rest ih =>
      rcases dispatchObserved : SourcePruningEnumerationSharedDispatch.dispatch checkEmpty nativeFuel p h
        beforeCaller before.core source target queries with ⟨dispatchResult, reachedCaller, saved⟩
      cases dispatchResult with
      | error fault =>
          simp only [fold, cachedAdapter, dispatchObserved] at observed
          cases observed
      | ok possible =>
          cases possible with
          | none =>
              simp only [fold, cachedAdapter, dispatchObserved] at observed
              cases observed
          | some action =>
              cases rawObserved : ExceptT.run (action before.core) with
              | nil =>
                  simp only [fold, cachedAdapter, dispatchObserved,
                    rawObserved, SourcePruningEnumerationCachedAdapter.adapt, Option.some.injEq] at observed
                  subst after
                  exact ⟨rfl, rfl⟩
              | cons first tail =>
                  cases first with
                  | error error =>
                      simp only [fold, cachedAdapter, dispatchObserved,
                        rawObserved, SourcePruningEnumerationCachedAdapter.adapt] at observed
                      cases observed
                  | ok pair =>
                      rcases pair with ⟨valueUnit, middle⟩
                      cases valueUnit
                      cases tail with
                      | nil =>
                          have headBounds := dispatch_counter_mass
                            checkEmpty nativeFuel p h beforeCaller before.core source target queries action
                            reachedCaller saved middle dispatchObserved rawObserved
                          cases cacheObserved : SourcePruningEnumerationCachedAdapter.adapt
                              reachedCaller.checked.native.machine.heap before source target [.ok ((), middle)] with
                          | none =>
                              simp only [fold, cachedAdapter, dispatchObserved,
                                rawObserved, cacheObserved] at observed
                              cases observed
                          | some recovered =>
                              simp only [fold, cachedAdapter, dispatchObserved,
                                rawObserved, cacheObserved] at observed
                              have tailBounds := ih reachedCaller (EnumerationExpandableIndex.frame middle recovered) saved observed
                              exact ⟨tailBounds.1.trans headBounds.1, tailBounds.2.trans headBounds.2⟩
                      | cons second remaining =>
                          simp only [fold, cachedAdapter, dispatchObserved,
                            rawObserved, SourcePruningEnumerationCachedAdapter.adapt] at observed
                          cases observed

/-- A full actual successful observation retains both scalar bounds at its outer prefix and returned cache. -/
theorem fold_observed_bounds
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (beforeCaller : Caller width) (before : Cached) (target : Nat) (queries : Queries)
    (raw : Raw) (afterCaller : Caller width) (savedQueries : Queries) (outer : Core) (after : Cached)
    (observed : fold checkEmpty nativeFuel p h sources beforeCaller before target queries =
      ((.ok (some raw), afterCaller, savedQueries, outer), some after)) :
    outer.counter = before.core.counter ∧ suspendedBound outer = suspendedBound before.core ∧
    after.core.counter = before.core.counter ∧ suspendedBound after.core = suspendedBound before.core := by
  have erased := fold_erase checkEmpty nativeFuel p h sources beforeCaller before target queries
  rw [observed] at erased
  have outerBounds := rawFold_observed_counter_mass checkEmpty nativeFuel p h
    sources beforeCaller before.core target queries (.ok (some raw)) afterCaller savedQueries outer erased.symm
  have cacheBounds := fold_observed_cache_bounds checkEmpty nativeFuel p h sources beforeCaller before target queries
    after (by rw [observed])
  exact ⟨outerBounds.1, outerBounds.2, cacheBounds.1, cacheBounds.2⟩

end MicroCFTA.SourcePruningEnumerationSharedCachedTerminal


/-!
# Scalar bounds for actual terminal cache returns

The terminal prefix and source fold preserve suspended mass. The incoming
write adds its own bucket. Rejected folds retain their actual prefix cache.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedCachedTerminal
open EnumerationState EnumerationCorrectness InternedConstructorTemplates
open SourcePruningEnumerationPrefixAdmission (suspendedBound)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual returned terminal cache retains its counter and adds at most the incoming bucket. -/
theorem observed_cache_bounds
    (checkEmpty : Bool) (r n p h k : Nat) (first : Suspended) (rest : List Suspended)
    (beforeCaller : Caller width) (before : Cached) (incoming : Node)
    (incomingScs : List Suspended) (queries : Queries) (after : Cached)
    (observed : (run checkEmpty r n p h k first rest beforeCaller before
      incoming incomingScs queries).2 = some after) :
    after.core.counter = before.core.counter ∧
      suspendedBound after.core ≤ suspendedBound before.core + incomingScs.length := by
  by_cases empty : incoming = .empty
  · simp only [run, ite_eq_left empty, Option.some.injEq] at observed
    subst after
    exact ⟨rfl, Nat.le_add_right _ _⟩
  · cases prefixObserved : ExceptT.run (SourcePruningEnumerationTerminalPrefix.run
        r first rest before.waiting before.core) with
    | nil => simp only [run, ite_eq_right empty, prefixObserved] at observed; cases observed
    | cons prefixEntry prefixTail =>
      cases prefixEntry with
      | error fault => simp only [run, ite_eq_right empty, prefixObserved] at observed; cases observed
      | ok prefixResult =>
        rcases prefixResult with ⟨⟨recorded, winner, moved⟩, joined⟩
        cases prefixTail with
        | cons second remaining =>
          simp only [run, ite_eq_right empty, prefixObserved] at observed
          cases observed
        | nil =>
          have prefixBounds := SourcePruningEnumerationTerminalPrefix.observed_counter_mass
            r first rest before.waiting before.core joined (recorded, winner, moved) prefixObserved
          rcases foldObserved : fold checkEmpty n p h recorded
              beforeCaller ⟨joined, before.expandable, moved⟩ winner queries with
            ⟨⟨foldOutcome, foldCaller, foldQueries, foldOuter⟩, foldCache⟩
          simp only [run, ite_eq_right empty, prefixObserved, foldObserved] at observed
          cases foldOutcome with
          | error fault => cases observed
          | ok possible =>
            cases possible with
            | none => cases observed
            | some foldRaw =>
              cases foldRaw with
              | nil =>
                have foldBounds := fold_observed_cache_bounds
                  checkEmpty n p h recorded beforeCaller ⟨joined, before.expandable, moved⟩
                  winner queries after (by rw [foldObserved]; exact observed)
                exact ⟨foldBounds.1.trans prefixBounds.1, by
                  rw [foldBounds.2, prefixBounds.2]
                  exact Nat.le_add_right _ _⟩
              | cons foldEntry foldTail =>
                cases foldEntry with
                | error fault => cases observed
                | ok foldPair =>
                  rcases foldPair with ⟨foldUnit, folded⟩
                  cases foldUnit
                  cases foldTail with
                  | cons second remaining => cases observed
                  | nil =>
                    have erased := fold_erase checkEmpty n p h recorded
                      beforeCaller ⟨joined, before.expandable, moved⟩ winner queries
                    rw [foldObserved] at erased
                    have foldedSame := rawFold_singleton_core
                      checkEmpty n p h recorded beforeCaller joined winner queries
                      folded foldCaller foldQueries foldOuter erased.symm
                    have foldBounds := rawFold_observed_counter_mass
                      checkEmpty n p h recorded beforeCaller joined winner queries
                      (.ok (some [.ok ((), folded)])) foldCaller foldQueries foldOuter erased.symm
                    cases foldCache with
                    | none =>
                      dsimp only at observed
                      rcases incomingObserved : SourcePruningEnumerationSharedIncomingNode.run
                          checkEmpty r n p h foldCaller folded winner incoming incomingScs foldQueries with
                        ⟨incomingOutcome, reachedCaller, savedQueries, read⟩
                      cases incomingOutcome with
                      | error fault => simp only [incomingObserved] at observed; cases observed
                      | ok possible =>
                        cases possible <;> simp only [incomingObserved] at observed <;> cases observed
                    | some recovered =>
                      dsimp only at observed
                      rcases incomingObserved : incomingCacheAdapter
                          checkEmpty r n p h k foldCaller (EnumerationExpandableIndex.frame folded recovered)
                          winner incoming incomingScs foldQueries with
                        ⟨⟨incomingOutcome, reachedCaller, savedQueries, read⟩, incomingCache⟩
                      cases incomingOutcome with
                      | error fault => simp only [incomingObserved] at observed; cases observed
                      | ok possible =>
                        cases possible with
                        | none => simp only [incomingObserved] at observed; cases observed
                        | some raw =>
                          simp only [incomingObserved] at observed
                          have incomingBounds := incoming_observed_cache_bounds
                            checkEmpty r n p h k foldCaller (EnumerationExpandableIndex.frame folded recovered)
                            winner incoming incomingScs foldQueries after
                            (by rw [incomingObserved]; exact observed)
                          dsimp only [EnumerationExpandableIndex.frame] at incomingBounds
                          rw [foldedSame, foldBounds.1, foldBounds.2, prefixBounds.1, prefixBounds.2] at incomingBounds
                          exact ⟨incomingBounds.1, Nat.le_of_eq incomingBounds.2⟩

end MicroCFTA.SourcePruningEnumerationSharedCachedTerminal
