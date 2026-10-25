import MicroCFTA.SourcePruningEnumerationCachedAdapter
import MicroCFTA.SourcePruningEnumerationFoldInvariants

namespace MicroCFTA.SourcePruningEnumerationCachedFold
open EnumerationState
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {width : Nat}

/-- Retain the full original fold observation with a separate optional cache. -/
noncomputable def run
    [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (beforeCaller : Caller width) (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (target : Nat) (queries : Queries) :
    ((Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourceCurrentAllocatedConjunctionWorker.Outcome width)
      (Option (List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol Constraint))))) ×
      Caller width × Queries × EnumerationState.State Symbol Constraint) ×
      Option (EnumerationExpandableIndex.Cached Symbol Constraint) :=
  match sources with
  | [] => ((.ok (some [.ok ((), before.core)]), beforeCaller, queries, before.core), some before)
  | source :: rest =>
      match SourcePruningEnumerationCachedAdapter.run checkEmpty nativeFuel p h
          beforeCaller before source target queries with
      | (.error fault, reachedCaller, savedQueries, _) =>
          ((.error fault, reachedCaller, savedQueries, before.core), none)
      | (.ok none, reachedCaller, savedQueries, _) =>
          ((.ok none, reachedCaller, savedQueries, before.core), none)
      | (.ok (some raw), reachedCaller, savedQueries, cache) =>
          match raw with
          | [.ok ((), core)] =>
              match cache with
              | none =>
                  (SourcePruningEnumerationFold.run checkEmpty nativeFuel p h rest
                    reachedCaller core target savedQueries, none)
              | some recovered =>
                  run checkEmpty nativeFuel p h rest reachedCaller
                    (EnumerationExpandableIndex.frame core recovered) target savedQueries
          | other => ((.ok (some other), reachedCaller, savedQueries, before.core), cache)

/-- Erasing cache data preserves every bounded original fold observation. -/
theorem erase
    [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (beforeCaller : Caller width) (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (target : Nat) (queries : Queries) :
    (run checkEmpty nativeFuel p h sources beforeCaller before target queries).1 =
      SourcePruningEnumerationFold.run checkEmpty nativeFuel p h sources
        beforeCaller before.core target queries := by
  induction sources generalizing beforeCaller before queries with
  | nil => rfl
  | cons source rest ih =>
      cases dispatchResult : SourcePruningEnumerationDispatch.dispatch checkEmpty nativeFuel p h
          beforeCaller before.core source target queries with
      | mk outcome saved =>
          rcases saved with ⟨reachedCaller, savedQueries⟩
          cases outcome with
          | error fault =>
              simp only [run, SourcePruningEnumerationCachedAdapter.run, dispatchResult,
                SourcePruningEnumerationFold.run]
          | ok returned =>
              cases returned with
              | none =>
                  simp only [run, SourcePruningEnumerationCachedAdapter.run, dispatchResult,
                    SourcePruningEnumerationFold.run]
              | some action =>
                  cases rawResult : ExceptT.run (action before.core) with
                  | nil =>
                      simp only [run, SourcePruningEnumerationCachedAdapter.run, dispatchResult,
                        rawResult, SourcePruningEnumerationFold.run]
                  | cons first tail =>
                      cases first with
                      | error _rowError =>
                          simp only [run, SourcePruningEnumerationCachedAdapter.run, dispatchResult,
                            rawResult, SourcePruningEnumerationFold.run]
                      | ok value =>
                          rcases value with ⟨valueUnit, core⟩
                          cases valueUnit
                          cases tail with
                          | nil =>
                              cases receipt : SourcePruningEnumerationCachedAdapter.adapt
                                  reachedCaller.checked.native.machine.heap before source target [.ok ((), core)] with
                              | none =>
                                  simp only [run, SourcePruningEnumerationCachedAdapter.run, dispatchResult,
                                    rawResult, receipt, SourcePruningEnumerationFold.run]
                              | some recovered =>
                                  simp only [run, SourcePruningEnumerationCachedAdapter.run, dispatchResult,
                                    rawResult, receipt, SourcePruningEnumerationFold.run]
                                  exact ih reachedCaller (EnumerationExpandableIndex.frame core recovered) savedQueries
                          | cons _second _remaining =>
                              simp only [run, SourcePruningEnumerationCachedAdapter.run, dispatchResult,
                                rawResult, SourcePruningEnumerationFold.run]

/-- The actual returned prefix retains storage and canonical waiting counts. -/
theorem preserves
    [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (beforeCaller : Caller width) (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (target : Nat) (queries : Queries) (roots : Nat → Nat)
    (storage : EnumerationCorrectness.StorageValid before.core)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting) :
    EnumerationCorrectness.StorageValid
      (run checkEmpty nativeFuel p h sources beforeCaller before target queries).1.2.2.2 ∧
      EnumerationCanonicalWaiting.Correct roots
        (run checkEmpty nativeFuel p h sources beforeCaller before target queries).1.2.2.2.values
        before.waiting := by
  exact SourcePruningEnumerationFoldInvariants.run_preserves checkEmpty nativeFuel p h sources
    beforeCaller before.core target queries
    (run checkEmpty nativeFuel p h sources beforeCaller before target queries).1.1
    (run checkEmpty nativeFuel p h sources beforeCaller before target queries).1.2.1
    (run checkEmpty nativeFuel p h sources beforeCaller before target queries).1.2.2.1
    (run checkEmpty nativeFuel p h sources beforeCaller before target queries).1.2.2.2
    roots before.waiting storage counts
    (erase checkEmpty nativeFuel p h sources beforeCaller before target queries).symm

end MicroCFTA.SourcePruningEnumerationCachedFold
