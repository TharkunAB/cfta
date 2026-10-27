import MicroCFTA.EnumerationFlatNativeCachedAdapter
import MicroCFTA.EnumerationFlatNativeFold
import MicroCFTA.SourcePruningEnumerationCachedFold

/-!
# Cached native assimilation with the complete uncached suffix

A recovered cache retains both indexes. A singleton without a cache executes
its full remaining raw loop. Reached native effects remain in both branches.
-/
namespace MicroCFTA.EnumerationFlatNativeCachedFold
open EnumerationFlatCached
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
    (beforeCaller : Caller width) (before : EnumerationFlatCached.Cached Symbol Constraint)
    (target : Nat) (queries : Queries) :
    ((Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourceCurrentAllocatedConjunctionWorker.Outcome width)
      (Option (List (Except EnumerationState.Error (Unit × EnumerationFlatState.State Symbol Constraint))))) ×
      Caller width × Queries × EnumerationFlatState.State Symbol Constraint) ×
      Option (EnumerationFlatCached.Cached Symbol Constraint) :=
  match sources with
  | [] => ((.ok (some [.ok ((), before.core)]), beforeCaller, queries, before.core), some before)
  | source :: rest =>
      match EnumerationFlatNativeCachedAdapter.run checkEmpty nativeFuel p h
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
                  (EnumerationFlatNativeFold.run checkEmpty nativeFuel p h rest
                    reachedCaller core target savedQueries, none)
              | some recovered =>
                  run checkEmpty nativeFuel p h rest reachedCaller
                    (EnumerationFlatCached.frame core recovered) target savedQueries
          | other => ((.ok (some other), reachedCaller, savedQueries, before.core), cache)

/-- Related observations retain the complete raw outcome and optional cache separately. -/
def ResultRelated
    (flat : ((Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourceCurrentAllocatedConjunctionWorker.Outcome width)
      (Option (List (Except EnumerationState.Error (Unit × EnumerationFlatState.State Symbol Constraint))))) ×
      Caller width × Queries × EnumerationFlatState.State Symbol Constraint) × Option (Cached Symbol Constraint))
    (earlier : ((Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourceCurrentAllocatedConjunctionWorker.Outcome width)
      (Option (List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol Constraint))))) ×
      Caller width × Queries × EnumerationState.State Symbol Constraint) ×
      Option (EnumerationExpandableIndex.Cached Symbol Constraint)) : Prop :=
  EnumerationFlatNativeFold.ResultRelated flat.1 earlier.1 ∧
    EnumerationFlatNativeIndex.WritesRelated flat.2 earlier.2

/-- Every bounded cached loop retains raw effects, cache recovery and the full uncached fallback. -/
theorem run_related
    [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)] [DecidableEq Node]
    (related : Related flat earlier) (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (beforeCaller : Caller width) (target : Nat) (queries : Queries) :
    ResultRelated (run checkEmpty nativeFuel p h sources beforeCaller flat target queries)
      (SourcePruningEnumerationCachedFold.run checkEmpty nativeFuel p h sources
        beforeCaller earlier target queries) := by
  induction sources generalizing flat earlier beforeCaller queries with
  | nil => exact ⟨⟨rfl, rfl, related.core, .cons (.ok () related.core) .nil⟩, related⟩
  | cons source rest ih =>
    have step := EnumerationFlatNativeCachedAdapter.run_related related checkEmpty nativeFuel p h
      beforeCaller source target queries
    generalize leftRun : EnumerationFlatNativeCachedAdapter.run checkEmpty nativeFuel p h
      beforeCaller flat source target queries = left at step ⊢
    generalize rightRun : SourcePruningEnumerationCachedAdapter.run checkEmpty nativeFuel p h
      beforeCaller earlier source target queries = right at step ⊢
    obtain ⟨leftOutcome, reachedCaller, savedQueries, leftCache⟩ := left
    obtain ⟨rightOutcome, oldCaller, oldQueries, rightCache⟩ := right
    obtain ⟨callerSame, queriesSame, caches, rows⟩ := step
    dsimp only at callerSame queriesSame
    subst oldCaller
    subst oldQueries
    dsimp only at rows caches
    simp only [run, SourcePruningEnumerationCachedFold.run, leftRun, rightRun]
    cases leftOutcome with
    | error first =>
      cases rightOutcome with
      | error second => exact ⟨⟨rfl, rfl, related.core, rows⟩, trivial⟩
      | ok returned => cases rows
    | ok leftReturned =>
      cases rightOutcome with
      | error fault => cases leftReturned <;> cases rows
      | ok rightReturned =>
        cases leftReturned with
        | none =>
          cases rightReturned with
          | none => exact ⟨⟨rfl, rfl, related.core, trivial⟩, trivial⟩
          | some raw => cases rows
        | some flatRows =>
          cases rightReturned with
          | none => cases rows
          | some oldRows =>
            dsimp only
            cases rows with
            | nil => exact ⟨⟨rfl, rfl, related.core, .nil⟩, caches⟩
            | cons head tail =>
              cases head with
              | error fault => exact ⟨⟨rfl, rfl, related.core, .cons (.error fault) tail⟩, caches⟩
              | ok value states =>
                cases value
                cases tail with
                | cons next remaining =>
                    exact ⟨⟨rfl, rfl, related.core, .cons (.ok () states) (.cons next remaining)⟩, caches⟩
                | nil =>
                  cases leftCache with
                  | none =>
                    cases rightCache with
                    | none => exact ⟨EnumerationFlatNativeFold.run_related states checkEmpty nativeFuel p h
                        rest reachedCaller target savedQueries, trivial⟩
                    | some oldCache => cases caches
                  | some flatCache =>
                    cases rightCache with
                    | none => cases caches
                    | some oldCache =>
                      exact ih (frame_related caches states) reachedCaller savedQueries

end MicroCFTA.EnumerationFlatNativeCachedFold
