import MicroCFTA.EnumerationFlatNativeDispatch
import MicroCFTA.EnumerationFlatNativeIndex
import MicroCFTA.SourcePruningEnumerationCachedAdapter

/-!
# Native cache recovery across the union-find representation change

Raw action rows and optional cache recovery remain separate. Both workers use
one actual dispatch and classify its rows at that same reached native heap.
-/
namespace MicroCFTA.EnumerationFlatNativeCachedAdapter
open EnumerationFlatCached
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
open InternedConstructorTemplates (EdgeKey)
variable {width : Nat}

/-- Reconstruct the cache from an actual raw row with explicit partiality. -/
def adapt
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (before : EnumerationFlatCached.Cached Symbol Constraint) (source target : Nat)
    (raw : List (Except EnumerationState.Error (Unit × EnumerationFlatState.State Symbol Constraint))) :
    Option (EnumerationFlatCached.Cached Symbol Constraint) :=
  match raw with
  | [] => some before
  | [.ok ((), core)] =>
      if source = target then some before else
        match before.core.values[source]? with
        | some .eliminated => some before
        | _ =>
            (core.values[target]?).bind fun value =>
              (SourcePruningEnumerationNativeIndex.candidate heap value).map fun flag =>
                ⟨core, (fun slot => if slot = source then false else
                  if slot = target then flag else before.expandable slot), before.waiting⟩
  | _ => none

/-- Run dispatch and its captured action once, with a separate cache receipt. -/
noncomputable def run
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat)
    (beforeCaller : Caller width) (before : EnumerationFlatCached.Cached Symbol Constraint)
    (source target : Nat) (queries : Queries) :
    (Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourceCurrentAllocatedConjunctionWorker.Outcome width)
      (Option (List (Except EnumerationState.Error (Unit × EnumerationFlatState.State Symbol Constraint))))) ×
      Caller width × Queries × Option (EnumerationFlatCached.Cached Symbol Constraint) :=
  match EnumerationFlatNativeDispatch.dispatch checkEmpty nativeFuel p h
      beforeCaller before.core source target queries with
  | (.error fault, reachedCaller, savedQueries) =>
      (.error fault, reachedCaller, savedQueries, none)
  | (.ok none, reachedCaller, savedQueries) =>
      (.ok none, reachedCaller, savedQueries, none)
  | (.ok (some action), reachedCaller, savedQueries) =>
      let raw : List (Except EnumerationState.Error (Unit × EnumerationFlatState.State Symbol Constraint)) :=
        ExceptT.run (action before.core)
      (.ok (some raw), reachedCaller, savedQueries,
        adapt reachedCaller.checked.native.machine.heap before source target raw)

/-- Related raw observations recover related caches or both fail classification. -/
theorem adapt_related (related : Related flat earlier)
    (heap : InternedConstructorTemplates.State Symbol Constraint) (source target : Nat)
    (rows : EnumerationResultRelation.Results EnumerationFlatState.Related flatRows oldRows) :
    EnumerationFlatNativeIndex.WritesRelated (adapt heap flat source target flatRows)
      (SourcePruningEnumerationCachedAdapter.adapt heap earlier source target oldRows) := by
  cases rows with
  | nil => exact related
  | cons head tail =>
    cases tail with
    | cons next remaining => cases head <;> trivial
    | nil =>
      cases head with
      | error fault => trivial
      | @ok left right value states =>
        cases value
        simp only [adapt, SourcePruningEnumerationCachedAdapter.adapt]
        by_cases same : source = target
        · simp only [same, ↓reduceIte]
          exact related
        · simp only [same, ↓reduceIte]
          rw [related.core.values, states.values]
          have rebuilt : EnumerationFlatNativeIndex.WritesRelated
              (((right.values[target]?).bind fun value =>
                (SourcePruningEnumerationNativeIndex.candidate heap value).map fun flag =>
                  (⟨left, (fun slot => if slot = source then false else
                    if slot = target then flag else flat.expandable slot), flat.waiting⟩ : Cached Symbol Constraint)))
              (((right.values[target]?).bind fun value =>
                (SourcePruningEnumerationNativeIndex.candidate heap value).map fun flag =>
                  (⟨right, (fun slot => if slot = source then false else
                    if slot = target then flag else earlier.expandable slot), earlier.waiting⟩ :
                    EnumerationExpandableIndex.Cached Symbol Constraint))) := by
            cases targetRead : right.values[target]? with
            | none => trivial
            | some value =>
              cases classified : SourcePruningEnumerationNativeIndex.candidate heap value with
              | none => trivial
              | some flag =>
                exact ⟨states, by rw [related.expandable], related.waiting⟩
          cases sourceRead : earlier.core.values[source]? with
          | none => exact rebuilt
          | some value =>
            cases value with
            | eliminated => exact related
            | enumerated fragment => exact rebuilt
            | unenumerated node scs => exact rebuilt

/-- Retain every raw row and native effect independently of optional cache recovery. -/
def ResultRelated
    (flat : Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourceCurrentAllocatedConjunctionWorker.Outcome width)
      (Option (List (Except EnumerationState.Error (Unit × EnumerationFlatState.State Symbol Constraint)))) ×
      Caller width × Queries × Option (Cached Symbol Constraint))
    (earlier : Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourceCurrentAllocatedConjunctionWorker.Outcome width)
      (Option (List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol Constraint)))) ×
      Caller width × Queries × Option (EnumerationExpandableIndex.Cached Symbol Constraint)) : Prop :=
  flat.2.1 = earlier.2.1 ∧ flat.2.2.1 = earlier.2.2.1 ∧
    EnumerationFlatNativeIndex.WritesRelated flat.2.2.2 earlier.2.2.2 ∧
    match flat.1, earlier.1 with
    | .error first, .error second => first = second
    | .ok none, .ok none => True
    | .ok (some first), .ok (some second) =>
        EnumerationResultRelation.Results EnumerationFlatState.Related first second
    | _, _ => False

/-- Every bounded adapter preserves actual native effects, raw rows and optional caches. -/
theorem run_related
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (related : Related flat earlier) (checkEmpty : Bool) (nativeFuel p h : Nat)
    (beforeCaller : Caller width) (source target : Nat) (queries : Queries) :
    ResultRelated (run checkEmpty nativeFuel p h beforeCaller flat source target queries)
      (SourcePruningEnumerationCachedAdapter.run checkEmpty nativeFuel p h
        beforeCaller earlier source target queries) := by
  have step := EnumerationFlatNativeDispatch.dispatch_related related.core checkEmpty nativeFuel p h
    beforeCaller source target queries
  generalize leftRun : EnumerationFlatNativeDispatch.dispatch checkEmpty nativeFuel p h
    beforeCaller flat.core source target queries = left at step ⊢
  generalize rightRun : SourcePruningEnumerationDispatch.dispatch checkEmpty nativeFuel p h
    beforeCaller earlier.core source target queries = right at step ⊢
  obtain ⟨leftOutcome, reachedCaller, savedQueries⟩ := left
  obtain ⟨rightOutcome, oldCaller, oldQueries⟩ := right
  obtain ⟨effects, actions⟩ := step
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj effects
  dsimp only at actions
  simp only [run, SourcePruningEnumerationCachedAdapter.run, leftRun, rightRun]
  cases leftOutcome with
  | error first =>
    cases rightOutcome with
    | error second => exact ⟨rfl, rfl, trivial, actions⟩
    | ok returned => cases actions
  | ok leftReturned =>
    cases rightOutcome with
    | error fault => cases leftReturned <;> cases actions
    | ok rightReturned =>
      cases leftReturned with
      | none =>
        cases rightReturned with
        | none => exact ⟨rfl, rfl, trivial, trivial⟩
        | some action => cases actions
      | some first =>
        cases rightReturned with
        | none => cases actions
        | some second =>
          have rows := actions flat.core earlier.core related.core
          exact ⟨rfl, rfl, adapt_related related _ source target rows, rows⟩

end MicroCFTA.EnumerationFlatNativeCachedAdapter
