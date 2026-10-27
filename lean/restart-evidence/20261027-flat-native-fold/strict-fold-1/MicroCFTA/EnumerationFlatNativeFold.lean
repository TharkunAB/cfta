import MicroCFTA.EnumerationFlatNativeDispatch
import MicroCFTA.SourcePruningEnumerationFold

/-!
# Ordered native assimilation with direct-parent forests

Each actual reached caller and query state enters the next source. Rejection
keeps those effects and returns the enumeration state of the current prefix.
-/
namespace MicroCFTA.EnumerationFlatNativeFold
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {EnumGuard : Type} {width : Nat}

/-- Run the recorded source slots in order and retain each reached state. -/
noncomputable def run
    [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (beforeCaller : Caller width) (before : EnumerationFlatState.State Symbol EnumGuard)
    (target : Nat) (queries : Queries) :
    (Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourceCurrentAllocatedConjunctionWorker.Outcome width)
      (Option (List (Except EnumerationState.Error (Unit × EnumerationFlatState.State Symbol EnumGuard))))) ×
      Caller width × Queries × EnumerationFlatState.State Symbol EnumGuard :=
  match sources with
  | [] => (.ok (some [.ok ((), before)]), beforeCaller, queries, before)
  | source :: rest =>
    let observation :
      (Except (SourceEqualityNativeDemand.Outcome width Node ⊕
        SourceCurrentAllocatedConjunctionWorker.Outcome width)
        (Option (EnumerationFlatState.Action Symbol EnumGuard Unit))) × Caller width × Queries :=
      EnumerationFlatNativeDispatch.dispatch checkEmpty nativeFuel p h beforeCaller before source target queries
    match observation with
    | (.error fault, reachedCaller, savedQueries) => (.error fault, reachedCaller, savedQueries, before)
    | (.ok none, reachedCaller, savedQueries) => (.ok none, reachedCaller, savedQueries, before)
    | (.ok (some action), reachedCaller, savedQueries) =>
        let raw : List (Except EnumerationState.Error (Unit × EnumerationFlatState.State Symbol EnumGuard)) := ExceptT.run (action before)
        match raw with
        | [.ok ((), after)] => run checkEmpty nativeFuel p h rest reachedCaller after target savedQueries
        | other => (.ok (some other), reachedCaller, savedQueries, before)

/-- Keep every ordered row, fault, missing action and exact reached outer state. -/
def ResultRelated
    (flat : Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourceCurrentAllocatedConjunctionWorker.Outcome width)
      (Option (List (Except EnumerationState.Error (Unit × EnumerationFlatState.State Symbol EnumGuard)))) ×
      Caller width × Queries × EnumerationFlatState.State Symbol EnumGuard)
    (earlier : Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourceCurrentAllocatedConjunctionWorker.Outcome width)
      (Option (List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol EnumGuard)))) ×
      Caller width × Queries × EnumerationState.State Symbol EnumGuard) : Prop :=
  flat.2.1 = earlier.2.1 ∧ flat.2.2.1 = earlier.2.2.1 ∧
    EnumerationFlatState.Related flat.2.2.2 earlier.2.2.2 ∧
    match flat.1, earlier.1 with
    | .error first, .error second => first = second
    | .ok none, .ok none => True
    | .ok (some first), .ok (some second) =>
        EnumerationResultRelation.Results EnumerationFlatState.Related first second
    | _, _ => False

/-- All bounds retain complete native effects and every ordered loop observation. -/
theorem run_related
    [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)] [DecidableEq Node]
    (related : EnumerationFlatState.Related flat earlier)
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (beforeCaller : Caller width) (target : Nat) (queries : Queries) :
    ResultRelated (run checkEmpty nativeFuel p h sources beforeCaller flat target queries)
      (SourcePruningEnumerationFold.run checkEmpty nativeFuel p h sources beforeCaller earlier target queries) := by
  induction sources generalizing flat earlier beforeCaller queries with
  | nil => exact ⟨rfl, rfl, related, .cons (.ok () related) .nil⟩
  | cons source rest ih =>
    have step := EnumerationFlatNativeDispatch.dispatch_related related checkEmpty nativeFuel p h
      beforeCaller source target queries
    generalize leftRun : EnumerationFlatNativeDispatch.dispatch checkEmpty nativeFuel p h
      beforeCaller flat source target queries = left at step ⊢
    generalize rightRun : SourcePruningEnumerationDispatch.dispatch checkEmpty nativeFuel p h
      beforeCaller earlier source target queries = right at step ⊢
    obtain ⟨leftOutcome, reachedCaller, savedQueries⟩ := left
    obtain ⟨rightOutcome, oldCaller, oldQueries⟩ := right
    obtain ⟨effects, actions⟩ := step
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj effects
    simp only [run, SourcePruningEnumerationFold.run, leftRun, rightRun]
    cases leftOutcome with
    | error first =>
      cases rightOutcome with
      | error second => exact ⟨rfl, rfl, related, actions⟩
      | ok returned => cases actions
    | ok leftReturned =>
      cases rightOutcome with
      | error fault => cases actions
      | ok rightReturned =>
        cases leftReturned with
        | none =>
          cases rightReturned with
          | none => exact ⟨rfl, rfl, related, trivial⟩
          | some action => cases actions
        | some first =>
          cases rightReturned with
          | none => cases actions
          | some second =>
            have rows := actions flat earlier related
            change EnumerationResultRelation.Results EnumerationFlatState.Related
              (ExceptT.run (first flat)) (ExceptT.run (second earlier)) at rows
            generalize leftRows : ExceptT.run (first flat) = left at rows ⊢
            generalize rightRows : ExceptT.run (second earlier) = right at rows ⊢
            cases rows with
            | nil => exact ⟨rfl, rfl, related, .nil⟩
            | cons head tail =>
              cases head with
              | error fault => exact ⟨rfl, rfl, related, .cons (.error fault) tail⟩
              | ok value states =>
                cases value
                cases tail with
                | nil => exact ih states reachedCaller savedQueries
                | cons next remaining => exact ⟨rfl, rfl, related, .cons (.ok () states) (.cons next remaining)⟩

end MicroCFTA.EnumerationFlatNativeFold
