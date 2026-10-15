import MicroCFTA.SourceEqualityOnePassGraph
import MicroCFTA.SourceEqualityRecordSelectionProofs

/-!
# Executable guarded native equality pass

The worker retains source prechecks, original physical record selection,
required paths, fresh class targets, the right fold, and final propagation.
Six bounds instrument the existing stages. Actual incomplete stage results
retain their returned caches and do not resume enclosing control.
-/
namespace MicroCFTA.SourceEqualityOnePassWorker
open InternedConstructorTemplates InternedNestedConstruction SourceEqualityClassFoldGraph
open SourceEqualityNativeScoped SourceEqualityPrecheck

/-- Completed source answers and actual incomplete stages retain their complete native scope. -/
inductive Result (width : Nat) (Symbol Guard : Type) : Type 1 where
  | done (answer : Except String (List (Value Symbol Guard))) (state : NativeState width Symbol Guard)
  | selection (observation : Outcome Symbol Guard (Option (List (InternedSourceClassSelection.Query Symbol Guard)))) (state : NativeState width Symbol Guard)
  | required (observation : SourceEqualityRequiredWorker.Result Symbol Guard (List (Value Symbol Guard))) (state : NativeState width Symbol Guard)
  | narrowing (observation : SourceEqualityClassFoldWorker.Result width Symbol Guard (List (Value Symbol Guard)))

/-- A completed native class fold supplies its literal final forest and native state. -/
def finish (observation : SourceEqualityClassFoldWorker.Result width Symbol Guard (List (Value Symbol Guard))) : Result width Symbol Guard :=
  match observation with
  | .done values after => .done (.ok values) after
  | other => .narrowing other

/-- The live branch selects original records, requires their paths, and executes the actual native fold. -/
def live [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (g e p h c n : Nat) (records : List SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard)) (before : NativeState width Symbol Guard) :
    Result width Symbol Guard :=
  match SourceEqualityRecordSelectionWorker.queries unconstrained g values records before.machine.heap with
  | .pending key heap => .selection (.pending key heap) (advanceHeap before heap)
  | .done none heap => .selection (.done none heap) (advanceHeap before heap)
  | .done (some queries) middle =>
      match SourceEqualityRequiredExecution.requireAll p h (SourceEqualitySelectedRequired.paths (InternedSourceClassSelection.selected queries)) values middle with
      | .done required heap => finish (SourceEqualityClassFoldWorker.pass emptyGuard conjoin clear top e p h c n
          (SourceEqualitySelectedRecords.keep records queries) required (advanceHeap before heap))
      | .pending key heap => .required (.pending key heap) (advanceHeap before heap)
      | .unresolved name heap => .required (.unresolved name heap) (advanceHeap before heap)
      | .exhausted limit heap => .required (.exhausted limit heap) (advanceHeap before heap)

/-- Immediate source branches bypass all later workers, including final empty propagation. -/
def runChecked [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (g e p h c n : Nat) (checked : Except String Branch) (values : List (Value Symbol Guard)) (before : NativeState width Symbol Guard) : Result width Symbol Guard :=
  match checked with
  | .error message => .done (.error message) before
  | .ok .unchanged => .done (.ok values) before
  | .ok .emptyChildren => .done (.ok (EqualityLeafProjectionRuntimeEmpty.erase values)) before
  | .ok (.classes records) => live unconstrained emptyGuard conjoin clear top g e p h c n records values before

/-- Execute actual source guards and physical ordering before the complete checked native pass. -/
noncomputable def run [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (g e p h c n : Nat) (own inherited : SourceEqualityPrecheck.Constraint) (values : List (Value Symbol Guard)) (before : NativeState width Symbol Guard) : Result width Symbol Guard :=
  runChecked unconstrained emptyGuard conjoin clear top g e p h c n (precheck own inherited) values before

/-- Execute actual bounded parent-array normalization before the complete source pass. -/
noncomputable def runArray [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (work g e p h c n : Nat) (own inherited : SourceEqualityPrecheck.Constraint) (values : List (Value Symbol Guard)) (before : NativeState width Symbol Guard) : Result width Symbol Guard :=
  runChecked unconstrained emptyGuard conjoin clear top g e p h c n (precheckArray work own inherited) values before

end MicroCFTA.SourceEqualityOnePassWorker
