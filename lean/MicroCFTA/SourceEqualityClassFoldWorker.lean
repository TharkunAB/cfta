import MicroCFTA.SourceEqualityClassFoldComplete

/-!
# Executable source class right fold

Every class starts fresh target slots over its captured current forest.
Only the native state passes to the earlier class. Incomplete class work
retains its original captured forest and full shared stage observation.
One final literal empty propagation follows the complete class fold.
-/
namespace MicroCFTA.SourceEqualityClassFoldWorker
open InternedConstructorTemplates SourceEqualitySharedTargetState SourceEqualityClassFoldGraph

/-- Class-local failures retain their captured forest and literal shared worker observation. -/
inductive Result (width : Nat) (Symbol Guard A : Type) : Type 1 where
  | done (value : A) (state : NativeState width Symbol Guard)
  | incomplete (record : SourceEqualityClassOrder.Record) (captured : List (Value Symbol Guard))
      (observation : SourceEqualitySharedTargetWorker.Result width Symbol Guard (List (Value Symbol Guard)))

/-- Only a completed tail enters the earlier class with its returned forest and native state. -/
def Result.bind (result : Result width Symbol Guard A) (next : A → NativeState width Symbol Guard → Result width Symbol Guard B) : Result width Symbol Guard B :=
  match result with
  | .done value state => next value state
  | .incomplete record captured observation => .incomplete record captured observation

/-- Execute one actual class over its captured forest and initially unforced target slots. -/
def classEdit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (e p h c n : Nat) (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard)) (before : NativeState width Symbol Guard) :
    Result width Symbol Guard (List (Value Symbol Guard)) :=
  match SourceEqualitySharedEditWorker.editAll emptyGuard conjoin clear top record values e p h c n
      (SourceEqualityClassEdits.edits record.paths id) values (initial before) with
  | .done values after => .done values after.native
  | other => .incomplete record values other

/-- Execute the actual finite class-list right fold without resetting native tables between classes. -/
def fold [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (e p h c n : Nat) : List SourceEqualityClassOrder.Record → List (Value Symbol Guard) → NativeState width Symbol Guard →
      Result width Symbol Guard (List (Value Symbol Guard))
  | [], values, before => .done values before
  | record :: records, values, before => (fold emptyGuard conjoin clear top e p h c n records values before).bind fun current next =>
      classEdit emptyGuard conjoin clear top e p h c n record current next

/-- Propagate literal empty children once after the entire class fold. -/
def pass [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (e p h c n : Nat) (records : List SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard)) (before : NativeState width Symbol Guard) :
    Result width Symbol Guard (List (Value Symbol Guard)) :=
  (fold emptyGuard conjoin clear top e p h c n records values before).bind fun results after =>
    .done (EqualityLeafProjectionRuntimeEmpty.propagate results) after

end MicroCFTA.SourceEqualityClassFoldWorker
