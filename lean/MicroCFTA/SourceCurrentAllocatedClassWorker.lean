import MicroCFTA.SourceCurrentAllocatedSharedEditWorker
import MicroCFTA.SourceCurrentAllocatedClassPass

/-!
# Literal checked class editing and right folds

A class captures its actual input forest and clears only its local slots.
The right fold executes the tail before its head class. Complete checked
state and the merge memo pass through every return. Failed edits retain
their full shared state, including the class-local slots. Final empty
propagation changes no cache. Host forcing remains a separate boundary.
-/
namespace MicroCFTA.SourceCurrentAllocatedClassWorker
open InternedConstructorTemplates
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Record" => SourceEqualityClassOrder.Record

/-- A failed class retains its complete reached state and exact edit diagnostic. -/
inductive Outcome (width : Nat) : Type 1 where
  | done (values : List (Value Symbol Guard)) (checked : Checked width) (memo : Memo)
  | failed (fault : SourceCurrentAllocatedSharedEditWorker.Fault width) (state : Shared width)

def Outcome.state : Outcome width → Checked width
  | .done _ checked _ => checked
  | .failed _ state => state.checked

def Outcome.memo : Outcome width → Memo
  | .done _ _ memo => memo
  | .failed _ state => state.memo

/-- Only completed classes execute their continuation at the actual returned state. -/
def Outcome.bind (first : Outcome width)
    (next : List (Value Symbol Guard) → Checked width → Memo → Outcome width) : Outcome width :=
  match first with
  | .done values checked memo => next values checked memo
  | .failed fault state => .failed fault state

/-- A class starts with empty local slots over the supplied checked state and warm memo. -/
noncomputable def runClass [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (editFuel projectionFuel readFuel mergeFuel selectionFuel nativeFuel : Nat)
    (record : Record) (values : List (Value Symbol Guard)) (before : Checked width) (memo : Memo) : Outcome width :=
  match SourceCurrentAllocatedSharedEditWorker.editList
      (SourceCurrentAllocatedSharedEditWorker.edit record values editFuel projectionFuel readFuel mergeFuel selectionFuel nativeFuel)
      (SourceCurrentAllocatedClassEditPlan.compiled record) values
      (SourceCurrentAllocatedSharedTargetState.initial before memo) with
  | .done results shared => .done results shared.checked shared.memo
  | .failed fault shared => .failed fault shared

/-- The tail executes before the head captures its literal returned forest. -/
noncomputable def fold [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (editFuel projectionFuel readFuel mergeFuel selectionFuel nativeFuel : Nat) :
    List Record → List (Value Symbol Guard) → Checked width → Memo → Outcome width
  | [], values, before, memo => .done values before memo
  | record :: records, values, before, memo =>
      (fold editFuel projectionFuel readFuel mergeFuel selectionFuel nativeFuel records values before memo).bind
        fun middle checked current =>
          runClass editFuel projectionFuel readFuel mergeFuel selectionFuel nativeFuel record middle checked current

/-- Empty propagation runs only after a completed full class fold. -/
noncomputable def pass [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (editFuel projectionFuel readFuel mergeFuel selectionFuel nativeFuel : Nat)
    (records : List Record) (values : List (Value Symbol Guard)) (before : Checked width) (memo : Memo) : Outcome width :=
  (fold editFuel projectionFuel readFuel mergeFuel selectionFuel nativeFuel records values before memo).bind
    fun results checked saved => .done (EqualityLeafProjectionRuntimeEmpty.propagate results) checked saved

/-- Failed class edits retain their exact local slots instead of resetting the shared state. -/
theorem runClass_failed [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (e p h m s n : Nat) (record : Record) (values : List (Value Symbol Guard)) (before : Checked width) (memo : Memo)
    (fault : SourceCurrentAllocatedSharedEditWorker.Fault width) (shared : Shared width)
    (failed : SourceCurrentAllocatedSharedEditWorker.editList
      (SourceCurrentAllocatedSharedEditWorker.edit record values e p h m s n)
      (SourceCurrentAllocatedClassEditPlan.compiled record) values
      (SourceCurrentAllocatedSharedTargetState.initial before memo) = .failed fault shared) :
    runClass e p h m s n record values before memo = .failed fault shared := by
  simp only [runClass, failed]

/-- An empty fold retains the supplied forest and every cache without using a bound. -/
theorem fold_nil [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (e p h m s n : Nat) (values : List (Value Symbol Guard)) (before : Checked width) (memo : Memo) :
    fold e p h m s n [] values before memo = .done values before memo := rfl

/-- Even an empty class list runs the source propagation without changing state. -/
theorem pass_nil [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (e p h m s n : Nat) (values : List (Value Symbol Guard)) (before : Checked width) (memo : Memo) :
    pass e p h m s n [] values before memo =
      .done (EqualityLeafProjectionRuntimeEmpty.propagate values) before memo := rfl

end MicroCFTA.SourceCurrentAllocatedClassWorker
