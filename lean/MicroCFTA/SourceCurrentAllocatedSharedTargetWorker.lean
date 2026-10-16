import MicroCFTA.SourceCurrentAllocatedTargetWorker
import MicroCFTA.SourceCurrentAllocatedSharedTargetLeaf

/-!
# Literal shared targets with full checked state

A ready target slot returns the same whole state. A miss executes the
current target worker and stores only a completed result. Leaf intersection
runs at that returned checked state. Every failed prefix retains its exact
observation, checked operations, native tables, merge memo, and target slots.
This serial worker retains the separate host forcing boundary.
-/
namespace MicroCFTA.SourceCurrentAllocatedSharedTargetWorker
open InternedConstructorTemplates SourceCurrentAllocatedSharedTargetState
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Path" => EqualityNormalize.Path

/-- Diagnostics retain the exact failed target stage or checked native observation. -/
inductive Fault (width : Nat) : Type 1 where
  | target (fault : SourceCurrentAllocatedTargetWorker.Fault width)
  | native (observation : SourceEqualityNativeDemand.Outcome width (Value Symbol Guard))

/-- Success and failure retain the full returned shared state. -/
inductive Outcome (width : Nat) : Type 1 where
  | done (value : Value Symbol Guard) (state : State width)
  | failed (fault : Fault width) (state : State width)

def Outcome.state : Outcome width → State width
  | .done _ state | .failed _ state => state

/-- Only a completed prefix enters its continuation. -/
def Outcome.bind (first : Outcome width)
    (next : Value Symbol Guard → State width → Outcome width) : Outcome width :=
  match first with
  | .done value state => next value state
  | .failed fault state => .failed fault state

/-- A miss stores its completed target. A failure retains all earlier slots. -/
noncomputable def force [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (projectionFuel readFuel mergeFuel selectionFuel nativeFuel : Nat)
    (record : Record) (values : List (Value Symbol Guard)) (path : Path)
    (before : State width) : Outcome width :=
  match before.targets path with
  | some value => .done value before
  | none =>
      match SourceCurrentAllocatedTargetWorker.target projectionFuel readFuel mergeFuel selectionFuel nativeFuel
          values (SourceEqualityClassTarget.operandPaths record.paths path) before.checked before.memo with
      | .done value checked saved => .done value (store before path value checked saved)
      | .failed fault checked saved => .failed (.target fault) {before with checked := checked, memo := saved}

/-- A checked intersection retains its exact observation and both shared tables. -/
noncomputable def step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (nativeFuel : Nat) (target input : Value Symbol Guard) (before : State width) : Outcome width :=
  match SourceEqualityNativeDemand.execute nativeFuel
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain target input)) before.checked with
  | .done value checked => .done value (advance before checked)
  | other => .failed (.native other) (advance before other.state)

/-- Target forcing precedes the actual checked leaf request. -/
noncomputable def leaf [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (projectionFuel readFuel mergeFuel selectionFuel nativeFuel : Nat)
    (record : Record) (values : List (Value Symbol Guard)) (path : Path) (input : Value Symbol Guard)
    (before : State width) : Outcome width :=
  (force projectionFuel readFuel mergeFuel selectionFuel nativeFuel record values path before).bind
    fun target middle => step nativeFuel target input middle

/-- A ready hit ignores all execution bounds and retains the complete input state. -/
theorem force_hit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (p h m s n : Nat) (record : Record) (values : List (Value Symbol Guard))
    (path : Path) (before : State width) (value : Value Symbol Guard)
    (present : before.targets path = some value) :
    force p h m s n record values path before = .done value before := by
  simp only [force, present]

/-- A failed target does not install a result or replace an earlier target slot. -/
theorem force_failed [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (p h m s n : Nat) (record : Record) (values : List (Value Symbol Guard))
    (path : Path) (before : State width) (absent : before.targets path = none)
    (fault : SourceCurrentAllocatedTargetWorker.Fault width) (checked : Checked width) (saved : Memo)
    (failed : SourceCurrentAllocatedTargetWorker.target p h m s n values
      (SourceEqualityClassTarget.operandPaths record.paths path) before.checked before.memo = .failed fault checked saved) :
    force p h m s n record values path before =
      .failed (.target fault) {before with checked := checked, memo := saved} := by
  simp only [force, absent, failed]

/-- Every native observation retains its exact checked return and unchanged shared tables. -/
theorem step_state [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (n : Nat) (target input : Value Symbol Guard) (before : State width) :
    (step n target input before).state.checked =
      (SourceEqualityNativeDemand.execute n
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain target input)) before.checked).state ∧
    (step n target input before).state.targets = before.targets ∧
    (step n target input before).state.memo = before.memo := by
  cases actual : SourceEqualityNativeDemand.execute n
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain target input)) before.checked <;>
    simp only [step, actual, Outcome.state, advance, SourceEqualityNativeDemand.Outcome.state, and_self]

end MicroCFTA.SourceCurrentAllocatedSharedTargetWorker
