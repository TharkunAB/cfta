import MicroCFTA.SourceCurrentAllocatedTargetGraph
import MicroCFTA.SourceCurrentAllocatedMergeWorker
import MicroCFTA.SourceEqualityProjectionWorker

/-!
# Bounded current targets with checked native state

Projection precedes the allocated memo-aware merge. Each fold evaluates
its head operand, its tail, and the checked intersection in that order.
Five independent bounds control projection, reads, merge, selection, and
native execution. Incomplete observations retain their full returned state
and do not execute a continuation. The serial graph does not establish
the host demand schedule or runtime memo publication.
-/
namespace MicroCFTA.SourceCurrentAllocatedTargetWorker
open InternedConstructorTemplates
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

abbrev Checked := SourceEqualityNativeDemand.State
abbrev Memo := SourceCurrentMemoMergeGraph.Memo Symbol Guard

/-- Each incomplete stage retains its complete underlying observation. -/
inductive Fault (width : Nat) : Type 1 where
  | projection (observation : SourceEqualityRequiredWorker.Result Symbol Guard (Value Symbol Guard))
  | merge (fault : SourceCurrentAllocatedMergeWorker.Fault)
  | native (observation : SourceEqualityNativeDemand.Outcome width (Value Symbol Guard))

/-- Every observation retains the full checked state and completed merge table. -/
inductive Outcome (width : Nat) : Type 1 where
  | done (value : Value Symbol Guard) (state : Checked width) (memo : Memo)
  | failed (fault : Fault width) (state : Checked width) (memo : Memo)

def Outcome.state : Outcome width → Checked width
  | .done _ state _ | .failed _ state _ => state

def Outcome.memo : Outcome width → Memo
  | .done _ _ memo | .failed _ _ memo => memo

/-- Only a completed stage enters its continuation at the literal returned state. -/
def Outcome.bind (first : Outcome width)
    (next : Value Symbol Guard → Checked width → Memo → Outcome width) : Outcome width :=
  match first with
  | .done value state memo => next value state memo
  | .failed fault state memo => .failed fault state memo

/-- Projection advances only the constructor heap at the same equality operations. -/
def projection [DecidableEq (EdgeKey Symbol Guard)] (fuel readFuel : Nat) (path : List Int)
    (values : List (Value Symbol Guard)) (before : Checked width) (memo : Memo) : Outcome width :=
  match SourceEqualityProjectionWorker.forest fuel readFuel path values before.native.machine.heap with
  | .done value heap => .done value (advancePhysical before ⟨heap, before.operations⟩) memo
  | .pending key heap => .failed (.projection (.pending key heap))
      (advancePhysical before ⟨heap, before.operations⟩) memo
  | .unresolved name heap => .failed (.projection (.unresolved name heap))
      (advancePhysical before ⟨heap, before.operations⟩) memo
  | .exhausted limit heap => .failed (.projection (.exhausted limit heap))
      (advancePhysical before ⟨heap, before.operations⟩) memo

/-- Merge retains both the allocated equality operations and the returned merge table. -/
noncomputable def merge [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (mergeFuel selectionFuel : Nat) (value : Value Symbol Guard)
    (before : Checked width) (memo : Memo) : Outcome width :=
  match SourceCurrentAllocatedMergeWorker.call SourceCurrentAllocatedMerge.literalClear
      mergeFuel selectionFuel value (physical before) memo with
  | .done result after saved => .done result (advancePhysical before after) saved
  | .failed fault after saved => .failed (.merge fault) (advancePhysical before after) saved

/-- An operand projects its captured forest before it merges the actual result. -/
noncomputable def operand [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (projectionFuel readFuel mergeFuel selectionFuel : Nat) (path : List Int)
    (values : List (Value Symbol Guard)) (before : Checked width) (memo : Memo) : Outcome width :=
  (projection projectionFuel readFuel path values before memo).bind fun value after saved =>
    merge mergeFuel selectionFuel value after saved

/-- The native request starts at the exact tail return and retains the merge table. -/
noncomputable def leaf [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (left right : Value Symbol Guard) (before : Checked width) (memo : Memo) : Outcome width :=
  match SourceEqualityNativeDemand.execute fuel
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) before with
  | .done result after => .done result after memo
  | other => .failed (.native other) other.state memo

/-- The first seed executes at the base after each preceding head operand. -/
noncomputable def fold [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (projectionFuel readFuel mergeFuel selectionFuel nativeFuel : Nat)
    (values : List (Value Symbol Guard)) (seed : List Int) :
    List (List Int) → Checked width → Memo → Outcome width
  | [], before, memo => operand projectionFuel readFuel mergeFuel selectionFuel seed values before memo
  | path :: paths, before, memo =>
      (operand projectionFuel readFuel mergeFuel selectionFuel path values before memo).bind fun head middle current =>
        (fold projectionFuel readFuel mergeFuel selectionFuel nativeFuel values seed paths middle current).bind
          fun tail later saved => leaf nativeFuel head tail later saved

/-- Empty targets retain the entire initial state and memo without using fuel. -/
noncomputable def target [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (projectionFuel readFuel mergeFuel selectionFuel nativeFuel : Nat)
    (values : List (Value Symbol Guard)) (paths : List (List Int))
    (before : Checked width) (memo : Memo) : Outcome width :=
  match paths with
  | [] => .done .empty before memo
  | seed :: rest => fold projectionFuel readFuel mergeFuel selectionFuel nativeFuel values seed rest before memo

end MicroCFTA.SourceCurrentAllocatedTargetWorker
