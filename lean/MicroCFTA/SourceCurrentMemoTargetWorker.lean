import MicroCFTA.SourceCurrentMemoTargetOperand
import MicroCFTA.SourceCurrentMemoMergeWorker
import MicroCFTA.SourceEqualityProjectionWorker

/-!
# Executable targets with memo-aware operand demands

Projection precedes the actual memo-aware merge. Each source fold demands
its left operand before its tail and native intersection. Every stage
retains the returned native state and completed merge table. The five proof
bounds remain separate. Incomplete observations do not enter continuations.
-/
namespace MicroCFTA.SourceCurrentMemoTargetWorker
open InternedConstructorTemplates SourceEqualityNativeScoped
open SourceCurrentMemoMergeGraph (Memo)

abbrev NativeState (width : Nat) (Symbol Guard : Type) := SourceRecursiveIntersectionThunks.State width Symbol Guard

/-- Incomplete stages retain the full projection or native observation. -/
inductive Fault (width : Nat) (Symbol Guard : Type) : Type 1 where
  | projection (observation : SourceEqualityRequiredWorker.Result Symbol Guard (Value Symbol Guard))
  | merge (fault : MergedSourceComparison.Fault)
  | native (observation : SourceRecursiveIntersectionNative.Outcome width Symbol Guard (Value Symbol Guard))

/-- Every target observation retains the same full native scope and completed result table. -/
inductive Outcome (width : Nat) (Symbol Guard : Type) : Type 1 where
  | done (value : Value Symbol Guard) (state : NativeState width Symbol Guard) (memo : Memo Symbol Guard)
  | failed (fault : Fault width Symbol Guard) (state : NativeState width Symbol Guard) (memo : Memo Symbol Guard)

def Outcome.state : Outcome width Symbol Guard → NativeState width Symbol Guard
  | .done _ state _ | .failed _ state _ => state

def Outcome.memo : Outcome width Symbol Guard → Memo Symbol Guard
  | .done _ _ memo | .failed _ _ memo => memo

/-- Only a completed stage executes its continuation with its actual returned tables. -/
def Outcome.bind (first : Outcome width Symbol Guard)
    (next : Value Symbol Guard → NativeState width Symbol Guard → Memo Symbol Guard → Outcome width Symbol Guard) :
    Outcome width Symbol Guard :=
  match first with
  | .done value state memo => next value state memo
  | .failed fault state memo => .failed fault state memo

/-- Project the captured forest and advance only the actual constructor heap. -/
def projection [DecidableEq (EdgeKey Symbol Guard)] (fuel readFuel : Nat) (path : List Int)
    (values : List (Value Symbol Guard)) (before : NativeState width Symbol Guard) (memo : Memo Symbol Guard) :
    Outcome width Symbol Guard :=
  match SourceEqualityProjectionWorker.forest fuel readFuel path values before.machine.heap with
  | .done value heap => .done value (advanceHeap before heap) memo
  | .pending key heap => .failed (.projection (.pending key heap)) (advanceHeap before heap) memo
  | .unresolved name heap => .failed (.projection (.unresolved name heap)) (advanceHeap before heap) memo
  | .exhausted limit heap => .failed (.projection (.exhausted limit heap)) (advanceHeap before heap) memo

/-- Merge the projected value through the actual completed result table. -/
def merge [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (top : Guard)
    (mergeFuel selectionFuel : Nat) (value : Value Symbol Guard)
    (before : NativeState width Symbol Guard) (memo : Memo Symbol Guard) : Outcome width Symbol Guard :=
  match SourceCurrentMemoMergeWorker.call clear top mergeFuel selectionFuel value before.machine.heap memo with
  | .done result heap saved => .done result (advanceHeap before heap) saved
  | .failed fault heap saved => .failed (.merge fault) (advanceHeap before heap) saved

/-- One actual operand demands projection before the memo-aware merge. -/
def operand [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (top : Guard)
    (projectionFuel readFuel mergeFuel selectionFuel : Nat) (path : List Int) (values : List (Value Symbol Guard))
    (before : NativeState width Symbol Guard) (memo : Memo Symbol Guard) : Outcome width Symbol Guard :=
  (projection projectionFuel readFuel path values before memo).bind fun value after saved =>
    merge clear top mergeFuel selectionFuel value after saved

/-- The native request uses the exact returned scope and retains the completed merge table. -/
def leaf [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (value tail : Value Symbol Guard) (before : NativeState width Symbol Guard) (memo : Memo Symbol Guard) :
    Outcome width Symbol Guard :=
  match SourceRecursiveIntersectionNative.execute emptyGuard conjoin fuel
      (.node ⟨IntersectionEmptyDomain.emptyDomain, value, tail⟩ .pure) before with
  | .done result after => .done result after memo
  | other => .failed (.native other) other.state memo

/-- The deferred first seed runs at the base after every preceding operand demand. -/
def fold [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (clear : Guard → Bool) (top : Guard) (projectionFuel readFuel mergeFuel selectionFuel nativeFuel : Nat)
    (values : List (Value Symbol Guard)) (seed : List Int) :
    List (List Int) → NativeState width Symbol Guard → Memo Symbol Guard → Outcome width Symbol Guard
  | [], before, memo => operand clear top projectionFuel readFuel mergeFuel selectionFuel seed values before memo
  | path :: paths, before, memo =>
      (operand clear top projectionFuel readFuel mergeFuel selectionFuel path values before memo).bind fun value middle current =>
        (fold emptyGuard conjoin clear top projectionFuel readFuel mergeFuel selectionFuel nativeFuel values seed paths middle current).bind fun tail later saved =>
          leaf emptyGuard conjoin nativeFuel value tail later saved

/-- Empty targets return EmptyNode; other targets use the source first-seeded fold. -/
def target [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (clear : Guard → Bool) (top : Guard) (projectionFuel readFuel mergeFuel selectionFuel nativeFuel : Nat)
    (values : List (Value Symbol Guard)) (paths : List (List Int))
    (before : NativeState width Symbol Guard) (memo : Memo Symbol Guard) : Outcome width Symbol Guard :=
  match paths with
  | [] => .done .empty before memo
  | seed :: rest => fold emptyGuard conjoin clear top projectionFuel readFuel mergeFuel selectionFuel nativeFuel values seed rest before memo

end MicroCFTA.SourceCurrentMemoTargetWorker
