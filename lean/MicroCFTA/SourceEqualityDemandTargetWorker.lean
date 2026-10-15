import MicroCFTA.SourceEqualityDemandTargetComplete

/-!
# Executable source targets with actual operand demands

Projection, cold head reads, comparison, and native requests have separate
proof bounds. Every stage retains its actual complete state or incomplete
observation. The worker does not resume enclosing control from an observation.
-/
namespace MicroCFTA.SourceEqualityDemandTargetWorker
open InternedConstructorTemplates SourceEqualityNativeScoped

/-- Target workers retain the existing constructor, domain, and both native memo tables. -/
abbrev NativeState (width : Nat) (Symbol Guard : Type) := SourceRecursiveIntersectionThunks.State width Symbol Guard

/-- Stage observations remain distinct from completed target values and retain their full native scope. -/
inductive Result (width : Nat) (Symbol Guard A : Type) : Type 1 where
  | done (value : A) (state : NativeState width Symbol Guard)
  | projection (observation : SourceEqualityRequiredWorker.Result Symbol Guard (Value Symbol Guard)) (state : NativeState width Symbol Guard)
  | merge (fault : MergedSourceComparison.Fault) (state : NativeState width Symbol Guard)
  | native (observation : SourceRecursiveIntersectionNative.Outcome width Symbol Guard (Value Symbol Guard))

/-- Only a completed stage enters the continuation at its actual full native state. -/
def Result.bind (result : Result width Symbol Guard A) (next : A → NativeState width Symbol Guard → Result width Symbol Guard B) : Result width Symbol Guard B :=
  match result with
  | .done value state => next value state
  | .projection observation state => .projection observation state
  | .merge fault state => .merge fault state
  | .native observation => .native observation

/-- Demand actual forest projection and retain its precise failure or exhausted stage. -/
def projection [DecidableEq (EdgeKey Symbol Guard)] (fuel readFuel : Nat) (path : List Int) (values : List (Value Symbol Guard))
    (before : NativeState width Symbol Guard) : Result width Symbol Guard (Value Symbol Guard) :=
  match SourceEqualityProjectionWorker.forest fuel readFuel path values before.machine.heap with
  | .done result heap => .done result (advanceHeap before heap)
  | .pending key heap => .projection (.pending key heap) (advanceHeap before heap)
  | .unresolved name heap => .projection (.unresolved name heap) (advanceHeap before heap)
  | .exhausted limit heap => .projection (.exhausted limit heap) (advanceHeap before heap)

/-- Demand general merging at the projected value's actual cache and derived ordinary height. -/
def merge [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (top : Guard) (fuel : Nat)
    (value : Value Symbol Guard) (before : NativeState width Symbol Guard) : Result width Symbol Guard (Value Symbol Guard) :=
  match SourceMergedWorker.execute clear top fuel value before.machine.heap with
  | .done result heap => .done result (advanceHeap before heap)
  | .failed fault heap => .merge fault (advanceHeap before heap)

/-- One operand performs actual projection before its demanded general merge. -/
def operand [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (top : Guard)
    (fuel readFuel comparisonFuel : Nat) (path : List Int) (values : List (Value Symbol Guard)) (before : NativeState width Symbol Guard) :
    Result width Symbol Guard (Value Symbol Guard) :=
  (projection fuel readFuel path values before).bind fun value after => merge clear top comparisonFuel value after

/-- A native request runs at the warm state returned by the recursive demanded fold. -/
def leaf [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (value tail : Value Symbol Guard) (before : NativeState width Symbol Guard) : Result width Symbol Guard (Value Symbol Guard) :=
  match SourceRecursiveIntersectionNative.execute emptyGuard conjoin fuel (.node ⟨IntersectionEmptyDomain.emptyDomain, value, tail⟩ .pure) before with
  | .done result after => .done result after
  | other => .native other

/-- Demand each left operand before its tail; demand the original first seed only at the fold base. -/
def fold [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (clear : Guard → Bool) (top : Guard) (fuel readFuel comparisonFuel nativeFuel : Nat) (values : List (Value Symbol Guard)) (seed : List Int) :
    List (List Int) → NativeState width Symbol Guard → Result width Symbol Guard (Value Symbol Guard)
  | [], before => operand clear top fuel readFuel comparisonFuel seed values before
  | path :: paths, before => (operand clear top fuel readFuel comparisonFuel path values before).bind fun value middle =>
      (fold emptyGuard conjoin clear top fuel readFuel comparisonFuel nativeFuel values seed paths middle).bind fun tail later =>
        leaf emptyGuard conjoin nativeFuel value tail later

/-- The source empty target returns EmptyNode; nonempty targets use their first path as deferred seed. -/
def target [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (clear : Guard → Bool) (top : Guard) (fuel readFuel comparisonFuel nativeFuel : Nat) (values : List (Value Symbol Guard))
    (paths : List (List Int)) (before : NativeState width Symbol Guard) : Result width Symbol Guard (Value Symbol Guard) :=
  match paths with
  | [] => .done .empty before
  | seed :: rest => fold emptyGuard conjoin clear top fuel readFuel comparisonFuel nativeFuel values seed rest before

end MicroCFTA.SourceEqualityDemandTargetWorker
