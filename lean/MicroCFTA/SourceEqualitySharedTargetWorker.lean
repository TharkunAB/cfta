import MicroCFTA.SourceEqualitySharedTargetLeafComplete
import MicroCFTA.SourceEqualityDemandTargetWorkerComplete

/-!
# Executable shared class target closures

A hit returns the stored value without a target request. A miss runs the
actual demanded target worker and stores its completed result. Incomplete
observations retain the shared slots and the native stage observation.
-/
namespace MicroCFTA.SourceEqualitySharedTargetWorker
open InternedConstructorTemplates SourceEqualitySharedTargetState SourceEqualitySharedTargetForce SourceEqualitySharedTargetLeaf

/-- Completed values and incomplete stages retain the original shared closure slots. -/
inductive Result (width : Nat) (Symbol Guard A : Type) : Type 1 where
  | done (value : A) (state : State width Symbol Guard)
  | pending (key : InternedBinderProtocol.NodeKey) (state : State width Symbol Guard)
  | unresolved (name : InternedBinderProtocol.Reference) (state : State width Symbol Guard)
  | exhausted (limit : SourceEqualityRequiredWorker.Limit) (state : State width Symbol Guard)
  | target (observation : SourceEqualityDemandTargetWorker.Result width Symbol Guard (Value Symbol Guard)) (state : State width Symbol Guard)
  | native (observation : SourceRecursiveIntersectionNative.Outcome width Symbol Guard (Value Symbol Guard)) (state : State width Symbol Guard)

/-- Only a completed stage enters its continuation at the returned shared state. -/
def Result.bind (result : Result width Symbol Guard A) (next : A → State width Symbol Guard → Result width Symbol Guard B) : Result width Symbol Guard B :=
  match result with
  | .done value state => next value state
  | .pending key state => .pending key state
  | .unresolved name state => .unresolved name state
  | .exhausted limit state => .exhausted limit state
  | .target observation state => .target observation state
  | .native observation state => .native observation state

/-- Reuse a returned slot or demand and store its actual target at first force. -/
def force [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (p h c n : Nat) (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
    (path : EqualityNormalize.Path) (before : State width Symbol Guard) : Result width Symbol Guard (Value Symbol Guard) :=
  match before.targets path with
  | some value => .done value before
  | none => match SourceEqualityDemandTargetWorker.target emptyGuard conjoin clear top p h c n originals
      (SourceEqualityClassTarget.operandPaths record.paths path) before.native with
    | .done value native => .done value (store before path value native)
    | other => .target other before

/-- Intersect the forced target with the input at its returned warm native state. -/
def step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (n : Nat) (target input : Value Symbol Guard)
    (before : State width Symbol Guard) : Result width Symbol Guard (Value Symbol Guard) :=
  match SourceRecursiveIntersectionNative.execute emptyGuard conjoin n (.node ⟨IntersectionEmptyDomain.emptyDomain, target, input⟩ .pure) before.native with
  | .done value native => .done value (advance before native)
  | other => .native other before

/-- The leaf forces its shared target before the actual native request. -/
def leaf [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (p h c n : Nat) (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
    (path : EqualityNormalize.Path) (input : Value Symbol Guard) (before : State width Symbol Guard) : Result width Symbol Guard (Value Symbol Guard) :=
  (force emptyGuard conjoin clear top p h c n record originals path before).bind fun target middle => step emptyGuard conjoin n target input middle

end MicroCFTA.SourceEqualitySharedTargetWorker
