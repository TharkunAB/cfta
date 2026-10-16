import MicroCFTA.SourceCurrentMemoTargetWorker
import MicroCFTA.SourceCurrentMemoSharedTargetLeaf

/-!
# Executable memo-aware shared target forcing and leaves

Target hits reuse the entire shared state. A miss threads the actual target
worker's native state and completed merge table. Native intersection retains
that returned table and the shared slots. Failed stages retain their exact
diagnostic and reached shared state. This worker models completed merge
calls. Pending publication and runtime forcing remain separate boundaries.
-/
namespace MicroCFTA.SourceCurrentMemoSharedLeafWorker
open InternedConstructorTemplates SourceCurrentMemoSharedTargetState

/-- Stage diagnostics retain complete target and native observations. Head diagnostics serve shared edits. -/
inductive Fault (width : Nat) (Symbol Guard : Type) : Type 1 where
  | target (fault : SourceCurrentMemoTargetWorker.Fault width Symbol Guard)
  | native (observation : SourceRecursiveIntersectionNative.Outcome width Symbol Guard (Value Symbol Guard))
  | pending (key : InternedBinderProtocol.NodeKey)
  | unresolved (name : InternedBinderProtocol.Reference)
  | exhausted (limit : SourceEqualityRequiredWorker.Limit)

/-- Every completed value or failed prefix retains the full reached shared state. -/
inductive Outcome (width : Nat) (Symbol Guard A : Type) : Type 1 where
  | done (value : A) (state : State width Symbol Guard)
  | failed (fault : Fault width Symbol Guard) (state : State width Symbol Guard)

def Outcome.state : Outcome width Symbol Guard A → State width Symbol Guard
  | .done _ state | .failed _ state => state

/-- Failed prefixes keep their exact diagnostic and state without entering a continuation. -/
def Outcome.bind (first : Outcome width Symbol Guard A)
    (next : A → State width Symbol Guard → Outcome width Symbol Guard B) : Outcome width Symbol Guard B :=
  match first with
  | .done value state => next value state
  | .failed fault state => .failed fault state

/-- Reuse a returned slot or run the actual target worker and store its completed result. -/
def force [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (projectionFuel readFuel mergeFuel selectionFuel nativeFuel : Nat)
    (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
    (path : EqualityNormalize.Path) (before : State width Symbol Guard) : Outcome width Symbol Guard (Value Symbol Guard) :=
  match before.targets path with
  | some value => .done value before
  | none => match SourceCurrentMemoTargetWorker.target emptyGuard conjoin clear top projectionFuel readFuel mergeFuel selectionFuel nativeFuel
      originals (SourceEqualityClassTarget.operandPaths record.paths path) before.native before.memo with
    | .done value native saved => .done value (store before path value native saved)
    | .failed fault native saved => .failed (.target fault) {before with native := native, memo := saved}

/-- Native intersection retains the exact merge table and slots returned by target forcing. -/
def step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (nativeFuel : Nat)
    (target input : Value Symbol Guard) (before : State width Symbol Guard) : Outcome width Symbol Guard (Value Symbol Guard) :=
  match SourceRecursiveIntersectionNative.execute emptyGuard conjoin nativeFuel
      (.node ⟨IntersectionEmptyDomain.emptyDomain, target, input⟩ .pure) before.native with
  | .done value native => .done value (advance before native)
  | other => .failed (.native other) (advance before other.state)

/-- A leaf forces its shared target before intersecting at the actual returned state. -/
def leaf [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (projectionFuel readFuel mergeFuel selectionFuel nativeFuel : Nat)
    (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
    (path : EqualityNormalize.Path) (input : Value Symbol Guard) (before : State width Symbol Guard) : Outcome width Symbol Guard (Value Symbol Guard) :=
  (force emptyGuard conjoin clear top projectionFuel readFuel mergeFuel selectionFuel nativeFuel record originals path before).bind
    fun target middle => step emptyGuard conjoin nativeFuel target input middle

/-- Reusing a stored target ignores all five worker bounds and returns the complete original state. -/
theorem force_hit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (p h w c n : Nat) (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
    (path : EqualityNormalize.Path) (before : State width Symbol Guard) (value : Value Symbol Guard)
    (present : before.targets path = some value) :
    force emptyGuard conjoin clear top p h w c n record originals path before = .done value before := by
  simp only [force, present]

/-- A failed target prefix retains its exact native state, completed table, and all earlier slots. -/
theorem force_failed [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (p h w c n : Nat) (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
    (path : EqualityNormalize.Path) (before : State width Symbol Guard)
    (absent : before.targets path = none) (fault : SourceCurrentMemoTargetWorker.Fault width Symbol Guard)
    (native : SourceRecursiveIntersectionThunks.State width Symbol Guard) (saved : SourceCurrentMemoMergeGraph.Memo Symbol Guard)
    (failed : SourceCurrentMemoTargetWorker.target emptyGuard conjoin clear top p h w c n originals
      (SourceEqualityClassTarget.operandPaths record.paths path) before.native before.memo = .failed fault native saved) :
    force emptyGuard conjoin clear top p h w c n record originals path before =
      .failed (.target fault) {before with native := native, memo := saved} := by
  simp only [force, absent, failed]

/-- Every native observation retains its exact reached state and leaves shared slots and merge entries unchanged. -/
theorem step_state [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (n : Nat)
    (target input : Value Symbol Guard) (before : State width Symbol Guard) :
    (step emptyGuard conjoin n target input before).state.native =
      (SourceRecursiveIntersectionNative.execute emptyGuard conjoin n
        (.node ⟨IntersectionEmptyDomain.emptyDomain, target, input⟩ .pure) before.native).state ∧
    (step emptyGuard conjoin n target input before).state.targets = before.targets ∧
    (step emptyGuard conjoin n target input before).state.memo = before.memo := by
  cases actual : SourceRecursiveIntersectionNative.execute emptyGuard conjoin n
      (.node ⟨IntersectionEmptyDomain.emptyDomain, target, input⟩ .pure) before.native <;>
    simp only [step, actual, Outcome.state, advance, SourceRecursiveIntersectionNative.Outcome.state, and_self]

end MicroCFTA.SourceCurrentMemoSharedLeafWorker
