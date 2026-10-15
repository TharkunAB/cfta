import MicroCFTA.SourceEqualityNativeEditGraph
import MicroCFTA.SourceEqualityRequiredWorker

/-!
# Instrumented simultaneous edits over the full native state

Three separate bounds instrument edit recursion, head reads, and native leaf
requests. Constructor and native failures retain their actual observations.
No native memo or domain cache is reinitialized between calls.
-/
namespace MicroCFTA.SourceEqualityNativeEditWorker
open InternedConstructorTemplates SourceEqualityEdits SourceEqualityNativeEditGraph SourceEqualityNativeScoped

/-- Worker observations retain complete native state or an actual incomplete native leaf observation. -/
inductive Result (width : Nat) (Symbol Guard A : Type) : Type 1 where
  | done (value : A) (state : NativeState width Symbol Guard)
  | pending (key : InternedBinderProtocol.NodeKey) (state : NativeState width Symbol Guard)
  | unresolved (name : InternedBinderProtocol.Reference) (state : NativeState width Symbol Guard)
  | exhausted (limit : SourceEqualityRequiredWorker.Limit) (state : NativeState width Symbol Guard)
  | native (observation : SourceRecursiveIntersectionNative.Outcome width Symbol Guard (Value Symbol Guard))

/-- Only a completed preceding operation enters its continuation. -/
def Result.bind (result : Result width Symbol Guard A)
    (next : A → NativeState width Symbol Guard → Result width Symbol Guard B) : Result width Symbol Guard B :=
  match result with
  | .done value state => next value state
  | .pending key state => .pending key state
  | .unresolved name state => .unresolved name state
  | .exhausted limit state => .exhausted limit state
  | .native observation => .native observation

/-- Actual constructor work updates only the heap of the retained full native state. -/
def work [DecidableEq (EdgeKey Symbol Guard)] (request : Work Symbol Guard A) (state : NativeState width Symbol Guard) : Result width Symbol Guard A :=
  let actual := run request state.machine.heap
  .done actual.1 (advanceHeap state actual.2)

/-- Actual head normalization keeps each returned cache and source failure. -/
def head [DecidableEq (EdgeKey Symbol Guard)] (readFuel : Nat) (value : Value Symbol Guard) (state : NativeState width Symbol Guard) :
    Result width Symbol Guard (Value Symbol Guard) :=
  match SourceEqualityRequiredWorker.head readFuel value state.machine.heap with
  | .done result heap => .done result (advanceHeap state heap)
  | .pending key heap => .pending key (advanceHeap state heap)
  | .unresolved name heap => .unresolved name (advanceHeap state heap)
  | .exhausted limit heap => .exhausted limit (advanceHeap state heap)

/-- A native leaf passes its actual full result or actual noncompleted observation to the edit worker. -/
def leaf [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (nativeFuel : Nat) (target value : Value Symbol Guard) (state : NativeState width Symbol Guard) : Result width Symbol Guard (Value Symbol Guard) :=
  match SourceRecursiveIntersectionNative.execute emptyGuard conjoin nativeFuel
      (.node ⟨IntersectionEmptyDomain.emptyDomain, target, value⟩ .pure) state with
  | .done result after => .done result after
  | other => .native other

/-- Visit each existing child position with its selected signed edit subtree. -/
def children (recur : Edits (Value Symbol Guard) → Value Symbol Guard → NativeState width Symbol Guard → Result width Symbol Guard (Value Symbol Guard))
    (entries : List (Int × Edits (Value Symbol Guard))) : Nat → List (Value Symbol Guard) → NativeState width Symbol Guard → Result width Symbol Guard (List (Value Symbol Guard))
  | _, [], state => .done [] state
  | index, value :: values, state => match SourceEqualityNeededMap.lookup (index : Int) entries with
    | none => (children recur entries (index + 1) values state).bind fun results after => .done (value :: results) after
    | some edits => (recur edits value state).bind fun result middle =>
        (children recur entries (index + 1) values middle).bind fun results after => .done (result :: results) after

/-- Rebuild every original edge in order, retaining its symbol and complete guard. -/
def rows [DecidableEq (EdgeKey Symbol Guard)]
    (recur : Edits (Value Symbol Guard) → Value Symbol Guard → NativeState width Symbol Guard → Result width Symbol Guard (Value Symbol Guard))
    (entries : List (Int × Edits (Value Symbol Guard))) : List (EdgeValue Symbol Guard) → NativeState width Symbol Guard → Result width Symbol Guard (List (EdgeValue Symbol Guard))
  | [], state => .done [] state
  | edge :: edges, state => (children recur entries 0 edge.children state).bind fun values middle =>
      (work (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle).bind fun result afterEdge =>
        (rows recur entries edges afterEdge).bind fun results after => .done (result :: results) after

/-- Execute native leaves before node inspection and retain actual normalized recursive branches. -/
def edit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) :
    Nat → Nat → Nat → Edits (Value Symbol Guard) → Value Symbol Guard → NativeState width Symbol Guard → Result width Symbol Guard (Value Symbol Guard)
  | 0, _, _, _, _, state => .exhausted .worker state
  | _ + 1, _, nativeFuel, .editAt target, value, state => leaf emptyGuard conjoin nativeFuel target value state
  | fuel + 1, readFuel, nativeFuel, .editBelow entries, value, state => match value with
    | .empty => .done .empty state
    | .reference name => .unresolved name state
    | .node _ edges _ _ => (rows (edit emptyGuard conjoin fuel readFuel nativeFuel) entries edges state).bind fun rebuilt after => work (makeNode rebuilt) after
    | .mu .. | .union .. => (head readFuel value state).bind fun exposed after => edit emptyGuard conjoin fuel readFuel nativeFuel (.editBelow entries) exposed after

/-- Child-list leaves are ignored, with no native request or worker consumption. -/
def editList (recur : Edits (Value Symbol Guard) → Value Symbol Guard → NativeState width Symbol Guard → Result width Symbol Guard (Value Symbol Guard))
    (edits : Edits (Value Symbol Guard)) (values : List (Value Symbol Guard)) (state : NativeState width Symbol Guard) : Result width Symbol Guard (List (Value Symbol Guard)) :=
  match edits with
  | .editAt _ => .done values state
  | .editBelow entries => children recur entries 0 values state

/-- Execute the actual signed right-fold edit compiler before the source child-list entry. -/
def editAll [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel readFuel nativeFuel : Nat) (edits : List (Path × Value Symbol Guard)) (values : List (Value Symbol Guard)) (state : NativeState width Symbol Guard) :
    Result width Symbol Guard (List (Value Symbol Guard)) := editList (edit emptyGuard conjoin fuel readFuel nativeFuel) (build edits) values state

end MicroCFTA.SourceEqualityNativeEditWorker
