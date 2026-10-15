import MicroCFTA.SourceEqualitySharedEditGraph
import MicroCFTA.SourceEqualitySharedTargetWorkerProofs

/-!
# Executable simultaneous edits with shared target closures

Five bounds instrument edit recursion and the four target stages. Native
state and returned target slots pass through every source branch.
Incomplete observations do not resume enclosing source control.
-/
namespace MicroCFTA.SourceEqualitySharedEditWorker
open InternedConstructorTemplates SourceEqualityEdits SourceEqualitySharedEditGraph SourceEqualitySharedTargetState SourceEqualitySharedTargetWorker

/-- Actual constructor work updates only the heap of the retained full native state. -/
def work [DecidableEq (EdgeKey Symbol Guard)] (request : Work Symbol Guard A) (state : SharedState width Symbol Guard) : Result width Symbol Guard A :=
  let actual := run request state.native.machine.heap
  .done actual.1 (advanceHeap state actual.2)

/-- Actual head normalization keeps each returned cache and source failure. -/
def head [DecidableEq (EdgeKey Symbol Guard)] (readFuel : Nat) (value : Value Symbol Guard) (state : SharedState width Symbol Guard) :
    Result width Symbol Guard (Value Symbol Guard) :=
  match SourceEqualityRequiredWorker.head readFuel value state.native.machine.heap with
  | .done result heap => .done result (advanceHeap state heap)
  | .pending key heap => .pending key (advanceHeap state heap)
  | .unresolved name heap => .unresolved name (advanceHeap state heap)
  | .exhausted limit heap => .exhausted limit (advanceHeap state heap)

/-- Visit each existing child position with its selected signed edit subtree. -/
def children (recur : Edits EqualityNormalize.Path → Value Symbol Guard → SharedState width Symbol Guard → Result width Symbol Guard (Value Symbol Guard))
    (entries : List (Int × Edits EqualityNormalize.Path)) : Nat → List (Value Symbol Guard) → SharedState width Symbol Guard → Result width Symbol Guard (List (Value Symbol Guard))
  | _, [], state => .done [] state
  | index, value :: values, state => match SourceEqualityNeededMap.lookup (index : Int) entries with
    | none => (children recur entries (index + 1) values state).bind fun results after => .done (value :: results) after
    | some edits => (recur edits value state).bind fun result middle =>
        (children recur entries (index + 1) values middle).bind fun results after => .done (result :: results) after

/-- Rebuild every original edge in order, retaining its symbol and complete guard. -/
def rows [DecidableEq (EdgeKey Symbol Guard)]
    (recur : Edits EqualityNormalize.Path → Value Symbol Guard → SharedState width Symbol Guard → Result width Symbol Guard (Value Symbol Guard))
    (entries : List (Int × Edits EqualityNormalize.Path)) : List (EdgeValue Symbol Guard) → SharedState width Symbol Guard → Result width Symbol Guard (List (EdgeValue Symbol Guard))
  | [], state => .done [] state
  | edge :: edges, state => (children recur entries 0 edge.children state).bind fun values middle =>
      (work (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle).bind fun result afterEdge =>
        (rows recur entries edges afterEdge).bind fun results after => .done (result :: results) after

/-- Execute shared leaves before node inspection and retain every actual recursive head. -/
def edit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (clear : Guard → Bool) (top : Guard) (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) :
    Nat → Nat → Nat → Nat → Nat → Edits EqualityNormalize.Path → Value Symbol Guard → SharedState width Symbol Guard → Result width Symbol Guard (Value Symbol Guard)
  | 0, _, _, _, _, _, _, state => .exhausted .worker state
  | _ + 1, p, h, c, n, .editAt target, value, state => leaf emptyGuard conjoin clear top p h c n record originals target value state
  | fuel + 1, p, h, c, n, .editBelow entries, value, state => match value with
    | .empty => .done .empty state
    | .reference name => .unresolved name state
    | .node _ edges _ _ => (rows (edit emptyGuard conjoin clear top record originals fuel p h c n) entries edges state).bind fun rebuilt after => work (makeNode rebuilt) after
    | .mu .. | .union .. => (head h value state).bind fun exposed after => edit emptyGuard conjoin clear top record originals fuel p h c n (.editBelow entries) exposed after

/-- Child-list leaves are ignored, with no native request or worker consumption. -/
def editList (recur : Edits EqualityNormalize.Path → Value Symbol Guard → SharedState width Symbol Guard → Result width Symbol Guard (Value Symbol Guard))
    (edits : Edits EqualityNormalize.Path) (values : List (Value Symbol Guard)) (state : SharedState width Symbol Guard) : Result width Symbol Guard (List (Value Symbol Guard)) :=
  match edits with
  | .editAt _ => .done values state
  | .editBelow entries => children recur entries 0 values state

/-- Compile the actual signed edit list before entering the shared child scan. -/
def editAll [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (clear : Guard → Bool) (top : Guard) (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
    (fuel p h c n : Nat) (edits : List (Path × EqualityNormalize.Path)) (values : List (Value Symbol Guard)) (state : SharedState width Symbol Guard) :
    Result width Symbol Guard (List (Value Symbol Guard)) := editList (edit emptyGuard conjoin clear top record originals fuel p h c n) (build edits) values state

end MicroCFTA.SourceEqualitySharedEditWorker
