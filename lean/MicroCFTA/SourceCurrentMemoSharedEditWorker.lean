import MicroCFTA.SourceCurrentMemoSharedEditGraph
import MicroCFTA.SourceCurrentMemoSharedLeafWorker

/-!
# Executable simultaneous edits with the completed merge table

Six bounds instrument edit recursion, projection, head reads, merge work,
selection, and native intersection. Every branch retains the actual native
state, shared target slots, and completed merge table. A failed observation
stops the enclosing source control at that returned state.
-/
namespace MicroCFTA.SourceCurrentMemoSharedEditWorker
open InternedConstructorTemplates SourceEqualityEdits SourceCurrentMemoSharedEditGraph
open SourceCurrentMemoSharedTargetState SourceCurrentMemoSharedLeafWorker

/-- Constructor work advances only the heap in the retained shared state. -/
def work [DecidableEq (EdgeKey Symbol Guard)] (request : Work Symbol Guard A)
    (state : SharedState width Symbol Guard) : Outcome width Symbol Guard A :=
  let actual := run request state.native.machine.heap
  .done actual.1 (advanceHeap state actual.2)

/-- Head normalization retains the exact returned heap and source diagnostic. -/
def head [DecidableEq (EdgeKey Symbol Guard)] (readFuel : Nat) (value : Value Symbol Guard)
    (state : SharedState width Symbol Guard) : Outcome width Symbol Guard (Value Symbol Guard) :=
  match SourceEqualityRequiredWorker.head readFuel value state.native.machine.heap with
  | .done result heap => .done result (advanceHeap state heap)
  | .pending key heap => .failed (.pending key) (advanceHeap state heap)
  | .unresolved name heap => .failed (.unresolved name) (advanceHeap state heap)
  | .exhausted limit heap => .failed (.exhausted limit) (advanceHeap state heap)

/-- Visit each existing child position with its selected signed edit subtree. -/
def children
    (recur : Edits EqualityNormalize.Path → Value Symbol Guard → SharedState width Symbol Guard → Outcome width Symbol Guard (Value Symbol Guard))
    (entries : List (Int × Edits EqualityNormalize.Path)) :
    Nat → List (Value Symbol Guard) → SharedState width Symbol Guard → Outcome width Symbol Guard (List (Value Symbol Guard))
  | _, [], state => .done [] state
  | index, value :: values, state => match SourceEqualityNeededMap.lookup (index : Int) entries with
    | none => (children recur entries (index + 1) values state).bind fun results after => .done (value :: results) after
    | some edits => (recur edits value state).bind fun result middle =>
        (children recur entries (index + 1) values middle).bind fun results after => .done (result :: results) after

/-- Rebuild every original edge in order with its symbol and full guard. -/
def rows [DecidableEq (EdgeKey Symbol Guard)]
    (recur : Edits EqualityNormalize.Path → Value Symbol Guard → SharedState width Symbol Guard → Outcome width Symbol Guard (Value Symbol Guard))
    (entries : List (Int × Edits EqualityNormalize.Path)) :
    List (EdgeValue Symbol Guard) → SharedState width Symbol Guard → Outcome width Symbol Guard (List (EdgeValue Symbol Guard))
  | [], state => .done [] state
  | edge :: edges, state => (children recur entries 0 edge.children state).bind fun values middle =>
      (work (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle).bind fun result afterEdge =>
        (rows recur entries edges afterEdge).bind fun results after => .done (result :: results) after

/-- Execute a shared leaf before node inspection and retain actual recursive head prefixes. -/
def edit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) :
    Nat → Nat → Nat → Nat → Nat → Nat → Edits EqualityNormalize.Path → Value Symbol Guard → SharedState width Symbol Guard → Outcome width Symbol Guard (Value Symbol Guard)
  | 0, _, _, _, _, _, _, _, state => .failed (.exhausted .worker) state
  | _ + 1, p, h, w, c, n, .editAt target, value, state => leaf emptyGuard conjoin clear top p h w c n record originals target value state
  | fuel + 1, p, h, w, c, n, .editBelow entries, value, state => match value with
    | .empty => .done .empty state
    | .reference name => .failed (.unresolved name) state
    | .node _ edges _ _ =>
        (rows (edit emptyGuard conjoin clear top record originals fuel p h w c n) entries edges state).bind fun rebuilt after => work (makeNode rebuilt) after
    | .mu .. | .union .. =>
        (head h value state).bind fun exposed after => edit emptyGuard conjoin clear top record originals fuel p h w c n (.editBelow entries) exposed after

/-- Child-list leaves return their inputs without a target or native request. -/
def editList
    (recur : Edits EqualityNormalize.Path → Value Symbol Guard → SharedState width Symbol Guard → Outcome width Symbol Guard (Value Symbol Guard))
    (edits : Edits EqualityNormalize.Path) (values : List (Value Symbol Guard))
    (state : SharedState width Symbol Guard) : Outcome width Symbol Guard (List (Value Symbol Guard)) :=
  match edits with
  | .editAt _ => .done values state
  | .editBelow entries => children recur entries 0 values state

/-- Compile the signed edit list before entering the ordered shared child scan. -/
def editAll [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
    (e p h w c n : Nat) (edits : List (Path × EqualityNormalize.Path)) (values : List (Value Symbol Guard))
    (state : SharedState width Symbol Guard) : Outcome width Symbol Guard (List (Value Symbol Guard)) :=
  editList (edit emptyGuard conjoin clear top record originals e p h w c n) (build edits) values state

end MicroCFTA.SourceCurrentMemoSharedEditWorker
