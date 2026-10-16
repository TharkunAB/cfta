import MicroCFTA.SourceCurrentAllocatedSharedEditGraph
import MicroCFTA.SourceCurrentAllocatedSharedTargetWorker
import MicroCFTA.SourceEqualityRequiredWorker

/-!
# Bounded current edits in the full shared checked state

Six bounds control edit recursion, projection, reads, merge work,
selection, and checked native execution. Each branch retains the returned
checked state, target slots, and merge memo. A failed prefix stops before
its continuation. Row reconstruction retains the original raw guard.
The completed serial schedule does not establish host forcing order.
-/
namespace MicroCFTA.SourceCurrentAllocatedSharedEditWorker
open InternedConstructorTemplates SourceEqualityEdits
open SourceCurrentAllocatedSharedEditGraph (SharedState advanceHeap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Record" => SourceEqualityClassOrder.Record

/-- Leaf failures retain their complete native diagnostic. Head failures retain their source reason. -/
inductive Fault (width : Nat) : Type 1 where
  | leaf (fault : SourceCurrentAllocatedSharedTargetWorker.Fault width)
  | pending (key : InternedBinderProtocol.NodeKey)
  | unresolved (name : InternedBinderProtocol.Reference)
  | exhausted (limit : SourceEqualityRequiredWorker.Limit)

/-- Success and failure retain the entire current shared state. -/
inductive Outcome (width : Nat) (Output : Type) : Type 1 where
  | done (output : Output) (state : SharedState width)
  | failed (fault : Fault width) (state : SharedState width)

def Outcome.state : Outcome width Output → SharedState width
  | .done _ state | .failed _ state => state

/-- Only a completed prefix enters the next stage at its literal returned state. -/
def Outcome.bind (first : Outcome width Input)
    (next : Input → SharedState width → Outcome width Output) : Outcome width Output :=
  match first with
  | .done value state => next value state
  | .failed fault state => .failed fault state

/-- Lift each current shared leaf observation without changing its returned state. -/
def lift : SourceCurrentAllocatedSharedTargetWorker.Outcome width → Outcome width (Value Symbol Guard)
  | .done value state => .done value state
  | .failed fault state => .failed (.leaf fault) state

/-- A selected leaf runs the literal current target force and checked intersection. -/
noncomputable def leaf [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (p h m s n : Nat) (record : Record) (originals : List (Value Symbol Guard))
    (target : EqualityNormalize.Path) (input : Value Symbol Guard) (state : SharedState width) :
    Outcome width (Value Symbol Guard) :=
  lift (SourceCurrentAllocatedSharedTargetWorker.leaf p h m s n record originals target input state)

/-- Constructor work advances only the heap and retains every other state component. -/
def work [DecidableEq (EdgeKey Symbol Guard)] (request : Work Symbol Guard Output)
    (state : SharedState width) : Outcome width Output :=
  let actual := run request state.checked.native.machine.heap
  .done actual.1 (advanceHeap state actual.2)

/-- Actual head normalization retains its returned heap and exact source diagnostic. -/
def head [DecidableEq (EdgeKey Symbol Guard)] (readFuel : Nat) (value : Value Symbol Guard)
    (state : SharedState width) : Outcome width (Value Symbol Guard) :=
  match SourceEqualityRequiredWorker.head readFuel value state.checked.native.machine.heap with
  | .done result heap => .done result (advanceHeap state heap)
  | .pending key heap => .failed (.pending key) (advanceHeap state heap)
  | .unresolved name heap => .failed (.unresolved name) (advanceHeap state heap)
  | .exhausted limit heap => .failed (.exhausted limit) (advanceHeap state heap)

/-- Visit existing child positions and execute only their selected signed edit subtree. -/
def children
    (recur : Edits EqualityNormalize.Path → Value Symbol Guard → SharedState width → Outcome width (Value Symbol Guard))
    (entries : List (Int × Edits EqualityNormalize.Path)) :
    Nat → List (Value Symbol Guard) → SharedState width → Outcome width (List (Value Symbol Guard))
  | _, [], state => .done [] state
  | index, value :: values, state => match SourceEqualityNeededMap.lookup (index : Int) entries with
    | none => (children recur entries (index + 1) values state).bind fun results after => .done (value :: results) after
    | some edits => (recur edits value state).bind fun result middle =>
        (children recur entries (index + 1) values middle).bind fun results after => .done (result :: results) after

/-- Rebuild rows in order with each original symbol and full raw guard. -/
def rows [DecidableEq (EdgeKey Symbol Guard)]
    (recur : Edits EqualityNormalize.Path → Value Symbol Guard → SharedState width → Outcome width (Value Symbol Guard))
    (entries : List (Int × Edits EqualityNormalize.Path)) :
    List (EdgeValue Symbol Guard) → SharedState width → Outcome width (List (EdgeValue Symbol Guard))
  | [], state => .done [] state
  | edge :: edges, state => (children recur entries 0 edge.children state).bind fun values middle =>
      (work (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle).bind fun result afterEdge =>
        (rows recur entries edges afterEdge).bind fun results after => .done (result :: results) after

/-- Execute shared leaves before node inspection and retain each recursive head prefix. -/
noncomputable def edit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (record : Record) (originals : List (Value Symbol Guard)) :
    Nat → Nat → Nat → Nat → Nat → Nat → Edits EqualityNormalize.Path → Value Symbol Guard →
      SharedState width → Outcome width (Value Symbol Guard)
  | 0, _, _, _, _, _, _, _, state => .failed (.exhausted .worker) state
  | _ + 1, p, h, m, s, n, .editAt target, value, state => leaf p h m s n record originals target value state
  | fuel + 1, p, h, m, s, n, .editBelow entries, value, state => match value with
    | .empty => .done .empty state
    | .reference name => .failed (.unresolved name) state
    | .node _ edges _ _ =>
        (rows (edit record originals fuel p h m s n) entries edges state).bind fun rebuilt after => work (makeNode rebuilt) after
    | .mu .. | .union .. =>
        (head h value state).bind fun exposed after => edit record originals fuel p h m s n (.editBelow entries) exposed after

/-- A child-list root leaf is ignored without target forcing or native execution. -/
def editList
    (recur : Edits EqualityNormalize.Path → Value Symbol Guard → SharedState width → Outcome width (Value Symbol Guard))
    (edits : Edits EqualityNormalize.Path) (values : List (Value Symbol Guard))
    (state : SharedState width) : Outcome width (List (Value Symbol Guard)) :=
  match edits with
  | .editAt _ => .done values state
  | .editBelow entries => children recur entries 0 values state

/-- Compile the literal signed edit list before its ordered shared child scan. -/
noncomputable def editAll [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (record : Record) (originals : List (Value Symbol Guard))
    (e p h m s n : Nat) (edits : List (Path × EqualityNormalize.Path)) (values : List (Value Symbol Guard))
    (state : SharedState width) : Outcome width (List (Value Symbol Guard)) :=
  editList (edit record originals e p h m s n) (build edits) values state

end MicroCFTA.SourceCurrentAllocatedSharedEditWorker
