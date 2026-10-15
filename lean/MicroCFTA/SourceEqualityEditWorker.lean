import MicroCFTA.SourceEqualityEditGraph

/-!
# Instrumented physical simultaneous edit worker

Worker and head-read bounds remain separate. Callbacks retain their explicit
partial result. The bounds instrument source recursion, not the callback's
internal work. Native lazy callback scheduling is not asserted here.
-/
namespace MicroCFTA.SourceEqualityEditWorker
open InternedConstructorTemplates SourceEqualityEdits SourceEqualityEditGraph
open SourceEqualityRequiredWorker (Result work head)

/-- Scan original child positions and invoke the selected edit subtree. -/
def children (recur : Edits Action → Value Symbol Guard → State Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (entries : List (Int × Edits Action)) : Nat → List (Value Symbol Guard) → State Symbol Guard →
      Result Symbol Guard (List (Value Symbol Guard))
  | _, [], state => .done [] state
  | index, value :: rest, state =>
      match SourceEqualityNeededMap.lookup (index : Int) entries with
      | none => (children recur entries (index + 1) rest state).bind fun results after => .done (value :: results) after
      | some edits => (recur edits value state).bind fun result middle =>
          (children recur entries (index + 1) rest middle).bind fun results after => .done (result :: results) after

/-- Rebuild every source row with its original label and complete guard. -/
def rows [DecidableEq (EdgeKey Symbol Guard)]
    (recur : Edits Action → Value Symbol Guard → State Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (entries : List (Int × Edits Action)) : List (EdgeValue Symbol Guard) → State Symbol Guard →
      Result Symbol Guard (List (EdgeValue Symbol Guard))
  | [], state => .done [] state
  | edge :: rest, state =>
      (children recur entries 0 edge.children state).bind fun values middle =>
        (work (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle).bind fun result afterEdge =>
          (rows recur entries rest afterEdge).bind fun results after => .done (result :: results) after

/-- Execute leaf callbacks first, then follow the actual empty, ordinary, and recursive branches. -/
def edit [DecidableEq (EdgeKey Symbol Guard)] (call : Callback Action Symbol Guard) :
    Nat → Nat → Edits Action → Value Symbol Guard → State Symbol Guard → Result Symbol Guard (Value Symbol Guard)
  | 0, _, _, _, state => .exhausted .worker state
  | _ + 1, _, .editAt action, value, state => call action value state
  | fuel + 1, readFuel, .editBelow entries, value, state =>
      match value with
      | .empty => .done .empty state
      | .reference name => .unresolved name state
      | .node _ edges _ _ => (rows (edit call fuel readFuel) entries edges state).bind fun rebuilt after => work (makeNode rebuilt) after
      | value@(.mu ..) | value@(.union ..) =>
          (head readFuel value state).bind fun exposed after => edit call fuel readFuel (.editBelow entries) exposed after

/-- A child-list leaf returns unchanged without invoking its callback. -/
def editList (recur : Edits Action → Value Symbol Guard → State Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (edits : Edits Action) (values : List (Value Symbol Guard)) (state : State Symbol Guard) :
    Result Symbol Guard (List (Value Symbol Guard)) :=
  match edits with
  | .editAt _ => .done values state
  | .editBelow entries => children recur entries 0 values state

/-- Compile the original source edit pairs before the child-list traversal. -/
def editAll [DecidableEq (EdgeKey Symbol Guard)] (call : Callback Action Symbol Guard)
    (fuel readFuel : Nat) (edits : List (Path × Action)) (values : List (Value Symbol Guard)) (state : State Symbol Guard) :
    Result Symbol Guard (List (Value Symbol Guard)) :=
  editList (edit call fuel readFuel) (build edits) values state

/-- An empty source edit map never invokes a child callback. -/
theorem children_empty (recur : Edits Action → Value Symbol Guard → State Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (index : Nat) (values : List (Value Symbol Guard)) (state : State Symbol Guard) :
    children recur [] index values state = .done values state := by
  induction values generalizing index with
  | nil => rfl
  | cons value rest ih => simp only [children, SourceEqualityNeededMap.lookup, ih (index + 1), Result.bind]

/-- Empty source edits preserve arbitrary forests even at zero proof bounds. -/
theorem editAll_empty [DecidableEq (EdgeKey Symbol Guard)] (call : Callback Action Symbol Guard)
    (fuel readFuel : Nat) (values : List (Value Symbol Guard)) (state : State Symbol Guard) :
    editAll call fuel readFuel [] values state = .done values state :=
  children_empty _ 0 values state

/-- A leaf callback at a bare reference runs before the unresolved-reference branch. -/
theorem leaf_reference [DecidableEq (EdgeKey Symbol Guard)] (call : Callback Action Symbol Guard)
    (fuel readFuel : Nat) (action : Action) (name : InternedBinderProtocol.Reference) (state : State Symbol Guard) :
    edit call (fuel + 1) readFuel (.editAt action) (.reference name) state = call action (.reference name) state := rfl

end MicroCFTA.SourceEqualityEditWorker
