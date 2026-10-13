import MicroCFTA.InternedPendingProducerDescent

/-!
# A producer path does not preserve result liveness

The source evaluates every child before it removes an edge with an empty child.
The nested binder retains the outer ordinary name in a complete stored record.
The enclosing producer still returns the empty value.
-/
namespace MicroCFTA.InternedProducerPathBoundary
open InternedConstructorTemplates InternedNestedConstruction InternedNestedMissReadback
open InternedActiveSourceOrigins InternedLiveInputContext
open InternedBinderProtocol (Reference)

/-- The nested raw binder reads its outer binder's input. -/
def target : Syntax Nat Unit := .binder false (.var 1)

/-- The second child removes this edge after both children run. -/
def body : Syntax Nat Unit := .node [.mk 0 () [target, .empty]]

/-- A closed outer binder executes the target in its Depth and ordinary callbacks. -/
def expression : Syntax Nat Unit := .binder true body

/-- Execute both source callbacks and the outer request from empty caches. -/
def result := build expression [] (empty : State Nat Unit)

/-- The actual source route reaches the target without another binder crossing. -/
theorem source_path (names : List Reference) : Path body names target names [] := by
  exact .node (symbol := 0) (guard := ()) (children := [target, .empty])
    (by simp) (by simp) (.here _ _)

/-- The selected lexical occurrence is live at the nested binder. -/
theorem target_live : liveInputs target [(Reference.uninterned 0, 0)] = [(.uninterned 0, 0)] := by
  cbv

/-- The same occurrence is absent from the enclosing producer's result support. -/
theorem body_dead : liveInputs body [(Reference.uninterned 0, 0)] = [] := by
  cbv

/-- The closed producer completes with the empty result. -/
theorem complete_empty : (match result with | .done .empty _ => true | _ => false) = true := by
  set_option maxRecDepth 10000 in cbv

/-- The completed target record remains stored after its enclosing edge is removed. -/
theorem retained_target :
    (result.state.nodeRecords (muKey (.reference (.uninterned 0) : Value Nat Unit) (.reference (.uninterned 0)))).map
      (fun value => value.free.contains (.uninterned 0)) = some true := by
  set_option maxRecDepth 10000 in cbv

/-- Every variable is in lexical scope before the closed execution. -/
theorem expression_scoped : InternedNestedConstruction.Scoped 0 expression := by
  simp [expression, body, target, InternedNestedConstruction.Scoped, EdgesScoped, ManyScoped]

end MicroCFTA.InternedProducerPathBoundary
