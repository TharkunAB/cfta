import MicroCFTA.InternedNestedConstruction
/-!
# A closed constructor expression reaches a pending key

The source expression uses only structural constructors and lexical variables.
Its nested discarded children retain their construction effects.
The kernel verifies a pending readback from initially empty caches.
-/
namespace MicroCFTA.InternedClosedPendingBoundary
open InternedConstructorTemplates InternedNestedConstruction
open InternedBinderProtocol (Reference NodeKey)
/-- Context marker edges separate the earlier probe histories. -/
def inner : Syntax Nat Unit := .union [
 .node [.mk 2 () [.binder true (.node [.mk 0 () [.var 3], .mk 0 () [.var 4], .mk 42 () [.var 4, .var 5]]), .empty]],
 .node [.mk 1 () [.binder true (.node [.mk 0 () [.var 0], .mk 0 () [.var 2], .mk 0 () [.var 3], .mk 0 () [.var 4], .mk 42 () [.var 4, .var 5]])]]]
/-- The target pairs its ordinary local with both enclosing captures. -/
def target : Syntax Nat Unit := .binder false (.node [.mk 11 () [.var 1, .var 4, .var 5]])
/-- The target executes before the empty child removes its edge. -/
def discarded : Syntax Nat Unit := .node [.mk 9 () [target, .empty]]
/-- The first operand computes the ordinary level used by the target. -/
def crossed : Syntax Nat Unit := .union [inner, discarded]
/-- The active ancestor discards those effects and retains its original pair. -/
def ancestor : Syntax Nat Unit := .union [.node [.mk 10 () [.binder false crossed, .empty]], .node [.mk 11 () [.var 3, .var 2, .var 3]]]
/-- Actual outer callbacks supply all three captured names in closed execution. -/
def expression : Syntax Nat Unit := .binder true (.union [
  .binder false (.binder true (.node [.mk 3 () [.binder false ancestor, .empty]])),
  .binder false (.var 0)])
/-- Run the whole closed source expression from empty caches. -/
def result := build expression [] (empty : State Nat Unit)
/-- The closed executor stops at a reserved key whose record has not completed. -/
theorem pending : (match result with | .pending .. => true | _ => false) = true := by
  set_option maxRecDepth 30000 in
  set_option cbv.maxSteps 200000000 in cbv
/-- Every reference is in lexical scope. -/
theorem expression_scoped : Scoped 0 expression := by
  simp [expression, ancestor, crossed, discarded, target, inner, Scoped, EdgesScoped, ManyScoped]

/-- Read the stopped pair, its reserved slot, the next counter, and record presence. -/
def observation : Option (NodeKey × Option Nat × Nat × Bool) :=
  match result with
  | .done .. => none
  | .pending key state =>
      some (key, (state.nodes.table key).map (fun entry => entry.identity), state.nodes.next,
        (state.nodeRecords key).isSome)

/-- Both probe references are node 86; slot 87 is reserved and has no completed record. -/
theorem pending_slot : observation = some (.mu ⟨.node 86, .node 86⟩, some 87, 92, false) := by
  set_option maxRecDepth 30000 in
  set_option cbv.maxSteps 200000000 in cbv

/-- The closed source result is an actual pending outcome. -/
theorem pending_result : ∃ key final, build expression [] empty = .pending key final := by
  cases returned : build expression [] empty with
  | done value final =>
      have stopped := pending
      simp only [result, returned] at stopped
      cases stopped
  | pending key final => exact ⟨key, final, rfl⟩

/-- General completion of all scoped closed source expressions is false for this executor. -/
theorem not_all_closed_complete :
    ¬ (∀ expression : Syntax Nat Unit, Scoped 0 expression →
      ∃ value final, build expression [] empty = .done value final) := by
  intro complete
  obtain ⟨value, final, finished⟩ := complete expression expression_scoped
  obtain ⟨key, stopped, unfinished⟩ := pending_result
  rw [finished] at unfinished
  cases unfinished

end MicroCFTA.InternedClosedPendingBoundary
