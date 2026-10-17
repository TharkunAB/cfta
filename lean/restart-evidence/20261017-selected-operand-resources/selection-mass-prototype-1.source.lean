import MicroCFTA.SourceMergedSelectionCompletion
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace MicroCFTA.SelectionMassPrototype
open InternedConstructorTemplates
private def expression : InternedNestedConstruction.Syntax Nat Bool :=
  .node [.mk 9 true [
    .binder true (.node [.mk 0 true [.var 0], .mk 1 true []]),
    .node [.mk 1 true []]]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def recursive : Value Nat Bool := (InternedProbeProvenance.children root)[0]!
private def narrow : Value Nat Bool := (InternedProbeProvenance.children root)[1]!
private def observed := SourceMergedSelection.select (fun guard => guard) 1 [recursive, narrow] heap
private def after := observed.state

/-- The actual recursive comparison removes the covered ordinary input. -/
theorem actual : observed = .done [recursive] after := by cbv

/-- The actual first comparison allocates a demanded recursive unfolding. -/
theorem allocated : heap.nodes.next < after.nodes.next ∧ heap.edges.next < after.edges.next := by decide

end MicroCFTA.SelectionMassPrototype

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#print axioms MicroCFTA.SelectionMassPrototype.actual
#check @MicroCFTA.SelectionMassPrototype.actual
#print axioms MicroCFTA.SelectionMassPrototype.allocated
#check @MicroCFTA.SelectionMassPrototype.allocated
