import MicroCFTA.InternedFreshOrdinaryClosedCompletion
namespace MicroCFTA.NumericFuelSourceKernel
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedConstruction (Syntax)
open SourceRecursiveIntersectionInputView SourceRecursiveIntersectionNative IntersectSchedule

private def fixture : Syntax Nat Bool :=
  .node [.mk 99 true [
    .binder false (.union [.node [.mk 0 true []], .node [.mk 1 true [.var 0]]]),
    .binder false (.union [.node [.mk 0 false []], .node [.mk 1 true [.var 0]]]),
    .union [.node [.mk 2 true []], .node [.mk 3 false []]]]]
private def kind : Value Nat Bool → Nat
  | .empty => 0
  | .reference _ => 1
  | .node _ _ _ _ => 2
  | .union _ _ _ _ => 3
  | .mu _ _ _ _ => 4

#eval match InternedFreshOrdinaryConstruction.build fixture [] empty with
  | .done value state => ((children value).map kind, state.nodes.next, state.edges.next)
  | .pending _ state => ([], state.nodes.next, state.edges.next)
end MicroCFTA.NumericFuelSourceKernel
