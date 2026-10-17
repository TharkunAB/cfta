import MicroCFTA.InternedFreshOrdinaryClosedCompletion
import MicroCFTA.InternedFreshOrdinaryFacts
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
namespace MicroCFTA.SourceProfilePrototype
open InternedConstructorTemplates InternedNestedConstruction
private def plan : Syntax Nat Bool := .union [
  .binder false (.node [.mk 0 true [.var 0]]),
  .node [.mk 1 false [], .mk 2 true [.node [.mk 3 true []], .node [.mk 3 true []]]]]
set_option pp.deepTerms true in
set_option pp.maxSteps 1000000 in
#reduce match InternedFreshOrdinaryConstruction.build plan [] empty with
  | .done value state => (value.referenceOf, state.nodes.next, state.edges.next,
    match value with
    | .union _ members _ _ => members.map Value.referenceOf
    | _ => [])
  | .pending _ _ => (.empty, 0, 0, [])
end MicroCFTA.SourceProfilePrototype
