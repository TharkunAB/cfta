import MicroCFTA.SourceRecursiveIntersectionSourceProfile
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
#eval match InternedFreshOrdinaryConstruction.build plan [] empty with
  | .done value state => ((SourceRecursiveIntersectionSourceProfile.limits state).rows, (SourceRecursiveIntersectionSourceProfile.limits state).members, (SourceRecursiveIntersectionSourceProfile.limits state).arity,
    match value with
    | .union _ members _ _ => members.length
    | _ => 0)
  | .pending _ _ => (0, 0, 0, 0)
#eval match InternedFreshOrdinaryConstruction.build plan [] empty with
  | .done _ state => (List.range state.nodes.next).map fun index =>
    (index, (SourcePreparedSharedRows.read state index).map fun value =>
      match value with
      | .mu _ body _ _ => (2, (InternedEdgeResidency.nodeEdges body).length)
      | .node _ rows _ _ => (1, rows.length)
      | .union _ members _ _ => (3, members.length)
      | _ => (0, 0))
  | .pending _ _ => []
end MicroCFTA.SourceProfilePrototype
