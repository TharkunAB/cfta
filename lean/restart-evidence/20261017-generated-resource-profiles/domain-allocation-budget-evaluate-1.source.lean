import MicroCFTA.InternedFreshOrdinaryConstruction
import MicroCFTA.InternedNestedConstructionGrowth
open MicroCFTA MicroCFTA.InternedConstructorTemplates
open MicroCFTA.InternedNestedConstruction (Syntax)
open MicroCFTA.InternedFreshOrdinaryConstruction
private def example : Syntax Nat Bool :=
  .binder false (.node [.mk 7 false [.var 0,
    .binder false (.union [.var 0, .node [.mk 8 true [.var 1]]])]])
#eval let actual := build example [] empty
  (match actual with | .done _ _ => true | .pending _ _ => false,
    actual.state.nodes.next, actual.state.edges.next)
