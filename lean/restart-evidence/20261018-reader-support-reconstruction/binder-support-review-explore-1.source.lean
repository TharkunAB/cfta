import MicroCFTA.SourceCurrentReaderFiniteOrdinaryStep
import MicroCFTA.SourceCurrentOpenOriginSteps
import MicroCFTA.SourceCurrentStoredUnionObservations

set_option linter.all true
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000

namespace MicroCFTA.BinderSupportReview
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (unfold)

private def value (outcome : Outcome Nat Bool (Value Nat Bool)) :=
  match outcome with | .done result _ => result | .pending .. => .empty
private def inner : Syntax Nat Bool :=
  .binder true (.node [.mk 2 true [],.mk 3 false [.var 0,.var 1]])
private def source : Syntax Nat Bool :=
  .binder true (.node [.mk 0 true [],.mk 1 false [.var 0,inner]])
private def built := build source [] empty
private def original := value built
private def before := built.state
private def unfolded := unfold original before
private def next := value unfolded
private def after := unfolded.state
private def nested := ((InternedEdgeResidency.nodeEdges next)[1]?.getD (.mk ⟨0,⟨0,[],false⟩⟩ [])).children[1]?.getD .empty
private def cold := unfold nested before
private def warm := unfold nested after

#eval before.nodes.next
#eval after.nodes.next
#eval (InternedEdgeResidency.nodeEdges next).map (fun row => (row.entry.key.symbol,row.children.map Value.depth))
#eval (InternedEdgeResidency.nodeEdges (value cold)).map (fun row => row.entry.key.symbol)
#eval (InternedEdgeResidency.nodeEdges (value warm)).map (fun row => row.entry.key.symbol)
#eval cold.state.nodes.next
#eval warm.state.nodes.next
#eval ((value cold).referenceOf == (value warm).referenceOf)

end MicroCFTA.BinderSupportReview
