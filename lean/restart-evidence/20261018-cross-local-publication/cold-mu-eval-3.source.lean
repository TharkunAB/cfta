import MicroCFTA.SourceCurrentObservationReaderSupport
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000
namespace MicroCFTA.ColdMuKernels
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (unfold)
private def value (outcome : Outcome Nat Bool (Value Nat Bool)) : Value Nat Bool :=
  match outcome with | .done result _ => result | .pending .. => .empty
private def source : Syntax Nat Bool :=
  .binder true (.binder true (.node [.mk 7 true [.var 1,.var 0]]))
private def built := build source [] empty
private def root := value built
private def before := built.state
private def opened := unfold root before
private def next := value opened
private def after := opened.state
#eval (root.referenceOf, next.referenceOf, before.nodes.next, after.nodes.next,
  root.free, next.free, root.depth, next.depth,
  match opened with | .done .. => true | _ => false)
private def oldNext := unfold next before
private def grownNext := unfold next after
#eval (match oldNext with | .done result state => (true,result.referenceOf,state.nodes.next,(InternedEdgeResidency.nodeEdges result).map (fun row => row.entry.identity)) | .pending .. => (false,InternedBinderProtocol.NodeRef.empty,0,[]))
#eval (match grownNext with | .done result state => (true,result.referenceOf,state.nodes.next,(InternedEdgeResidency.nodeEdges result).map (fun row => row.entry.identity)) | .pending .. => (false,InternedBinderProtocol.NodeRef.empty,0,[]))
end MicroCFTA.ColdMuKernels
