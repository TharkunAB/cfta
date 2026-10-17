import MicroCFTA.SourceRecursiveIntersectionCompileMassInputs
import MicroCFTA.InternedFreshOrdinaryClosedCompletion
import MicroCFTA.InternedFreshOrdinaryFacts

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace MicroCFTA.CompileInputsIndependent
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionKernel
open InternedNestedConstruction (Syntax Outcome)
local notation "Stored" => InternedValueMassHeap.Stored
local notation "initialBound" => InternedValueMassHeap.initialBound
local notation "Inputs" => SourceRecursiveIntersectionWorkMass.Inputs
local notation "inflate" => InternedFreshOrdinaryResultMass.inflate

private def nodePlan : Syntax Nat Bool := .node [.mk 99 false [
  .node [.mk 0 true [], .mk 0 false [], .mk 1 true []],
  .node [.mk 0 true [], .mk 0 false [], .mk 1 false []]]]
private def nodeBuilt := InternedFreshOrdinaryConstruction.build nodePlan [] empty
private def outer : Value Nat Bool := match nodeBuilt with | .done value _ => value | .pending .. => .empty
private def nodeSource := nodeBuilt.state
private def left : Value Nat Bool := ((children outer)[0]?).getD .empty
private def right : Value Nat Bool := ((children outer)[1]?).getD .empty
private def nodeMachine : Machine Nat Bool := ⟨nodeSource, Cache.emptyState⟩
private def requests := pairs (nodeEdges left) (nodeEdges right)
private def values := requests.map Prod.fst
private def rowCall (rows : EdgeValue Nat Bool × EdgeValue Nat Bool) : Machine Nat Bool → Result Nat Bool (EdgeValue Nat Bool) :=
  edge true (fun first _ => first) (fun first second => execute true (fun a _ => a) 0 IntersectionEmptyDomain.emptyDomain first second)
    rows.1 rows.2
private def nodeBound := initialBound nodeSource + 1

private theorem node_constructed : nodeBuilt = .done outer nodeSource := by
  obtain ⟨value, after, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete nodePlan
  simp only [nodeBuilt, outer, nodeSource, done, Outcome.state]

private theorem node_facts : Facts nodeSource :=
  (InternedFreshOrdinaryFacts.closed_verified nodePlan).facts

private theorem left_right : Available nodeSource left ∧ Available nodeSource right := by
  have available := (InternedFreshOrdinaryFacts.closed_verified nodePlan).result outer nodeSource node_constructed
  have selected : children outer = [left, right] := by cbv
  exact ⟨available.children left (by rw [selected]; simp), available.children right (by rw [selected]; simp)⟩

/-- Distinct constructed node operands produce five literal hash-join calls and their own current square input certificate. -/
theorem constructed_row_inputs :
    InternedFreshOrdinaryConstruction.build nodePlan [] empty = .done outer nodeSource ∧
      left.referenceOf ≠ right.referenceOf ∧ requests.length = 5 ∧
      WalkTrace rowCall requests nodeMachine values nodeMachine ∧
      Inputs (nodeBound * nodeBound) nodeSource (makeNode values) ∧
      SourceEqualityNativeDemandHeapPrimitives.WorkInputs nodeSource (makeNode values) ∧
      Stored (inflate (nodeBound * nodeBound) nodeBound) (run (makeNode values) nodeSource).2 ∧
      (run (makeNode values) nodeSource).2.nodes.next ≤ nodeSource.nodes.next + 1 ∧
      (run (makeNode values) nodeSource).2.edges.next ≤ nodeSource.edges.next + 1 := by
  have walked : walk rowCall requests nodeMachine = .done values nodeMachine := by cbv
  have trace := (walk_done_iff rowCall requests nodeMachine values nodeMachine).mp walked
  have resident : ∀ row ∈ values, EdgeResident nodeSource row := by
    intro row member
    obtain ⟨pair, present, same⟩ := List.mem_map.mp member
    have original := (pairs_member (nodeEdges left) (nodeEdges right) pair).mp present
    subst row
    exact resident_edges nodeSource node_facts.linked left left_right.1.resident pair.1 original.1
  have initial := InternedValueMassHeap.initial nodeSource node_facts
  have inputs := SourceRecursiveIntersectionCompileMassInputs.rows rowCall left right nodeMachine nodeMachine values
    initial left_right.1 left_right.2 (show initialBound nodeSource ≤ nodeBound by omega) trace resident
  have current : Stored nodeBound nodeSource := initial.mono (by omega)
  have result := SourceRecursiveIntersectionWorkMass.run_bound current inputs
  exact ⟨node_constructed, by cbv, by cbv, trace, inputs, inputs.physical,
    result.1, result.2.1, result.2.2⟩

private def unionPlan : Syntax Nat Bool :=
  .union [.binder false (.node [.mk 2 true [.var 0]]), .node [.mk 3 false []]]
private def unionBuilt := InternedFreshOrdinaryConstruction.build unionPlan [] empty
private def original : Value Nat Bool := match unionBuilt with | .done value _ => value | .pending .. => .empty
private def unionSource := unionBuilt.state
private def unionEntry := match original with | .union entry .. => entry | _ => ⟨0, InternedBinderProtocol.NodeKey.node []⟩
private def members : List (Value Nat Bool) := match original with | .union _ values _ _ => values | _ => []
private def level : Nat := match original with | .union _ _ depth _ => depth | _ => 0
private def free : List InternedBinderProtocol.Reference := match original with | .union _ _ _ names => names | _ => []
private def unionMachine : Machine Nat Bool := ⟨unionSource, Cache.emptyState⟩
private def memberCall (member : Value Nat Bool) := execute true (fun first _ => first) 1 IntersectionEmptyDomain.emptyDomain member member
private def unionBound := initialBound unionSource + 1

private theorem union_constructed : unionBuilt = .done original unionSource := by
  obtain ⟨value, after, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete unionPlan
  simp only [unionBuilt, original, unionSource, done, Outcome.state]

private theorem union_shape : original = .union unionEntry members level free := by cbv
private theorem union_facts : Facts unionSource := (InternedFreshOrdinaryFacts.closed_verified unionPlan).facts

/-- A constructed mixed Mu/ordinary union supplies two actual closed-self requests and its own union-emitter certificate. -/
theorem constructed_union_inputs :
    InternedFreshOrdinaryConstruction.build unionPlan [] empty = .done original unionSource ∧
      original = .union unionEntry members level free ∧ members.length = 2 ∧
      WalkTrace memberCall members unionMachine members unionMachine ∧
      Inputs (unionBound * unionBound) unionSource (makeUnion members) ∧
      SourceEqualityNativeDemandHeapPrimitives.WorkInputs unionSource (makeUnion members) ∧
      run (makeUnion members) unionSource = (original, unionSource) ∧
      Stored (inflate (unionBound * unionBound) unionBound) (run (makeUnion members) unionSource).2 ∧
      (run (makeUnion members) unionSource).2.nodes.next ≤ unionSource.nodes.next + 1 ∧
      (run (makeUnion members) unionSource).2.edges.next ≤ unionSource.edges.next + 1 := by
  have originalAvailable := (InternedFreshOrdinaryFacts.closed_verified unionPlan).result original unionSource union_constructed
  have known : Available unionSource (.union unionEntry members level free) := by rw [← union_shape]; exact originalAvailable
  have available : ∀ value ∈ members, Available unionSource value := by
    intro value member
    exact originalAvailable.children value (by rw [union_shape]; exact member)
  have walked : walk memberCall members unionMachine = .done members unionMachine := by cbv
  have trace := (walk_done_iff memberCall members unionMachine members unionMachine).mp walked
  have initial := InternedValueMassHeap.initial unionSource union_facts
  have current : Stored unionBound unionSource := initial.mono (by omega)
  have inputs := SourceRecursiveIntersectionCompileMassInputs.union memberCall unionEntry members level free
    unionMachine unionMachine members initial known current (show initialBound unionSource ≤ unionBound by omega) trace available
  have result := SourceRecursiveIntersectionWorkMass.run_bound current inputs
  exact ⟨union_constructed, union_shape, by cbv, trace, inputs, inputs.physical, by cbv,
    result.1, result.2.1, result.2.2⟩

#print axioms constructed_row_inputs
#check @constructed_row_inputs
#print axioms constructed_union_inputs
#check @constructed_union_inputs
end MicroCFTA.CompileInputsIndependent
