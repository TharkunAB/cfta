import MicroCFTA.SourceCurrentConstrainedCapCheckedJointCache

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 1000000

namespace MicroCFTA.CheckedJointCacheKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
local notation "Joint" => SourceCurrentConstrainedCapCheckedJointCache.Stored
local notation "NodeLaw" => SourceCurrentConstrainedCapCheckedJointCode.NodeLaw
local notation "EdgeLaw" => SourceCurrentConstrainedCapCheckedJointCode.EdgeLaw
variable {width : Nat} {Symbol Guard : Type}

/-- A started owner receives its derived law before an exact whole-state warm demand. -/
theorem node_finish_warm (annotation : Guard → Prop) (source : State Symbol Guard)
    (before chosen running : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (request actual : NodeRequest Symbol Guard) (handle : Nat) (value : Value Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before) (stored : Joint annotation source before)
    (ready : NodeReady before.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (selected : lookupNode width request before = (.memoized handle, chosen))
    (started : demandNode handle chosen = (.evaluate actual, running))
    (available : Available running.machine.heap value) (derived : NodeLaw annotation source actual value) :
    actual = request ∧
      SourceCurrentAllocatedNativePhysicalCache.Valid (finishNode handle value running) ∧
      Joint annotation source (finishNode handle value running) ∧
      demandNode handle (finishNode handle value running) = (.ready value, finishNode handle value running) ∧
      NodeLaw annotation source request value := by
  obtain ⟨same, runningPhysical, runningStored, owner⟩ :=
    SourceCurrentConstrainedCapCheckedJointCache.node_started annotation source request actual before chosen running handle
      physical stored ready safe selected started
  subst actual
  have finishedStored := SourceCurrentConstrainedCapCheckedJointCache.finishNode_stored annotation source running handle
    request value runningStored owner derived
  have finishedPhysical := SourceCurrentAllocatedNativePhysicalCache.finishNode_valid running runningPhysical handle
    request value owner available
  have cell : (finishNode handle value running).nodes.cells handle = some ⟨request, .returned value⟩ := by
    simp [finishNode, FlatMemoThunk.finish, owner, FlatMemoThunk.setStatus, Cache.put]
  have hit := FlatMemoThunk.demand_ready handle (finishNode handle value running).nodes request value cell
  have warm : demandNode handle (finishNode handle value running) = (.ready value, finishNode handle value running) := by
    simp only [demandNode, hit]
  exact ⟨rfl, finishedPhysical, finishedStored, warm, finishedStored.nodes handle request value cell⟩

/-- The separate row owner retains its complete joint law and exact whole-state warm demand. -/
theorem edge_finish_warm (annotation : Guard → Prop) (source : State Symbol Guard)
    (before chosen running : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (request actual : EdgeRequest Symbol Guard) (handle : Nat) (value : EdgeValue Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before) (stored : Joint annotation source before)
    (ready : EdgeReady before.machine request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right)
    (selected : lookupEdge width request before = (handle, chosen))
    (started : demandEdge handle chosen = (.evaluate actual, running))
    (resident : EdgeResident running.machine.heap value) (derived : EdgeLaw annotation source actual value) :
    actual = request ∧
      SourceCurrentAllocatedNativePhysicalCache.Valid (finishEdge handle value running) ∧
      Joint annotation source (finishEdge handle value running) ∧
      demandEdge handle (finishEdge handle value running) = (.ready value, finishEdge handle value running) ∧
      EdgeLaw annotation source request value := by
  obtain ⟨same, runningPhysical, runningStored, owner⟩ :=
    SourceCurrentConstrainedCapCheckedJointCache.edge_started annotation source request actual before chosen running handle
      physical stored ready safe selected started
  subst actual
  have finishedStored := SourceCurrentConstrainedCapCheckedJointCache.finishEdge_stored annotation source running handle
    request value runningStored owner derived
  have finishedPhysical := SourceCurrentAllocatedNativePhysicalCache.finishEdge_valid running runningPhysical handle
    request value owner resident
  have cell : (finishEdge handle value running).edges.cells handle = some ⟨request, .returned value⟩ := by
    simp [finishEdge, FlatMemoThunk.finish, owner, FlatMemoThunk.setStatus, Cache.put]
  have hit := FlatMemoThunk.demand_ready handle (finishEdge handle value running).edges request value cell
  have warm : demandEdge handle (finishEdge handle value running) = (.ready value, finishEdge handle value running) := by
    simp only [demandEdge, hit]
  exact ⟨rfl, finishedPhysical, finishedStored, warm, finishedStored.edges handle request value cell⟩

#print axioms node_finish_warm
#check @node_finish_warm
#print axioms edge_finish_warm
#check @edge_finish_warm
end MicroCFTA.CheckedJointCacheKernels
