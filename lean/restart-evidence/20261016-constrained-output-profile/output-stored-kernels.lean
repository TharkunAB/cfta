import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputStored

namespace MicroCFTA.OutputStoredKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceCurrentAllocatedFiniteOrdinaryOutputStored
local notation "NodeShape" => SourceCurrentAllocatedFiniteOrdinaryNativeProfile.NodeShape
local notation "EdgeShape" => SourceCurrentAllocatedFiniteOrdinaryNativeProfile.EdgeShape
local notation "Native" => SourceRecursiveIntersectionThunks.State
variable {Symbol Guard : Type} {width : Nat}

/-- A started request can publish Empty and immediately demand the same stored result. -/
theorem publish_empty (request owner : NodeRequest Symbol Guard)
    (before chosen running : Native width Symbol Guard) (handle : Nat)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before) (stored : Stored before)
    (ready : NodeReady before.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (selected : lookupNode width request before = (.memoized handle, chosen))
    (demanded : demandNode handle chosen = (.evaluate owner, running)) :
    let final := finishNode handle .empty running
    owner = request ∧ Stored final ∧ final.edges = running.edges ∧
      final.nodes.cells handle = some ⟨request, .returned .empty⟩ ∧
      demandNode handle final = (.ready .empty, final) := by
  obtain ⟨same, current, cell⟩ := node_started request owner before chosen running handle physical stored ready safe selected demanded
  have certificate : NodeCertificate request .empty := by
    intro _ _ _ _ _
    trivial
  have saved := finishNode_stored running handle request .empty current cell certificate
  have returned : (finishNode handle (.empty : Value Symbol Guard) running).nodes.cells handle =
      some ⟨request, .returned .empty⟩ := by
    simp [finishNode, FlatMemoThunk.finish, cell, FlatMemoThunk.setStatus, put]
  exact ⟨same, saved, rfl, returned, by simp only [demandNode, FlatMemoThunk.demand, returned]⟩

/-- Serial finishes retain the first family's output profile in the second family's state. -/
theorem serial_families (before : Native width Symbol Guard) (stored : Stored before)
    (nodeHandle edgeHandle : Nat) (nodeRequest : NodeRequest Symbol Guard) (edgeRequest : EdgeRequest Symbol Guard)
    (entry : Interned (EdgeKey Symbol Guard))
    (nodeRunning : before.nodes.cells nodeHandle = some ⟨nodeRequest, .evaluating⟩)
    (edgeRunning : before.edges.cells edgeHandle = some ⟨edgeRequest, .evaluating⟩) :
    let middle := finishNode nodeHandle (.empty : Value Symbol Guard) before
    let result : EdgeValue Symbol Guard := .mk entry [.empty]
    let final := finishEdge edgeHandle result middle
    Stored final ∧ NodeCertificate nodeRequest .empty ∧ EdgeCertificate edgeRequest result ∧
      final.nodes.cells nodeHandle = some ⟨nodeRequest, .returned .empty⟩ ∧
      final.edges.cells edgeHandle = some ⟨edgeRequest, .returned result⟩ := by
  have nodeLaw : NodeCertificate nodeRequest .empty := by intro _ _ _ _ _; trivial
  have edgeLaw : EdgeCertificate edgeRequest (.mk entry [.empty]) := by
    intro _ rows arity _ _
    exact ⟨by simp; omega, by trivial⟩
  have middleStored := finishNode_stored before nodeHandle nodeRequest .empty stored nodeRunning nodeLaw
  have middleRunning : (finishNode nodeHandle (.empty : Value Symbol Guard) before).edges.cells edgeHandle =
      some ⟨edgeRequest, .evaluating⟩ := edgeRunning
  have finalStored := finishEdge_stored _ edgeHandle edgeRequest (.mk entry [.empty]) middleStored middleRunning edgeLaw
  refine ⟨finalStored, nodeLaw, edgeLaw, ?_, ?_⟩
  · simp [finishEdge, finishNode, FlatMemoThunk.finish, nodeRunning, FlatMemoThunk.setStatus, put]
  · simp [finishEdge, FlatMemoThunk.finish, middleRunning, FlatMemoThunk.setStatus, put]

/-- A warm node hit supplies the requested uniform profile and the actual available result. -/
theorem warm_node (request : NodeRequest Symbol Guard) (before chosen after : Native width Symbol Guard)
    (handle : Nat) (result : Value Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before) (stored : Stored before)
    (ready : NodeReady before.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (selected : lookupNode width request before = (.memoized handle, chosen))
    (demanded : demandNode handle chosen = (.ready result, after))
    (seen : request.domain.key.seen = []) (rows arity : Nat)
    (left : NodeShape rows arity request.left) (right : NodeShape rows arity request.right) :
    NodeShape (rows * rows) (max arity 1) result ∧ Stored after ∧
      after = chosen ∧ Available after.machine.heap result := by
  have hit := node_observed_ready request before chosen after handle result physical stored ready safe selected demanded
  exact ⟨hit.1 seen rows arity left right, hit.2⟩

/-- A warm edge hit keeps the sentinel-safe profile and the exact resident row. -/
theorem warm_edge (request : EdgeRequest Symbol Guard) (before chosen after : Native width Symbol Guard)
    (handle : Nat) (result : EdgeValue Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before) (stored : Stored before)
    (ready : EdgeReady before.machine request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right)
    (selected : lookupEdge width request before = (handle, chosen))
    (demanded : demandEdge handle chosen = (.ready result, after))
    (seen : request.domain.key.seen = []) (rows arity : Nat)
    (left : EdgeShape rows arity request.left) (right : EdgeShape rows arity request.right) :
    EdgeShape (rows * rows) (max arity 1) result ∧ Stored after ∧
      after = chosen ∧ EdgeResident after.machine.heap result := by
  have hit := edge_observed_ready request before chosen after handle result physical stored ready safe selected demanded
  exact ⟨hit.1 seen rows arity left right, hit.2⟩

/-- Nonempty seen domains impose no result profile condition. -/
theorem nonempty_seen (request : NodeRequest Symbol Guard) (result : Value Symbol Guard)
    (seen : request.domain.key.seen ≠ []) : NodeCertificate request result := by
  intro clear
  exact False.elim (seen clear)

end MicroCFTA.OutputStoredKernels

#check @MicroCFTA.OutputStoredKernels.publish_empty
#print axioms MicroCFTA.OutputStoredKernels.publish_empty
#check @MicroCFTA.OutputStoredKernels.serial_families
#print axioms MicroCFTA.OutputStoredKernels.serial_families
#check @MicroCFTA.OutputStoredKernels.warm_node
#print axioms MicroCFTA.OutputStoredKernels.warm_node
#check @MicroCFTA.OutputStoredKernels.warm_edge
#print axioms MicroCFTA.OutputStoredKernels.warm_edge
#check @MicroCFTA.OutputStoredKernels.nonempty_seen
#print axioms MicroCFTA.OutputStoredKernels.nonempty_seen
