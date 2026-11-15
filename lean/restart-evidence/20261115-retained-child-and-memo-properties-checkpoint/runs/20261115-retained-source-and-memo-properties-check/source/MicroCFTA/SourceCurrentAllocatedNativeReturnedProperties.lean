import MicroCFTA.SourceCurrentAllocatedNativeContextCache
import MicroCFTA.SourceCurrentAllocatedNativePhysicalCache

/-!
# Conditional properties at actual native memo returns

The existing Returned predicate records a property of each returned payload.
Exact physical hits recover that property for the original request.
A finish stores the property of the same literal producer result.
These laws do not prove that producer bodies satisfy a particular property.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeReturnedProperties
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceCurrentAllocatedNativeContextCache (Returned)
local notation "Native" => SourceRecursiveIntersectionThunks.State
variable {width : Nat} {Symbol Guard : Type}

set_option autoImplicit false

/-- A ready node hit returns its exact stored payload and conditional property. -/
theorem node_ready_property
    (law : NodeRequest Symbol Guard → Value Symbol Guard → Prop)
    (state : Native width Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid state)
    (returned : Returned law state.nodes)
    (request original : NodeRequest Symbol Guard) (ready : NodeReady state.machine request)
    (key : IntersectionFlatMemoKeyDomain.Triple width) (checked : NodeKey width request key)
    (handle : Nat) (published : state.nodes.table key = some handle) (value : Value Symbol Guard)
    (stored : state.nodes.cells handle = some ⟨original, .returned value⟩) :
    original = request ∧ lookupNode width request state = (.memoized handle, state) ∧
      demandNode handle state = (.ready value, state) ∧ Available state.machine.heap value ∧
      law request value := by
  obtain ⟨same, selected, demanded, available⟩ :=
    SourceCurrentAllocatedNativePhysicalCache.node_ready_receipt state physical request original
      ready key checked handle published value stored
  have localLaw := returned handle original value stored
  rw [same] at localLaw
  exact ⟨same, selected, demanded, available, localLaw⟩

/-- A ready edge hit returns its exact stored row and conditional property. -/
theorem edge_ready_property
    (law : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop)
    (state : Native width Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid state)
    (returned : Returned law state.edges)
    (request original : EdgeRequest Symbol Guard) (ready : EdgeReady state.machine request)
    (key : IntersectionFlatMemoKeyDomain.Triple width) (checked : EdgeKeyOf width request key)
    (handle : Nat) (published : state.edges.table key = some handle) (value : EdgeValue Symbol Guard)
    (stored : state.edges.cells handle = some ⟨original, .returned value⟩) :
    original = request ∧ lookupEdge width request state = (handle, state) ∧
      demandEdge handle state = (.ready value, state) ∧ EdgeResident state.machine.heap value ∧
      law request value := by
  obtain ⟨same, selected, demanded, resident⟩ :=
    SourceCurrentAllocatedNativePhysicalCache.edge_ready_receipt state physical request original
      ready key checked handle published value stored
  have localLaw := returned handle original value stored
  rw [same] at localLaw
  exact ⟨same, selected, demanded, resident, localLaw⟩

/-- A node finish retains prior properties and stores the same actual producer payload. -/
theorem finishNode_property
    (law : NodeRequest Symbol Guard → Value Symbol Guard → Prop)
    (state : Native width Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid state)
    (returned : Returned law state.nodes)
    (handle : Nat) (request : NodeRequest Symbol Guard) (value : Value Symbol Guard)
    (running : state.nodes.cells handle = some ⟨request, .evaluating⟩)
    (available : Available state.machine.heap value) (localLaw : law request value) :
    SourceCurrentAllocatedNativePhysicalCache.Valid (finishNode handle value state) ∧
      Returned law (finishNode handle value state).nodes ∧
      (finishNode handle value state).nodes.cells handle = some ⟨request, .returned value⟩ ∧
      (finishNode handle value state).machine = state.machine ∧
      (finishNode handle value state).edges = state.edges := by
  have physicalAfter := SourceCurrentAllocatedNativePhysicalCache.finishNode_valid
    state physical handle request value running available
  have returnedAfter := SourceCurrentAllocatedNativeContextCache.returned_finish
    law handle request value state.nodes returned running localLaw
  have exactCell := FlatMemoThunk.setStatus_cell handle (.returned value)
    state.nodes ⟨request, .evaluating⟩ running
  refine ⟨physicalAfter, returnedAfter, ?_, rfl, rfl⟩
  simpa only [finishNode, FlatMemoThunk.finish, running] using exactCell

/-- An edge finish retains prior properties and stores the same actual producer row. -/
theorem finishEdge_property
    (law : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop)
    (state : Native width Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid state)
    (returned : Returned law state.edges)
    (handle : Nat) (request : EdgeRequest Symbol Guard) (value : EdgeValue Symbol Guard)
    (running : state.edges.cells handle = some ⟨request, .evaluating⟩)
    (resident : EdgeResident state.machine.heap value) (localLaw : law request value) :
    SourceCurrentAllocatedNativePhysicalCache.Valid (finishEdge handle value state) ∧
      Returned law (finishEdge handle value state).edges ∧
      (finishEdge handle value state).edges.cells handle = some ⟨request, .returned value⟩ ∧
      (finishEdge handle value state).machine = state.machine ∧
      (finishEdge handle value state).nodes = state.nodes := by
  have physicalAfter := SourceCurrentAllocatedNativePhysicalCache.finishEdge_valid
    state physical handle request value running resident
  have returnedAfter := SourceCurrentAllocatedNativeContextCache.returned_finish
    law handle request value state.edges returned running localLaw
  have exactCell := FlatMemoThunk.setStatus_cell handle (.returned value)
    state.edges ⟨request, .evaluating⟩ running
  refine ⟨physicalAfter, returnedAfter, ?_, rfl, rfl⟩
  simpa only [finishEdge, FlatMemoThunk.finish, running] using exactCell

end MicroCFTA.SourceCurrentAllocatedNativeReturnedProperties

#print axioms MicroCFTA.SourceCurrentAllocatedNativeReturnedProperties.node_ready_property
#print axioms MicroCFTA.SourceCurrentAllocatedNativeReturnedProperties.edge_ready_property
#print axioms MicroCFTA.SourceCurrentAllocatedNativeReturnedProperties.finishNode_property
#print axioms MicroCFTA.SourceCurrentAllocatedNativeReturnedProperties.finishEdge_property
