import MicroCFTA.SourceCurrentAllocatedNativeContextCache
import MicroCFTA.SourceCurrentAllocatedNativePhysicalCache
import MicroCFTA.SourceCurrentConstrainedCapCheckedJointCode

/-!
# Joint structural laws in actual checked native memo cells

Each returned cell retains cap, occurrence, and scope laws for its complete
captured request. Lookup and demand do not create a returned law. A finish
installs only the law proved for its actual evaluating owner. Physical key
validity identifies the complete request at a warm hit.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapCheckedJointCache
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceCurrentAllocatedNativeContextCache (Returned)
local notation "Native" => SourceRecursiveIntersectionThunks.State
variable {width : Nat} {Symbol Guard : Type}

open SourceCurrentConstrainedCapCheckedJointCode (NodeLaw EdgeLaw)

/-- Returned cells carry conditional joint laws for their exact original requests. -/
structure Stored (annotation : Guard → Prop) (source : InternedConstructorTemplates.State Symbol Guard)
    (state : Native width Symbol Guard) : Prop where
  /-- Each returned node retains cap, occurrence, and scope laws for its original operands. -/
  nodes : Returned (NodeLaw annotation source) state.nodes
  /-- Each returned row retains cap, child occurrence, and scope laws. -/
  edges : Returned (EdgeLaw annotation source) state.edges

variable (annotation : Guard → Prop) (source : InternedConstructorTemplates.State Symbol Guard)

private theorem returned_empty (law : Request → Answer → Prop) :
    Returned law (FlatMemoThunk.empty : FlatMemoThunk.State Key Request Answer) := by
  intro handle request result found
  cases found

private theorem returned_lookup [DecidableEq Key] (law : Request → Answer → Prop)
    (key : Key) (request : Request) (state : FlatMemoThunk.State Key Request Answer)
    (valid : Returned law state) : Returned law (FlatMemoThunk.lookupOrInsert key request state).2 := by
  cases found : state.table key with
  | some handle => simpa only [FlatMemoThunk.lookupOrInsert, found] using valid
  | none =>
      intro handle original result stored
      by_cases same : handle = state.next
      · subst handle
        simp [FlatMemoThunk.lookupOrInsert, found, Cache.put] at stored
      · exact valid handle original result (by
          simpa only [FlatMemoThunk.lookupOrInsert, found, Cache.put, ite_eq_right same] using stored)

private theorem returned_evaluating (law : Request → Answer → Prop) (handle : Nat)
    (state : FlatMemoThunk.State Key Request Answer) (valid : Returned law state) :
    Returned law (FlatMemoThunk.setStatus handle .evaluating state) := by
  cases found : state.cells handle with
  | none => simpa only [FlatMemoThunk.setStatus, found] using valid
  | some cell =>
      intro other request result stored
      by_cases same : other = handle
      · subst other
        simp [FlatMemoThunk.setStatus, found, Cache.put] at stored
      · exact valid other request result (by
          simpa only [FlatMemoThunk.setStatus, found, Cache.put, ite_eq_right same] using stored)

private theorem returned_demand (law : Request → Answer → Prop) (handle : Nat)
    (state : FlatMemoThunk.State Key Request Answer) (valid : Returned law state) :
    Returned law (FlatMemoThunk.demand handle state).2 := by
  cases found : state.cells handle with
  | none => simpa only [FlatMemoThunk.demand, found] using valid
  | some cell =>
      cases cell with
      | mk request status =>
          cases status with
          | suspended => simpa only [FlatMemoThunk.demand, found] using returned_evaluating law handle state valid
          | evaluating | returned result => simpa only [FlatMemoThunk.demand, found] using valid

private theorem returned_finish (law : Request → Answer → Prop) (handle : Nat)
    (request : Request) (result : Answer) (state : FlatMemoThunk.State Key Request Answer)
    (valid : Returned law state) (running : state.cells handle = some ⟨request, .evaluating⟩)
    (localLaw : law request result) : Returned law (FlatMemoThunk.finish handle result state) := by
  intro other original value stored
  by_cases same : other = handle
  · subst other
    have equal : request = original ∧ result = value := by
      simpa [FlatMemoThunk.finish, running, FlatMemoThunk.setStatus, Cache.put] using stored
    rcases equal with ⟨rfl, rfl⟩
    exact localLaw
  · exact valid other original value (by
      simpa only [FlatMemoThunk.finish, running, FlatMemoThunk.setStatus, Cache.put, ite_eq_right same] using stored)

/-- Empty tables satisfy joint laws without a supplied completed result. -/
theorem initial_stored (width : Nat) (machine : Machine Symbol Guard) : Stored annotation source (initial width machine) :=
  ⟨returned_empty _, returned_empty _⟩

/-- Machine changes retain the joint laws of unchanged completed cells. -/
theorem advance_stored (state : Native width Symbol Guard) (after : Machine Symbol Guard)
    (annotations : Stored annotation source state) : Stored annotation source (advance state after) := ⟨annotations.nodes, annotations.edges⟩

/-- Node lookup retains completed joint laws and creates no returned result. -/
theorem lookupNode_stored (state : Native width Symbol Guard) (request : NodeRequest Symbol Guard)
    (annotations : Stored annotation source state) : Stored annotation source (lookupNode width request state).2 := by
  cases key : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right with
  | none => simpa only [lookupNode, key] using annotations
  | some keyValue =>
      simp only [lookupNode, key]
      exact ⟨returned_lookup _ keyValue request state.nodes annotations.nodes, annotations.edges⟩

/-- Edge lookup retains all previously completed joint laws. -/
theorem lookupEdge_stored (state : Native width Symbol Guard) (request : EdgeRequest Symbol Guard)
    (annotations : Stored annotation source state) : Stored annotation source (lookupEdge width request state).2 :=
  ⟨annotations.nodes, returned_lookup _ _ request state.edges annotations.edges⟩

/-- Node demand retains the joint law of every completed cell. -/
theorem demandNode_stored (state : Native width Symbol Guard) (handle : Nat)
    (annotations : Stored annotation source state) : Stored annotation source (demandNode handle state).2 :=
  ⟨returned_demand _ handle state.nodes annotations.nodes, annotations.edges⟩

/-- Edge demand retains the joint law of every completed cell. -/
theorem demandEdge_stored (state : Native width Symbol Guard) (handle : Nat)
    (annotations : Stored annotation source state) : Stored annotation source (demandEdge handle state).2 :=
  ⟨annotations.nodes, returned_demand _ handle state.edges annotations.edges⟩

/-- A node finish stores a joint law for its exact evaluating request. -/
theorem finishNode_stored (state : Native width Symbol Guard) (handle : Nat)
    (request : NodeRequest Symbol Guard) (result : Value Symbol Guard) (annotations : Stored annotation source state)
    (running : state.nodes.cells handle = some ⟨request, .evaluating⟩) (localLaw : NodeLaw annotation source request result) :
    Stored annotation source (finishNode handle result state) :=
  ⟨returned_finish _ handle request result state.nodes annotations.nodes running localLaw, annotations.edges⟩

/-- An edge finish stores a joint law for its exact evaluating request. -/
theorem finishEdge_stored (state : Native width Symbol Guard) (handle : Nat)
    (request : EdgeRequest Symbol Guard) (result : EdgeValue Symbol Guard) (annotations : Stored annotation source state)
    (running : state.edges.cells handle = some ⟨request, .evaluating⟩) (localLaw : EdgeLaw annotation source request result) :
    Stored annotation source (finishEdge handle result state) :=
  ⟨annotations.nodes, returned_finish _ handle request result state.edges annotations.edges running localLaw⟩

/-- A warm node hit recovers the exact requested joint law and an available result. -/
theorem node_observed_ready (request : NodeRequest Symbol Guard)
    (before chosen after : Native width Symbol Guard) (handle : Nat) (result : Value Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before) (annotations : Stored annotation source before)
    (ready : NodeReady before.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (selected : lookupNode width request before = (.memoized handle, chosen))
    (demanded : demandNode handle chosen = (.ready result, after)) :
    NodeLaw annotation source request result ∧ Stored annotation source after ∧ after = chosen ∧ Available after.machine.heap result := by
  have receipt := SourceCurrentAllocatedNativePhysicalCache.node_ready request before chosen after handle result
    physical ready safe selected demanded
  have chosenAnnotations := lookupNode_stored annotation source before request annotations
  simp only [selected] at chosenAnnotations
  exact ⟨chosenAnnotations.nodes handle request result receipt.1, receipt.2.1 ▸ chosenAnnotations, receipt.2⟩

/-- A warm edge hit recovers the exact requested joint row law and a resident row. -/
theorem edge_observed_ready (request : EdgeRequest Symbol Guard)
    (before chosen after : Native width Symbol Guard) (handle : Nat) (result : EdgeValue Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before) (annotations : Stored annotation source before)
    (ready : EdgeReady before.machine request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right)
    (selected : lookupEdge width request before = (handle, chosen))
    (demanded : demandEdge handle chosen = (.ready result, after)) :
    EdgeLaw annotation source request result ∧ Stored annotation source after ∧ after = chosen ∧ EdgeResident after.machine.heap result := by
  have receipt := SourceCurrentAllocatedNativePhysicalCache.edge_ready request before chosen after handle result
    physical ready safe selected demanded
  have chosenAnnotations := lookupEdge_stored annotation source before request annotations
  simp only [selected] at chosenAnnotations
  exact ⟨chosenAnnotations.edges handle request result receipt.1, receipt.2.1 ▸ chosenAnnotations, receipt.2⟩

/-- A node start preserves joint laws and records the exact requested evaluating cell. -/
theorem node_started (request actual : NodeRequest Symbol Guard)
    (before chosen running : Native width Symbol Guard) (handle : Nat)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before) (annotations : Stored annotation source before)
    (ready : NodeReady before.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (selected : lookupNode width request before = (.memoized handle, chosen))
    (demanded : demandNode handle chosen = (.evaluate actual, running)) :
    actual = request ∧ SourceCurrentAllocatedNativePhysicalCache.Valid running ∧ Stored annotation source running ∧
      running.nodes.cells handle = some ⟨request, .evaluating⟩ := by
  have same := SourceCurrentAllocatedNativePhysicalCache.node_started request actual before chosen running handle
    physical ready safe selected demanded
  have chosenPhysical := SourceCurrentAllocatedNativePhysicalCache.lookupNode_valid before physical request ready safe
  have chosenAnnotations := lookupNode_stored annotation source before request annotations
  simp only [selected] at chosenPhysical chosenAnnotations
  have runningPhysical := SourceCurrentAllocatedNativePhysicalCache.demandNode_valid chosen chosenPhysical handle
  have runningAnnotations := demandNode_stored annotation source chosen handle chosenAnnotations
  simp only [demanded] at runningPhysical runningAnnotations
  have cell := (SourceRecursiveIntersectionNative.demandNode_evaluate handle chosen running actual demanded).2
  exact ⟨same, runningPhysical, runningAnnotations, same ▸ cell⟩

/-- An edge start preserves joint laws and records the exact requested evaluating cell. -/
theorem edge_started (request actual : EdgeRequest Symbol Guard)
    (before chosen running : Native width Symbol Guard) (handle : Nat)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before) (annotations : Stored annotation source before)
    (ready : EdgeReady before.machine request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right)
    (selected : lookupEdge width request before = (handle, chosen))
    (demanded : demandEdge handle chosen = (.evaluate actual, running)) :
    actual = request ∧ SourceCurrentAllocatedNativePhysicalCache.Valid running ∧ Stored annotation source running ∧
      running.edges.cells handle = some ⟨request, .evaluating⟩ := by
  have same := SourceCurrentAllocatedNativePhysicalCache.edge_started request actual before chosen running handle
    physical ready safe selected demanded
  have chosenPhysical := SourceCurrentAllocatedNativePhysicalCache.lookupEdge_valid before physical request ready safe
  have chosenAnnotations := lookupEdge_stored annotation source before request annotations
  simp only [selected] at chosenPhysical chosenAnnotations
  have runningPhysical := SourceCurrentAllocatedNativePhysicalCache.demandEdge_valid chosen chosenPhysical handle
  have runningAnnotations := demandEdge_stored annotation source chosen handle chosenAnnotations
  simp only [demanded] at runningPhysical runningAnnotations
  have cell := (SourceRecursiveIntersectionNative.demandEdge_evaluate handle chosen running actual demanded).2
  exact ⟨same, runningPhysical, runningAnnotations, same ▸ cell⟩

end MicroCFTA.SourceCurrentConstrainedCapCheckedJointCache
