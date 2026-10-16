import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain
import MicroCFTA.SourceCurrentAllocatedNativeScopeCache

/-!
# Conditional finite ordinary structure in current native result cells

Each returned cell relates its result to its own stored operands. Requests
with a nonempty seen list or operands outside the finite ordinary domain
impose no result condition. Publication
and demand create no returned result. A finish needs a separately proved
certificate for the exact evaluating owner. This module does not derive
that producer certificate or transfer a historical execution.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceCurrentAllocatedNativeContextCache (Returned)
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "NodeDomain" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "EdgeDomain" => SourceCurrentAllocatedFiniteOrdinaryDomain.Edge
variable {width : Nat} {Symbol Guard : Type}

/-- Empty-seen finite ordinary inputs require a result no taller than either operand. -/
def NodeCertificate (request : NodeRequest Symbol Guard) (result : Value Symbol Guard) : Prop :=
  request.domain.key.seen = [] → NodeDomain request.left → NodeDomain request.right → NodeDomain result ∧
    MergedOrdinaryHeight.height result ≤ MergedOrdinaryHeight.height request.left ∧
    MergedOrdinaryHeight.height result ≤ MergedOrdinaryHeight.height request.right

/-- Empty-seen finite ordinary rows require a result bounded by each original row. -/
def EdgeCertificate (request : EdgeRequest Symbol Guard) (result : EdgeValue Symbol Guard) : Prop :=
  request.domain.key.seen = [] → EdgeDomain request.left → EdgeDomain request.right → EdgeDomain result ∧
    MergedOrdinaryHeight.edgeHeight result ≤ MergedOrdinaryHeight.edgeHeight request.left ∧
    MergedOrdinaryHeight.edgeHeight result ≤ MergedOrdinaryHeight.edgeHeight request.right

/-- Only returned native cells require conditional structural certificates. -/
structure Stored (state : Native width Symbol Guard) : Prop where
  nodes : Returned NodeCertificate state.nodes
  edges : Returned EdgeCertificate state.edges

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
    (certificate : law request result) : Returned law (FlatMemoThunk.finish handle result state) := by
  intro other original value stored
  by_cases same : other = handle
  · subst other
    have equal : request = original ∧ result = value := by
      simpa [FlatMemoThunk.finish, running, FlatMemoThunk.setStatus, Cache.put] using stored
    rcases equal with ⟨rfl, rfl⟩
    exact certificate
  · exact valid other original value (by
      simpa only [FlatMemoThunk.finish, running, FlatMemoThunk.setStatus, Cache.put, ite_eq_right same] using stored)

/-- Empty native tables need no completed result assumption. -/
theorem initial_stored (width : Nat) (machine : Machine Symbol Guard) : Stored (initial width machine) :=
  ⟨returned_empty _, returned_empty _⟩

/-- Physical machine changes retain the same stored structural certificates. -/
theorem advance_stored (state : Native width Symbol Guard) (after : Machine Symbol Guard)
    (stored : Stored state) : Stored (advance state after) := ⟨stored.nodes, stored.edges⟩

/-- Node publication creates only a suspended request and retains completed certificates. -/
theorem lookupNode_stored (state : Native width Symbol Guard) (request : NodeRequest Symbol Guard)
    (stored : Stored state) : Stored (lookupNode width request state).2 := by
  cases key : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right with
  | none => simpa only [lookupNode, key] using stored
  | some keyValue =>
      simp only [lookupNode, key]
      exact ⟨returned_lookup _ keyValue request state.nodes stored.nodes, stored.edges⟩

/-- Edge publication retains completed certificates in both families. -/
theorem lookupEdge_stored (state : Native width Symbol Guard) (request : EdgeRequest Symbol Guard)
    (stored : Stored state) : Stored (lookupEdge width request state).2 :=
  ⟨stored.nodes, returned_lookup _ _ request state.edges stored.edges⟩

/-- Node demand cannot add a returned result. -/
theorem demandNode_stored (state : Native width Symbol Guard) (handle : Nat)
    (stored : Stored state) : Stored (demandNode handle state).2 :=
  ⟨returned_demand _ handle state.nodes stored.nodes, stored.edges⟩

/-- Edge demand cannot add a returned result. -/
theorem demandEdge_stored (state : Native width Symbol Guard) (handle : Nat)
    (stored : Stored state) : Stored (demandEdge handle state).2 :=
  ⟨stored.nodes, returned_demand _ handle state.edges stored.edges⟩

/-- Node finish stores a local certificate at its literal evaluating owner. -/
theorem finishNode_stored (state : Native width Symbol Guard) (handle : Nat)
    (request : NodeRequest Symbol Guard) (result : Value Symbol Guard) (stored : Stored state)
    (running : state.nodes.cells handle = some ⟨request, .evaluating⟩)
    (certificate : NodeCertificate request result) : Stored (finishNode handle result state) :=
  ⟨returned_finish _ handle request result state.nodes stored.nodes running certificate, stored.edges⟩

/-- Edge finish stores a local certificate at its literal evaluating owner. -/
theorem finishEdge_stored (state : Native width Symbol Guard) (handle : Nat)
    (request : EdgeRequest Symbol Guard) (result : EdgeValue Symbol Guard) (stored : Stored state)
    (running : state.edges.cells handle = some ⟨request, .evaluating⟩)
    (certificate : EdgeCertificate request result) : Stored (finishEdge handle result state) :=
  ⟨stored.nodes, returned_finish _ handle request result state.edges stored.edges running certificate⟩

/-- A physical warm node hit identifies the request before reading its conditional certificate. -/
theorem node_observed_ready (request : NodeRequest Symbol Guard)
    (before chosen after : Native width Symbol Guard) (handle : Nat) (result : Value Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before) (stored : Stored before)
    (ready : NodeReady before.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (selected : lookupNode width request before = (.memoized handle, chosen))
    (demanded : demandNode handle chosen = (.ready result, after)) :
    NodeCertificate request result ∧ Stored after ∧ after = chosen ∧ Available after.machine.heap result := by
  have receipt := SourceCurrentAllocatedNativePhysicalCache.node_ready request before chosen after handle result
    physical ready safe selected demanded
  have chosenStored := lookupNode_stored before request stored
  simp only [selected] at chosenStored
  exact ⟨chosenStored.nodes handle request result receipt.1, receipt.2.1 ▸ chosenStored, receipt.2⟩

/-- A physical warm edge hit identifies the original complete rows before reading its certificate. -/
theorem edge_observed_ready (request : EdgeRequest Symbol Guard)
    (before chosen after : Native width Symbol Guard) (handle : Nat) (result : EdgeValue Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before) (stored : Stored before)
    (ready : EdgeReady before.machine request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right)
    (selected : lookupEdge width request before = (handle, chosen))
    (demanded : demandEdge handle chosen = (.ready result, after)) :
    EdgeCertificate request result ∧ Stored after ∧ after = chosen ∧ EdgeResident after.machine.heap result := by
  have receipt := SourceCurrentAllocatedNativePhysicalCache.edge_ready request before chosen after handle result
    physical ready safe selected demanded
  have chosenStored := lookupEdge_stored before request stored
  simp only [selected] at chosenStored
  exact ⟨chosenStored.edges handle request result receipt.1, receipt.2.1 ▸ chosenStored, receipt.2⟩

/-- Node start records the exact requested owner and retains earlier completed certificates. -/
theorem node_started (request actual : NodeRequest Symbol Guard)
    (before chosen running : Native width Symbol Guard) (handle : Nat)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before) (stored : Stored before)
    (ready : NodeReady before.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (selected : lookupNode width request before = (.memoized handle, chosen))
    (demanded : demandNode handle chosen = (.evaluate actual, running)) :
    actual = request ∧ Stored running ∧ running.nodes.cells handle = some ⟨request, .evaluating⟩ := by
  have same := SourceCurrentAllocatedNativePhysicalCache.node_started request actual before chosen running handle
    physical ready safe selected demanded
  have chosenStored := lookupNode_stored before request stored
  simp only [selected] at chosenStored
  have runningStored := demandNode_stored chosen handle chosenStored
  simp only [demanded] at runningStored
  have cell := (SourceRecursiveIntersectionNative.demandNode_evaluate handle chosen running actual demanded).2
  exact ⟨same, runningStored, same ▸ cell⟩

/-- Edge start records the exact requested owner and retains earlier completed certificates. -/
theorem edge_started (request actual : EdgeRequest Symbol Guard)
    (before chosen running : Native width Symbol Guard) (handle : Nat)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before) (stored : Stored before)
    (ready : EdgeReady before.machine request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right)
    (selected : lookupEdge width request before = (handle, chosen))
    (demanded : demandEdge handle chosen = (.evaluate actual, running)) :
    actual = request ∧ Stored running ∧ running.edges.cells handle = some ⟨request, .evaluating⟩ := by
  have same := SourceCurrentAllocatedNativePhysicalCache.edge_started request actual before chosen running handle
    physical ready safe selected demanded
  have chosenStored := lookupEdge_stored before request stored
  simp only [selected] at chosenStored
  have runningStored := demandEdge_stored chosen handle chosenStored
  simp only [demanded] at runningStored
  have cell := (SourceRecursiveIntersectionNative.demandEdge_evaluate handle chosen running actual demanded).2
  exact ⟨same, runningStored, same ▸ cell⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStored
