import MicroCFTA.SourceCurrentAllocatedNativeContextCache
import MicroCFTA.SourceCurrentAllocatedNativePhysicalCache
import MicroCFTA.SourceRecursiveIntersectionResultScope

/-!
# Syntactic scope of returned checked native cells

Returned values contain only intersection names from their original request.
This invariant does not depend on an input language model. Physical validity
identifies the exact request at a warm hit. A finish needs independently
proved scope for its literal evaluating request.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeScopeCache
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceCurrentAllocatedNativeContextCache (Returned)
local notation "Native" => SourceRecursiveIntersectionThunks.State
variable {width : Nat} {Symbol Guard : Type}

/-- A node result uses only recursive pair names from its incoming domain. -/
def NodeLaw (request : NodeRequest Symbol Guard) (result : Value Symbol Guard) : Prop :=
  SourceRecursiveIntersectionResultScope.Scope request.domain.key.seen result

/-- Every returned edge child uses only the incoming recursive pair names. -/
def EdgeLaw (request : EdgeRequest Symbol Guard) (result : EdgeValue Symbol Guard) : Prop :=
  SourceRecursiveIntersectionResultScope.EdgeScope request.domain.key.seen result

/-- Only returned cells require a syntactic result scope. -/
structure Scoped (state : Native width Symbol Guard) : Prop where
  nodes : Returned NodeLaw state.nodes
  edges : Returned EdgeLaw state.edges

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

/-- Empty tables satisfy scope without a supplied completed result. -/
theorem initial_scoped (width : Nat) (machine : Machine Symbol Guard) : Scoped (initial width machine) :=
  ⟨returned_empty _, returned_empty _⟩

/-- Machine changes retain the scopes of unchanged completed cells. -/
theorem advance_scoped (state : Native width Symbol Guard) (after : Machine Symbol Guard)
    (scopes : Scoped state) : Scoped (advance state after) := ⟨scopes.nodes, scopes.edges⟩

/-- Node lookup retains completed scopes and creates no returned result. -/
theorem lookupNode_scoped (state : Native width Symbol Guard) (request : NodeRequest Symbol Guard)
    (scopes : Scoped state) : Scoped (lookupNode width request state).2 := by
  cases key : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right with
  | none => simpa only [lookupNode, key] using scopes
  | some keyValue =>
      simp only [lookupNode, key]
      exact ⟨returned_lookup _ keyValue request state.nodes scopes.nodes, scopes.edges⟩

/-- Edge lookup retains all previously completed scopes. -/
theorem lookupEdge_scoped (state : Native width Symbol Guard) (request : EdgeRequest Symbol Guard)
    (scopes : Scoped state) : Scoped (lookupEdge width request state).2 :=
  ⟨scopes.nodes, returned_lookup _ _ request state.edges scopes.edges⟩

/-- Node demand retains the scope of every completed cell. -/
theorem demandNode_scoped (state : Native width Symbol Guard) (handle : Nat)
    (scopes : Scoped state) : Scoped (demandNode handle state).2 :=
  ⟨returned_demand _ handle state.nodes scopes.nodes, scopes.edges⟩

/-- Edge demand retains the scope of every completed cell. -/
theorem demandEdge_scoped (state : Native width Symbol Guard) (handle : Nat)
    (scopes : Scoped state) : Scoped (demandEdge handle state).2 :=
  ⟨scopes.nodes, returned_demand _ handle state.edges scopes.edges⟩

/-- A node finish stores scope for its exact evaluating request. -/
theorem finishNode_scoped (state : Native width Symbol Guard) (handle : Nat)
    (request : NodeRequest Symbol Guard) (result : Value Symbol Guard) (scopes : Scoped state)
    (running : state.nodes.cells handle = some ⟨request, .evaluating⟩) (localScope : NodeLaw request result) :
    Scoped (finishNode handle result state) :=
  ⟨returned_finish _ handle request result state.nodes scopes.nodes running localScope, scopes.edges⟩

/-- An edge finish stores scope for its exact evaluating request. -/
theorem finishEdge_scoped (state : Native width Symbol Guard) (handle : Nat)
    (request : EdgeRequest Symbol Guard) (result : EdgeValue Symbol Guard) (scopes : Scoped state)
    (running : state.edges.cells handle = some ⟨request, .evaluating⟩) (localScope : EdgeLaw request result) :
    Scoped (finishEdge handle result state) :=
  ⟨scopes.nodes, returned_finish _ handle request result state.edges scopes.edges running localScope⟩

/-- A warm node hit recovers the exact requested scope and an available result. -/
theorem node_observed_ready (request : NodeRequest Symbol Guard)
    (before chosen after : Native width Symbol Guard) (handle : Nat) (result : Value Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before) (scopes : Scoped before)
    (ready : NodeReady before.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (selected : lookupNode width request before = (.memoized handle, chosen))
    (demanded : demandNode handle chosen = (.ready result, after)) :
    NodeLaw request result ∧ Scoped after ∧ after = chosen ∧ Available after.machine.heap result := by
  have receipt := SourceCurrentAllocatedNativePhysicalCache.node_ready request before chosen after handle result
    physical ready safe selected demanded
  have chosenScope := lookupNode_scoped before request scopes
  simp only [selected] at chosenScope
  exact ⟨chosenScope.nodes handle request result receipt.1, receipt.2.1 ▸ chosenScope, receipt.2⟩

/-- A warm edge hit recovers the exact requested child scopes and a resident row. -/
theorem edge_observed_ready (request : EdgeRequest Symbol Guard)
    (before chosen after : Native width Symbol Guard) (handle : Nat) (result : EdgeValue Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before) (scopes : Scoped before)
    (ready : EdgeReady before.machine request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right)
    (selected : lookupEdge width request before = (handle, chosen))
    (demanded : demandEdge handle chosen = (.ready result, after)) :
    EdgeLaw request result ∧ Scoped after ∧ after = chosen ∧ EdgeResident after.machine.heap result := by
  have receipt := SourceCurrentAllocatedNativePhysicalCache.edge_ready request before chosen after handle result
    physical ready safe selected demanded
  have chosenScope := lookupEdge_scoped before request scopes
  simp only [selected] at chosenScope
  exact ⟨chosenScope.edges handle request result receipt.1, receipt.2.1 ▸ chosenScope, receipt.2⟩

/-- A node start preserves scope and records the exact requested evaluating cell. -/
theorem node_started (request actual : NodeRequest Symbol Guard)
    (before chosen running : Native width Symbol Guard) (handle : Nat)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before) (scopes : Scoped before)
    (ready : NodeReady before.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (selected : lookupNode width request before = (.memoized handle, chosen))
    (demanded : demandNode handle chosen = (.evaluate actual, running)) :
    actual = request ∧ SourceCurrentAllocatedNativePhysicalCache.Valid running ∧ Scoped running ∧
      running.nodes.cells handle = some ⟨request, .evaluating⟩ := by
  have same := SourceCurrentAllocatedNativePhysicalCache.node_started request actual before chosen running handle
    physical ready safe selected demanded
  have chosenPhysical := SourceCurrentAllocatedNativePhysicalCache.lookupNode_valid before physical request ready safe
  have chosenScope := lookupNode_scoped before request scopes
  simp only [selected] at chosenPhysical chosenScope
  have runningPhysical := SourceCurrentAllocatedNativePhysicalCache.demandNode_valid chosen chosenPhysical handle
  have runningScope := demandNode_scoped chosen handle chosenScope
  simp only [demanded] at runningPhysical runningScope
  have cell := (SourceRecursiveIntersectionNative.demandNode_evaluate handle chosen running actual demanded).2
  exact ⟨same, runningPhysical, runningScope, same ▸ cell⟩

/-- An edge start preserves scope and records the exact requested evaluating cell. -/
theorem edge_started (request actual : EdgeRequest Symbol Guard)
    (before chosen running : Native width Symbol Guard) (handle : Nat)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before) (scopes : Scoped before)
    (ready : EdgeReady before.machine request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right)
    (selected : lookupEdge width request before = (handle, chosen))
    (demanded : demandEdge handle chosen = (.evaluate actual, running)) :
    actual = request ∧ SourceCurrentAllocatedNativePhysicalCache.Valid running ∧ Scoped running ∧
      running.edges.cells handle = some ⟨request, .evaluating⟩ := by
  have same := SourceCurrentAllocatedNativePhysicalCache.edge_started request actual before chosen running handle
    physical ready safe selected demanded
  have chosenPhysical := SourceCurrentAllocatedNativePhysicalCache.lookupEdge_valid before physical request ready safe
  have chosenScope := lookupEdge_scoped before request scopes
  simp only [selected] at chosenPhysical chosenScope
  have runningPhysical := SourceCurrentAllocatedNativePhysicalCache.demandEdge_valid chosen chosenPhysical handle
  have runningScope := demandEdge_scoped chosen handle chosenScope
  simp only [demanded] at runningPhysical runningScope
  have cell := (SourceRecursiveIntersectionNative.demandEdge_evaluate handle chosen running actual demanded).2
  exact ⟨same, runningPhysical, runningScope, same ▸ cell⟩

end MicroCFTA.SourceCurrentAllocatedNativeScopeCache
