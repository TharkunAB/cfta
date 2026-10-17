import MicroCFTA.SourceCurrentAllocatedNativeContextCache
import MicroCFTA.SourceCurrentAllocatedNativePhysicalCache
import MicroCFTA.SourceCurrentConstrainedCapNativeLaws
import MicroCFTA.FlatMemoThunkReturned

/-!
# Conditional cap laws in actual returned native cells

Each returned law refers to its complete captured request and source names.
Physical validity supplies the existing memo metadata for generic CellSpec
preservation. The cap laws remain a separate invariant.
A finish installs only a law proved for its actual evaluating owner.
This module does not prove mixed compilation or query completion.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapNativeCache
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceCurrentAllocatedNativeContextCache (Returned)
local notation "Native" => SourceRecursiveIntersectionThunks.State
variable {width : Nat} {Symbol Guard : Type}

open SourceCurrentConstrainedCapNativeLaws (NodeLaw EdgeLaw)

/-- Returned cells carry conditional conditional cap laws for their exact original requests. -/
structure Stored (annotation : Guard → Prop) (source : InternedConstructorTemplates.State Symbol Guard)
    (state : Native width Symbol Guard) : Prop where
  /-- Each returned node retains every common cap of its original ordered operands. -/
  nodes : Returned (NodeLaw annotation source) state.nodes
  /-- Each returned row retains every common cap of its complete original rows. -/
  edges : Returned (EdgeLaw annotation source) state.edges

variable (annotation : Guard → Prop) (source : InternedConstructorTemplates.State Symbol Guard)

private theorem checked_of_returned (law : Request → Answer → Prop)
    (state : FlatMemoThunk.State Key Request Answer) (keyOf : Request → Key → Prop)
    (good : FlatMemoThunk.Cell Request Answer → Prop) (physical : FlatMemoThunk.Valid keyOf good state)
    (stored : Returned law state) : FlatMemoThunk.Valid (fun _ _ => True) (FlatMemoThunk.CellSpec law) state := by
  refine ⟨physical.bounded, ?_, ?_⟩
  · intro key handle found
    obtain ⟨cell, present, _linked⟩ := physical.linked key handle found
    exact ⟨cell, present, trivial⟩
  · intro handle cell found
    cases cell with
    | mk request status =>
        cases status with
        | suspended | evaluating => trivial
        | returned result => exact stored handle request result found

private theorem returned_of_checked (law : Request → Answer → Prop)
    (state : FlatMemoThunk.State Key Request Answer)
    (checked : FlatMemoThunk.Valid (fun _ _ => True) (FlatMemoThunk.CellSpec law) state) : Returned law state :=
  fun handle request result found => checked.checked handle ⟨request, .returned result⟩ found

/-- Empty tables satisfy conditional cap laws without a supplied completed result. -/
theorem initial_stored (width : Nat) (machine : Machine Symbol Guard) : Stored annotation source (initial width machine) := by
  constructor
  · intro handle request result found
    cases found
  · intro handle request result found
    cases found

/-- Machine changes retain the annotations of unchanged completed cells. -/
theorem advance_stored (state : Native width Symbol Guard) (after : Machine Symbol Guard)
    (annotations : Stored annotation source state) : Stored annotation source (advance state after) := ⟨annotations.nodes, annotations.edges⟩

/-- Node lookup retains completed cap laws and creates no returned result. -/
theorem lookupNode_stored (state : Native width Symbol Guard) (request : NodeRequest Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid state)
    (annotations : Stored annotation source state) : Stored annotation source (lookupNode width request state).2 := by
  cases key : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right with
  | none => simpa only [lookupNode, key] using annotations
  | some keyValue =>
      simp only [lookupNode, key]
      exact ⟨returned_of_checked _ _ (FlatMemoThunk.lookup_valid keyValue request state.nodes _ _
        (checked_of_returned _ _ _ _ physical.nodes annotations.nodes) trivial trivial), annotations.edges⟩

/-- Edge lookup retains all previously completed cap laws. -/
theorem lookupEdge_stored (state : Native width Symbol Guard) (request : EdgeRequest Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid state)
    (annotations : Stored annotation source state) : Stored annotation source (lookupEdge width request state).2 :=
  ⟨annotations.nodes, returned_of_checked _ _ (FlatMemoThunk.lookup_valid _ request state.edges _ _
    (checked_of_returned _ _ _ _ physical.edges annotations.edges) trivial trivial)⟩

/-- Node demand retains the conditional cap law of every completed cell. -/
theorem demandNode_stored (state : Native width Symbol Guard) (handle : Nat)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid state)
    (annotations : Stored annotation source state) : Stored annotation source (demandNode handle state).2 :=
  ⟨returned_of_checked _ _ (FlatMemoThunk.demand_spec handle state.nodes _ _
    (checked_of_returned _ _ _ _ physical.nodes annotations.nodes)), annotations.edges⟩

/-- Edge demand retains the conditional cap law of every completed cell. -/
theorem demandEdge_stored (state : Native width Symbol Guard) (handle : Nat)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid state)
    (annotations : Stored annotation source state) : Stored annotation source (demandEdge handle state).2 :=
  ⟨annotations.nodes, returned_of_checked _ _ (FlatMemoThunk.demand_spec handle state.edges _ _
    (checked_of_returned _ _ _ _ physical.edges annotations.edges))⟩

/-- A node finish stores a conditional cap law for its exact evaluating request. -/
theorem finishNode_stored (state : Native width Symbol Guard) (handle : Nat)
    (request : NodeRequest Symbol Guard) (result : Value Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid state) (annotations : Stored annotation source state)
    (running : state.nodes.cells handle = some ⟨request, .evaluating⟩) (localLaw : NodeLaw annotation source request result) :
    Stored annotation source (finishNode handle result state) := by
  refine ⟨returned_of_checked _ _ (FlatMemoThunk.finish_spec handle result state.nodes _ _
    (checked_of_returned _ _ _ _ physical.nodes annotations.nodes) ?_), annotations.edges⟩
  intro original found
  have same : request = original := congrArg FlatMemoThunk.Cell.request (Option.some.inj (running.symm.trans found))
  simpa only [same] using localLaw

/-- An edge finish stores a conditional cap law for its exact evaluating request. -/
theorem finishEdge_stored (state : Native width Symbol Guard) (handle : Nat)
    (request : EdgeRequest Symbol Guard) (result : EdgeValue Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid state) (annotations : Stored annotation source state)
    (running : state.edges.cells handle = some ⟨request, .evaluating⟩) (localLaw : EdgeLaw annotation source request result) :
    Stored annotation source (finishEdge handle result state) := by
  refine ⟨annotations.nodes, returned_of_checked _ _ (FlatMemoThunk.finish_spec handle result state.edges _ _
    (checked_of_returned _ _ _ _ physical.edges annotations.edges) ?_)⟩
  intro original found
  have same : request = original := congrArg FlatMemoThunk.Cell.request (Option.some.inj (running.symm.trans found))
  simpa only [same] using localLaw

/-- A warm node hit recovers the exact requested conditional cap law and an available result. -/
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
  have chosenAnnotations := lookupNode_stored annotation source before request physical annotations
  simp only [selected] at chosenAnnotations
  exact ⟨chosenAnnotations.nodes handle request result receipt.1, receipt.2.1 ▸ chosenAnnotations, receipt.2⟩

/-- A warm edge hit recovers the exact requested child annotations and a resident row. -/
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
  have chosenAnnotations := lookupEdge_stored annotation source before request physical annotations
  simp only [selected] at chosenAnnotations
  exact ⟨chosenAnnotations.edges handle request result receipt.1, receipt.2.1 ▸ chosenAnnotations, receipt.2⟩

/-- A node start preserves conditional cap laws and records the exact requested evaluating cell. -/
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
  have chosenAnnotations := lookupNode_stored annotation source before request physical annotations
  simp only [selected] at chosenPhysical chosenAnnotations
  have runningPhysical := SourceCurrentAllocatedNativePhysicalCache.demandNode_valid chosen chosenPhysical handle
  have runningAnnotations := demandNode_stored annotation source chosen handle chosenPhysical chosenAnnotations
  simp only [demanded] at runningPhysical runningAnnotations
  have cell := (SourceRecursiveIntersectionNative.demandNode_evaluate handle chosen running actual demanded).2
  exact ⟨same, runningPhysical, runningAnnotations, same ▸ cell⟩

/-- An edge start preserves conditional cap laws and records the exact requested evaluating cell. -/
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
  have chosenAnnotations := lookupEdge_stored annotation source before request physical annotations
  simp only [selected] at chosenPhysical chosenAnnotations
  have runningPhysical := SourceCurrentAllocatedNativePhysicalCache.demandEdge_valid chosen chosenPhysical handle
  have runningAnnotations := demandEdge_stored annotation source chosen handle chosenPhysical chosenAnnotations
  simp only [demanded] at runningPhysical runningAnnotations
  have cell := (SourceRecursiveIntersectionNative.demandEdge_evaluate handle chosen running actual demanded).2
  exact ⟨same, runningPhysical, runningAnnotations, same ▸ cell⟩

end MicroCFTA.SourceCurrentConstrainedCapNativeCache
