import MicroCFTA.SourceCurrentConstrainedCapNativeCache
import MicroCFTA.SourceCurrentConstrainedCapPairOccurrences
import MicroCFTA.SourceRecursiveIntersectionInputView

/-!
# Source-indexed ranked laws in actual native memo cells

The immutable source determines every numeric occurrence weight. Returned
laws use complete original requests and supported source operands. Empty
cells need no result law. A finish installs only its actual owner's already
derived local cap and occurrence laws. General native closure is separate.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapNativeOccurrenceCache
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentConstrainedCapPairOccurrences (Classified FreeLE sourceWeight)
open SourceCurrentConstrainedCapNonplainRank (pairRank)
open SourceCurrentConstrainedCap (Cap Edge)
open SourceCurrentHereditaryNativeScope (Bindings)
open SourceRecursiveIntersectionInputView (Original)
local notation "Native" => SourceRecursiveIntersectionThunks.State
variable {width : Nat} {Symbol Guard : Type}

/-- A request uses its complete original operands from the fixed source heap. -/
def NodeInputs (source : State Symbol Guard) (request : NodeRequest Symbol Guard) : Prop :=
  Original request.left ∧ Original request.right ∧ Available source request.left ∧ Available source request.right

/-- Every literal row child is an original available value from the same fixed source heap. -/
def EdgeInputs (source : State Symbol Guard) (request : EdgeRequest Symbol Guard) : Prop :=
  (∀ value ∈ request.left.children, Original value ∧ Available source value) ∧
  (∀ value ∈ request.right.children, Original value ∧ Available source value)

/-- A finite literal child list uses the maximum of its actual ordered request ranks. -/
noncomputable def childBudget (annotation : Guard → Prop) : List (Value Symbol Guard × Value Symbol Guard) → Nat
  | [] => 0
  | first :: rest => max (pairRank annotation first.1 first.2) (childBudget annotation rest)

/-- A row request bounds only the child pairs that its literal zip will visit. -/
noncomputable def edgeBudget (annotation : Guard → Prop) (request : EdgeRequest Symbol Guard) : Nat :=
  childBudget annotation (request.left.children.zip request.right.children)

/-- Every actual zipped child request is below its row request's maximum budget. -/
theorem childBudget_member (annotation : Guard → Prop) (values : List (Value Symbol Guard × Value Symbol Guard))
    (value : Value Symbol Guard × Value Symbol Guard) (member : value ∈ values) :
    pairRank annotation value.1 value.2 ≤ childBudget annotation values := by
  induction values with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih later) (Nat.le_max_right _ _)

/-- A common child bound also bounds the exact row maximum. -/
theorem edgeBudget_le (annotation : Guard → Prop) (request : EdgeRequest Symbol Guard) (bound : Nat)
    (bounded : ∀ value ∈ request.left.children.zip request.right.children, pairRank annotation value.1 value.2 ≤ bound) :
    edgeBudget annotation request ≤ bound := by
  unfold edgeBudget
  generalize request.left.children.zip request.right.children = values at *
  induction values with
  | nil => exact Nat.zero_le _
  | cons first rest ih =>
      exact Nat.max_le (bounded first List.mem_cons_self)
        (ih (fun value member => bounded value (List.mem_cons_of_mem _ member)))

/-- Strict child descent bounds the exact row maximum at every positive parent rank. -/
theorem edgeBudget_lt (annotation : Guard → Prop) (request : EdgeRequest Symbol Guard) (bound : Nat) (positive : 0 < bound)
    (smaller : ∀ value ∈ request.left.children.zip request.right.children, pairRank annotation value.1 value.2 < bound) :
    edgeBudget annotation request < bound := by
  unfold edgeBudget
  generalize request.left.children.zip request.right.children = values at *
  induction values with
  | nil => exact positive
  | cons first rest ih =>
      exact Nat.max_lt.mpr ⟨smaller first List.mem_cons_self,
        ih (fun value member => smaller value (List.mem_cons_of_mem _ member))⟩

/-- Returned nodes retain the classifier at the exact original operand rank for every supported cap depth. -/
def NodeLaw (annotation : Guard → Prop) (source : State Symbol Guard)
    (request : NodeRequest Symbol Guard) (result : Value Symbol Guard) : Prop :=
  ∀ depth, Bindings annotation source request.domain.key → NodeInputs source request →
    Cap annotation depth request.left → Cap annotation depth request.right →
    Classified (sourceWeight annotation source) (pairRank annotation request.left request.right) result

/-- Returned rows bound each actual child without inventing an enclosing parent-node request. -/
def EdgeLaw (annotation : Guard → Prop) (source : State Symbol Guard)
    (request : EdgeRequest Symbol Guard) (result : EdgeValue Symbol Guard) : Prop :=
  ∀ depth, Bindings annotation source request.domain.key → EdgeInputs source request →
    Edge annotation depth request.left → Edge annotation depth request.right →
    ∀ value ∈ result.children, FreeLE (sourceWeight annotation source) (edgeBudget annotation request) value

/-- Returned cells retain their earlier cap and occurrence laws and source-indexed occurrence laws. -/
structure Stored (annotation : Guard → Prop) (source : InternedConstructorTemplates.State Symbol Guard)
    (state : Native width Symbol Guard) : Prop where
  /-- The existing conditional cap store remains available unchanged. -/
  base : SourceCurrentConstrainedCapNativeCache.Stored annotation source state
  /-- Each returned node retains the classifier for its complete original request. -/
  nodes : Returned (NodeLaw annotation source) state.nodes
  /-- Each returned row retains the free-name bound for its exact literal child zip. -/
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

/-- Empty tables satisfy conditional cap and occurrence laws without a supplied completed result. -/
theorem initial_stored (width : Nat) (machine : Machine Symbol Guard) : Stored annotation source (initial width machine) := by
  refine ⟨SourceCurrentConstrainedCapNativeCache.initial_stored annotation source width machine, ?_, ?_⟩
  · intro handle request result found
    cases found
  · intro handle request result found
    cases found

/-- Machine changes retain the cap and occurrence laws of unchanged completed cells. -/
theorem advance_stored (state : Native width Symbol Guard) (after : Machine Symbol Guard)
    (annotations : Stored annotation source state) : Stored annotation source (advance state after) := ⟨SourceCurrentConstrainedCapNativeCache.advance_stored annotation source state after annotations.base, annotations.nodes, annotations.edges⟩

/-- Node lookup retains completed cap and occurrence laws and creates no returned result. -/
theorem lookupNode_stored (state : Native width Symbol Guard) (request : NodeRequest Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid state)
    (annotations : Stored annotation source state) : Stored annotation source (lookupNode width request state).2 := by
  cases key : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right with
  | none => simpa only [lookupNode, key] using annotations
  | some keyValue =>
      simp only [lookupNode, key]
      exact ⟨by simpa only [lookupNode, key] using
        SourceCurrentConstrainedCapNativeCache.lookupNode_stored annotation source state request physical annotations.base,
        returned_of_checked _ _ (FlatMemoThunk.lookup_valid keyValue request state.nodes _ _
        (checked_of_returned _ _ _ _ physical.nodes annotations.nodes) trivial trivial), annotations.edges⟩

/-- Edge lookup retains all previously completed cap and occurrence laws. -/
theorem lookupEdge_stored (state : Native width Symbol Guard) (request : EdgeRequest Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid state)
    (annotations : Stored annotation source state) : Stored annotation source (lookupEdge width request state).2 :=
  ⟨SourceCurrentConstrainedCapNativeCache.lookupEdge_stored annotation source state request physical annotations.base,
    annotations.nodes, returned_of_checked _ _ (FlatMemoThunk.lookup_valid _ request state.edges _ _
    (checked_of_returned _ _ _ _ physical.edges annotations.edges) trivial trivial)⟩

/-- Node demand retains the conditional occurrence law of every completed cell. -/
theorem demandNode_stored (state : Native width Symbol Guard) (handle : Nat)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid state)
    (annotations : Stored annotation source state) : Stored annotation source (demandNode handle state).2 :=
  ⟨SourceCurrentConstrainedCapNativeCache.demandNode_stored annotation source state handle physical annotations.base,
    returned_of_checked _ _ (FlatMemoThunk.demand_spec handle state.nodes _ _
    (checked_of_returned _ _ _ _ physical.nodes annotations.nodes)), annotations.edges⟩

/-- Edge demand retains the conditional occurrence law of every completed cell. -/
theorem demandEdge_stored (state : Native width Symbol Guard) (handle : Nat)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid state)
    (annotations : Stored annotation source state) : Stored annotation source (demandEdge handle state).2 :=
  ⟨SourceCurrentConstrainedCapNativeCache.demandEdge_stored annotation source state handle physical annotations.base,
    annotations.nodes, returned_of_checked _ _ (FlatMemoThunk.demand_spec handle state.edges _ _
    (checked_of_returned _ _ _ _ physical.edges annotations.edges))⟩

/-- A node finish stores a conditional occurrence law for its exact evaluating request. -/
theorem finishNode_stored (state : Native width Symbol Guard) (handle : Nat)
    (request : NodeRequest Symbol Guard) (result : Value Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid state) (annotations : Stored annotation source state)
    (running : state.nodes.cells handle = some ⟨request, .evaluating⟩)
    (capLaw : SourceCurrentConstrainedCapNativeLaws.NodeLaw annotation source request result)
    (localLaw : NodeLaw annotation source request result) :
    Stored annotation source (finishNode handle result state) := by
  refine ⟨SourceCurrentConstrainedCapNativeCache.finishNode_stored annotation source state handle request result
    physical annotations.base running capLaw, returned_of_checked _ _ (FlatMemoThunk.finish_spec handle result state.nodes _ _
    (checked_of_returned _ _ _ _ physical.nodes annotations.nodes) ?_), annotations.edges⟩
  intro original found
  have same : request = original := congrArg FlatMemoThunk.Cell.request (Option.some.inj (running.symm.trans found))
  simpa only [same] using localLaw

/-- An edge finish stores a conditional occurrence law for its exact evaluating request. -/
theorem finishEdge_stored (state : Native width Symbol Guard) (handle : Nat)
    (request : EdgeRequest Symbol Guard) (result : EdgeValue Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid state) (annotations : Stored annotation source state)
    (running : state.edges.cells handle = some ⟨request, .evaluating⟩)
    (capLaw : SourceCurrentConstrainedCapNativeLaws.EdgeLaw annotation source request result)
    (localLaw : EdgeLaw annotation source request result) :
    Stored annotation source (finishEdge handle result state) := by
  refine ⟨SourceCurrentConstrainedCapNativeCache.finishEdge_stored annotation source state handle request result
    physical annotations.base running capLaw, annotations.nodes, returned_of_checked _ _ (FlatMemoThunk.finish_spec handle result state.edges _ _
    (checked_of_returned _ _ _ _ physical.edges annotations.edges) ?_)⟩
  intro original found
  have same : request = original := congrArg FlatMemoThunk.Cell.request (Option.some.inj (running.symm.trans found))
  simpa only [same] using localLaw

/-- A warm node hit recovers the exact requested conditional occurrence law and an available result. -/
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

/-- A warm edge hit recovers the exact requested cap law and a resident row. -/
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

/-- A node start preserves conditional cap and occurrence laws and records the exact requested evaluating cell. -/
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

/-- An edge start preserves conditional cap and occurrence laws and records the exact requested evaluating cell. -/
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

end MicroCFTA.SourceCurrentConstrainedCapNativeOccurrenceCache
