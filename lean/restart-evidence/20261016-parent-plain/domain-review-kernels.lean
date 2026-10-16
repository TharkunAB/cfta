import MicroCFTA.SourceCurrentAllocatedPartialReturnedDomain
import MicroCFTA.SourceCurrentAllocatedPartialWorker

namespace MicroCFTA.ReturnedDomainReview
open Cache InternedConstructorTemplates
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialReturnedDomain
open SourceCurrentAllocatedPartialActiveOrder
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Regions" => SourceEqualityPartialPlainRegion.Children
local notation "Region" => SourceEqualityPartialPlainRegion.Region
local notation "RawEntry" => Cache.Interned (InternedConstructorTemplates.EdgeKey Symbol Guard)

-- The original-child shape transfers the actual child list and its Region without a semantic premise.
theorem unchanged_children (original result : Edge) (same : result.children = original.children)
    (regions : Regions original.children) : Regions result.children ∧
      MergedOrdinaryHeight.edgeHeight result ≤ MergedOrdinaryHeight.edgeHeight original := by
  have shape := Shape.original same
  exact ⟨shape.regions regions, shape.height⟩

-- Erased slots retain Region even when no original child Region is known.
theorem erased_children (entry oldEntry : RawEntry) (values : List Node) :
    let original : Edge := .mk oldEntry values
    let result : Edge := .mk entry (EqualityLeafProjectionRuntimeEmpty.erase values)
    Shape original result ∧ Regions result.children ∧
      MergedOrdinaryHeight.edgeHeight result ≤ MergedOrdinaryHeight.edgeHeight original := by
  have regions : Regions (EqualityLeafProjectionRuntimeEmpty.erase values) := by
    induction values with
    | nil => exact .nil
    | cons value rest ih => exact .cons .empty ih
  have shape : Shape (.mk oldEntry values) (.mk entry (EqualityLeafProjectionRuntimeEmpty.erase values)) :=
    Or.inr (Or.inl rfl)
  exact ⟨shape, regions, shape.height⟩

-- Nullary rejection has one Empty child. It preserves height and Region but not arity.
theorem nullary_sentinel (entry oldEntry : RawEntry) (inherited : SourceEqualityConstraintAllocation.Value) :
    let original : Edge := .mk oldEntry []
    let result : Edge := .mk entry [.empty]
    Shape original result ∧ Regions result.children ∧
      result.children.length ≠ original.children.length ∧
      MergedOrdinaryHeight.edgeHeight result = MergedOrdinaryHeight.edgeHeight original ∧
      nodeRank ⟨inherited, .empty⟩ < edgeRank ⟨inherited, original⟩ := by
  refine ⟨Shape.sentinel rfl, .cons .empty .nil, by change 1 ≠ 0; decide, rfl, ?_⟩
  change 1 < 2
  decide

variable [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Guard)] [DecidableEq Node]

-- Actual publication and a completed parent body retain Stored; exact finish installs its own certificate.
theorem publish_parent_finish {width : Nat} {before running middle : Caller width}
    {request owner : EdgeRequest} {handle budget : Nat} {result : Edge}
    (stored : Stored before) (protocol : SourceCurrentAllocatedPartialFrames.Protocol before)
    (started : beginEdge request before = (handle, .evaluate owner, running))
    (body : EdgeBody budget owner running result middle) (shape : Shape owner.value result) :
    Stored (finishEdge handle result middle) ∧
      (finishEdge handle result middle).edgeResults.cells handle = some ⟨owner, .returned result⟩ := by
  have atStart := stored.beginEdge request
  rw [started] at atStart
  have atMiddle : Stored middle := by
    cases body
    exact atStart.advance _ _ _
  have own := (SourceCurrentAllocatedPartialFrames.beginEdge_owner request before handle owner running protocol started).1
  have forward := SourceCurrentAllocatedPartialFrames.beginEdge_frame request before protocol
  rw [started] at forward
  have bodyFrame := SourceCurrentAllocatedPartialFrames.edge_body body forward.valid
  have runningOwner := bodyFrame.edge_running handle owner own
  exact ⟨atMiddle.finishEdge result runningOwner shape, finishEdge_returned handle owner result middle runningOwner⟩

-- A warm candidate uses the STORED owner's certificate, transferred by actual coherent resident key equality.
theorem warm_hit_child {width : Nat} (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (before : Caller width) (candidate owner : EdgeRequest) (handle : Nat) (result : Edge)
    (stored : Stored before) (sound : SourceCurrentAllocatedPartialMemoSound.Sound formulas solver before)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap)
    (resident : InternedEdgeResidency.EdgeResident before.checked.native.machine.heap candidate.value)
    (published : before.edgeResults.table candidate.key = some handle)
    (returned : before.edgeResults.cells handle = some ⟨owner, .returned result⟩)
    (regions : Regions candidate.value.children) (inherited : SourceEqualityConstraintAllocation.Value)
    (child : Node) (member : child ∈ result.children) :
    SourceCurrentAllocatedPartialWorker.edgeCall 0 0 0 0 0 0 0 0 0 0 0 candidate before = .done result before ∧
      Region child ∧ nodeRank ⟨inherited, child⟩ < edgeRank candidate := by
  obtain ⟨cell, present, linked⟩ := sound.valid.edges.linked candidate.key handle published
  have sameCell := Option.some.inj (present.symm.trans returned)
  subst cell
  have originalResident := (sound.edges handle _ returned).input
  have same := InternedEdgeResidency.edge_identity_unique before.checked.native.machine.heap coherent
    owner.value candidate.value originalResident resident (congrArg Prod.snd linked.2)
  have ownerRegions : Regions owner.value.children := same ▸ regions
  have childFacts := stored.child returned ownerRegions inherited child member
  refine ⟨SourceCurrentAllocatedPartialWorker.edgeCall_ready 0 0 0 0 0 0 0 0 0 0 0 candidate before before handle result
    (beginEdge_ready candidate owner before handle result published returned), childFacts.1, ?_⟩
  simpa only [edgeRank, same] using childFacts.2

end MicroCFTA.ReturnedDomainReview
#print axioms MicroCFTA.ReturnedDomainReview.unchanged_children
#print axioms MicroCFTA.ReturnedDomainReview.erased_children
#print axioms MicroCFTA.ReturnedDomainReview.nullary_sentinel
#print axioms MicroCFTA.ReturnedDomainReview.publish_parent_finish
#print axioms MicroCFTA.ReturnedDomainReview.warm_hit_child
