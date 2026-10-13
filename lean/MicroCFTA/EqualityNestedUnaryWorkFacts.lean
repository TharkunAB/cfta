import MicroCFTA.EqualityNestedUnaryWork

/-!
# Actual completed-cache facts for the nested intersection worker

The constructor-work interface returns the same complete endpoint and cache
as the proved source action. Path reconstruction can use these facts at
its actual intermediate states without a later cache preparation step.
-/
namespace MicroCFTA.EqualityNestedUnaryWorkFacts
open SourceGuards FullSyntax InternedConstructorTemplates InternedRecordCoherence
open InternedProbeProvenance InternedNestedFacts InternedNestedProvenance InternedEdgeResidency
open MergedPhysicalWarmup MergedSourceComparison MergedColdMerge
open EqualityNestedUnaryCarrier EqualityNestedUnaryProduct EqualityMergedTargetReadback

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- Actual nested constructor work derives its returned cache and exact generated endpoint rows. -/
theorem meet_correct (parent leaf : Fin symbols) (left right : Node initial)
    (first second : Value (Fin symbols) ConstraintKey)
    (leftShape : NodeShape parent leaf left first) (rightShape : NodeShape parent leaf right second)
    (leftNormal : Replayable first) (rightNormal : Replayable second)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (prepared : Prepared state)
    (leftAvailable : Available state first) (rightAvailable : Available state second) :
    let result := run (EqualityNestedUnaryWork.meet first second) state
    Extension state result.2 ∧ Available result.2 result.1 ∧ Replayable result.1 ∧
      NodeShape parent leaf (EqualityFixedProjectionInvariant.narrow (Join initial) left right) result.1 := by
  obtain ⟨bound, value, after, done, extension, available, normal, represented⟩ :=
    EqualityNestedUnaryMeet.meet_complete parent leaf left right first second leftShape rightShape
      leftNormal rightNormal state facts prepared leftAvailable rightAvailable
  have actual := (EqualityNestedUnaryWork.meet_eq first second state).trans (done bound (Nat.le_refl _))
  have valueEq := (Result.done.inj actual).1
  have stateEq := (Result.done.inj actual).2
  dsimp only
  rw [valueEq, stateEq]
  exact ⟨extension, available, normal, represented⟩

/-- The actual returned nested endpoint keeps every finite ordinary target-merge layer exact. -/
theorem meet_normal (parent leaf : Fin symbols) (left right : Node initial)
    (small : (SourceLeafRowProgress.basis initial).length ≤ 2)
    (first second : Value (Fin symbols) ConstraintKey)
    (leftShape : NodeShape parent leaf left first) (rightShape : NodeShape parent leaf right second)
    (leftNormal : Replayable first) (rightNormal : Replayable second)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (prepared : Prepared state)
    (leftAvailable : Available state first) (rightAvailable : Available state second) :
    EqualityMergedTargetLayers.Normal EqualityMergedTargetFixedPoint.Exact
      (run (EqualityNestedUnaryWork.meet first second) state).1 := by
  obtain ⟨extension, available, normal, represented⟩ := meet_correct parent leaf left right first second
    leftShape rightShape leftNormal rightNormal state facts prepared leftAvailable rightAvailable
  exact EqualityNestedUnaryBound.node_normal parent leaf _ _ small represented normal _
    extension.facts extension.prepared available

end MicroCFTA.EqualityNestedUnaryWorkFacts
