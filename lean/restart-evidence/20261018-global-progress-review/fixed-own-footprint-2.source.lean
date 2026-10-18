import MicroCFTA.SourceEqualityInheritedGrowthBoundary

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000
set_option cbv.maxSteps 10000000

namespace MicroCFTA.FixedOwnFootprintReview
/-- The normalized own field has no replacement endpoint at child one or below its child one. -/
theorem footprint : SourceEqualityInheritedGrowthBoundary.localConstraint.equalities =
    some [[[0],[1,0,0]],[[0,1],[1,0,0,1],[1,0,1]]] := by
  have completed : EqualityNormalize.mkEqConstraints 32 SourceEqualityInheritedGrowthBoundary.raw =
      .normalized [[[0],[1,0,0]],[[0,1],[1,0,0,1],[1,0,1]]] := by cbv
  change SourceCompactGuards.normalize SourceEqualityInheritedGrowthBoundary.raw = _
  unfold SourceCompactGuards.normalize
  rw [SourceEqualityNormalizationReceipt.array_eq 32 SourceEqualityInheritedGrowthBoundary.raw
    (by rw [completed]; intro impossible; cases impossible),completed]
  rfl
end MicroCFTA.FixedOwnFootprintReview

#check @MicroCFTA.FixedOwnFootprintReview.footprint
#print MicroCFTA.FixedOwnFootprintReview.footprint
#print axioms MicroCFTA.FixedOwnFootprintReview.footprint
