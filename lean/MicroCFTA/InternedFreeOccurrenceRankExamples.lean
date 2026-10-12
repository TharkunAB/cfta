import MicroCFTA.InternedFreeOccurrenceRank
import MicroCFTA.InternedGateHeadGrowth

/-!
# Free-occurrence costs through actual source reconstruction

The candidate cost decreases on the source example where the leading Mu
count increases. This checked example does not replace a general source
substitution theorem.
-/
namespace MicroCFTA.InternedFreeOccurrenceRankExamples
open InternedConstructorTemplates InternedNestedConstruction InternedFreeOccurrenceRank

/-- Observe the candidate cost only after actual source completion. -/
def resultRank : Outcome Symbol Guard (Value Symbol Guard) → Option Nat
  | .done value _ => some (rank value)
  | .pending .. => none

/-- The source normalization counterexample has lower free-occurrence cost
although its consecutive leading Mu count increases. -/
theorem raw_growth_cost : resultRank InternedGateHeadGrowth.original = some 3 ∧
    resultRank InternedGateHeadGrowth.firstUnfold = some 2 := by
  set_option cbv.maxSteps 1000000 in cbv

/-- The earlier nested open union example also decreases this candidate cost. -/
theorem nested_union_cost : resultRank InternedGateReconstructionExamples.original = some 2 ∧
    resultRank InternedStoredSubstitution.firstStoredUnfold = some 1 ∧
    resultRank InternedStoredSubstitution.secondStoredUnfold = some 0 := by cbv

end MicroCFTA.InternedFreeOccurrenceRankExamples
