import MicroCFTA.SourceCurrentEqualityNormalizationFixed
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
namespace MicroCFTA.NormalizationFixedKernels
open EqualityNormalize SourceCurrentEqualityNormalizationFixed
private def raw : Constraints := [[[2],[1]],[[3],[2]],[[9],[8]],[[4]],[[8],[9]]]
private def canonical : Constraints := [[[1],[2],[3]],[[8],[9]]]
private def extended : Constraints := [[[1],[0]],[[2],[0,3]]]
private def closure : Constraints := [[[0],[1]],[[0,3],[1,3],[2]]]
private theorem small : mkEqConstraints 4 raw = .normalized canonical := by cbv
private theorem extended_small : mkEqConstraints 5 extended = .normalized closure := by cbv
private theorem actual (fuel : Nat) (classes output : Constraints)
    (small : mkEqConstraints fuel classes = .normalized output) :
    SourceCompactGuards.normalize classes = some output := by
  have array := SourceEqualityNormalizationReceipt.array_eq fuel classes (by rw [small]; intro impossible; cases impossible)
  unfold SourceCompactGuards.normalize
  rw [array,small]
  rfl
private theorem merged_order_proof :
    SourceCompactGuards.normalize raw = some canonical ∧ Fixed canonical ∧
    SourceCompactGuards.normalize canonical = some canonical ∧
    SourceCompactGuards.combineEqualities (some []) (some canonical) = some canonical ∧
    SourceCompactGuards.combineEqualities (some canonical) (some []) = some canonical ∧
    congruenceStep canonical = some canonical := by
  have produced := actual 4 raw canonical small
  have fixed := normalize_idempotent raw canonical produced
  exact ⟨produced,fixed,fixed,combine_empty_left canonical fixed,combine_empty_right canonical fixed,(invariants canonical fixed).2.2.2⟩
/-- An actual normalization merges overlaps, removes trivial and repeated input, and retains the exact sorted result under both empty combinations. -/
theorem merged_order :
    SourceCompactGuards.normalize raw = some canonical ∧ Fixed canonical ∧
    SourceCompactGuards.normalize canonical = some canonical ∧
    SourceCompactGuards.combineEqualities (some []) (some canonical) = some canonical ∧
    SourceCompactGuards.combineEqualities (some canonical) (some []) = some canonical ∧
    congruenceStep canonical = some canonical := merged_order_proof
private theorem generated_congruence_proof :
    SourceCompactGuards.normalize extended = some closure ∧ Fixed closure ∧
    [1,3] ∈ (closure[1]?.getD []) ∧
    SourceCompactGuards.normalize ([] ++ closure) = some closure ∧
    SourceCompactGuards.combineEqualities (some []) (some closure) = some closure ∧
    SourceCompactGuards.combineEqualities (some closure) (some []) = some closure := by
  have produced := actual 5 extended closure extended_small
  have fixed := normalize_idempotent extended closure produced
  exact ⟨produced,fixed,by simp [closure],empty_append closure fixed,
    combine_empty_left closure fixed,combine_empty_right closure fixed⟩
/-- The actual source normalizer generates the missing shared suffix and then keeps its exact nested-path class order. -/
theorem generated_congruence :
    SourceCompactGuards.normalize extended = some closure ∧ Fixed closure ∧
    [1,3] ∈ (closure[1]?.getD []) ∧
    SourceCompactGuards.normalize ([] ++ closure) = some closure ∧
    SourceCompactGuards.combineEqualities (some []) (some closure) = some closure ∧
    SourceCompactGuards.combineEqualities (some closure) (some []) = some closure := generated_congruence_proof
end MicroCFTA.NormalizationFixedKernels
#check @MicroCFTA.NormalizationFixedKernels.merged_order
#print MicroCFTA.NormalizationFixedKernels.merged_order
#print axioms MicroCFTA.NormalizationFixedKernels.merged_order
#check @MicroCFTA.NormalizationFixedKernels.generated_congruence
#print MicroCFTA.NormalizationFixedKernels.generated_congruence
#print axioms MicroCFTA.NormalizationFixedKernels.generated_congruence
