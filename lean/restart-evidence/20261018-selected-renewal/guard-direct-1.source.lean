import MicroCFTA.SourceCurrentNativeOwnOriginBoundary

/-!
# A live positive pair lost by an unsupported joined guard

The first accessor returns a live equality class. Conjunction retains its
Same atom. The second guard is outside the positive parser. The joined
accessor therefore returns its empty stored field. Both arity checks pass.
This is a parser boundary. It is not a complete native execution or a
Haskell defect.
-/
namespace MicroCFTA.SourceCurrentPositiveAccessorBoundary
local notation "Field" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq

private def pair : EqualityNormalize.Constraints := [[[0],[1]]]
private def first : Field := ⟨some [],.same [0] [1]⟩
private def second : Field := ⟨some [],.not .bottom⟩
private def joined : Field := ⟨some [],.and [.same [0] [1],.not .bottom]⟩

private theorem pair_normalized : SourceCompactGuards.normalize pair = some pair := by
  have small : EqualityNormalize.mkEqConstraints 2 pair = .normalized pair := by cbv
  have array := SourceEqualityNormalizationReceipt.array_eq 2 pair
    (by rw [small]; intro impossible; cases impossible)
  unfold SourceCompactGuards.normalize
  rw [array,small]
  rfl

private theorem first_own : SourceCompactGuards.sourceEqualities first = some pair := by
  have positive : SourceCompactGuards.positiveNormalized first.guard = some (some pair) := by
    change (if [0] ≠ [1] then some (SourceCompactGuards.normalize pair) else none) = _
    rw [ite_eq_left (by decide),pair_normalized]
  change (match SourceCompactGuards.positiveNormalized first.guard with
    | none | some (some []) => some []
    | some added => SourceCompactGuards.combineEqualities (some []) added) = some pair
  rw [positive]
  change SourceCompactGuards.normalize ([] ++ pair) = some pair
  exact pair_normalized

private theorem combined : SourceEqualityPCSNativeEdge.conjoin first second = joined := by
  change (⟨some [],GuardConjunction.merge GuardStructuralOrder.le first.guard second.guard⟩ : Field) = _
  cbv

private theorem joined_own : SourceCompactGuards.sourceEqualities joined = some [] := by
  unfold joined SourceCompactGuards.sourceEqualities
  simp only [SourceCompactGuards.positiveNormalized,SourceCompactGuards.positiveNormalizedList]
  rfl

private theorem checked_witness :
    SourceCompactGuards.positive first.guard = some pair ∧
    SourceCompactGuards.sourceEqualities first = some pair ∧
    SourceCompactGuards.sourceEqualities second = some [] ∧
    SourceEqualityPCSNativeEdge.conjoin first second = joined ∧
    .same [0] [1] ∈ GuardConjunction.atoms joined.guard ∧
    .not .bottom ∈ GuardConjunction.atoms joined.guard ∧
    SourceCompactGuards.positiveNormalized joined.guard = none ∧
    SourceCompactGuards.sourceEqualities joined = some [] ∧
    ¬ EqualityNormalize.Covers pair (SourceCompactGuards.sourceEqualities joined).getD [] ∧
    SourceEqualityMkEdgeAllocation.accepted first 2 = true ∧
    SourceEqualityMkEdgeAllocation.accepted joined 2 = true := by
  have notCovered : ¬ EqualityNormalize.Covers pair [] := by
    intro covers
    obtain ⟨_,impossible,_⟩ := covers [[0],[1]] (by simp [pair])
    cases impossible
  have firstAccepted : SourceEqualityMkEdgeAllocation.accepted first 2 = true := by
    change SourceEqualityMkEdgeAllocation.fits 2 (SourceCompactGuards.sourceEqualities first) = true
    rw [first_own]
    cbv
  have joinedAccepted : SourceEqualityMkEdgeAllocation.accepted joined 2 = true := by
    change SourceEqualityMkEdgeAllocation.fits 2 (SourceCompactGuards.sourceEqualities joined) = true
    rw [joined_own]
    cbv
  exact ⟨rfl,first_own,rfl,combined,by simp [joined,GuardConjunction.atoms],
    by simp [joined,GuardConjunction.atoms],rfl,joined_own,
    by rw [joined_own]; exact notCovered,firstAccepted,joinedAccepted⟩

/-- An unsupported joined guard drops a live accessor pair while retaining its original Same atom. -/
theorem live_pair_lost :
    let first : Field := ⟨some [],.same [0] [1]⟩
    let second : Field := ⟨some [],.not .bottom⟩
    let joined : Field := ⟨some [],.and [.same [0] [1],.not .bottom]⟩
    SourceCompactGuards.positive first.guard = some [[[0],[1]]] ∧
    SourceCompactGuards.sourceEqualities first = some [[[0],[1]]] ∧
    SourceCompactGuards.sourceEqualities second = some [] ∧
    SourceEqualityPCSNativeEdge.conjoin first second = joined ∧
    .same [0] [1] ∈ GuardConjunction.atoms joined.guard ∧
    .not .bottom ∈ GuardConjunction.atoms joined.guard ∧
    SourceCompactGuards.positiveNormalized joined.guard = none ∧
    SourceCompactGuards.sourceEqualities joined = some [] ∧
    ¬ EqualityNormalize.Covers [[[0],[1]]] (SourceCompactGuards.sourceEqualities joined).getD [] ∧
    SourceEqualityMkEdgeAllocation.accepted first 2 = true ∧
    SourceEqualityMkEdgeAllocation.accepted joined 2 = true := checked_witness

end MicroCFTA.SourceCurrentPositiveAccessorBoundary
