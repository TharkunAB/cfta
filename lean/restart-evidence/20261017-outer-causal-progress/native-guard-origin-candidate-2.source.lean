import MicroCFTA.SourceCurrentNativeEdgeHistory
import MicroCFTA.SourceEqualityNormalizationReceipt
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
namespace MicroCFTA.NativeGuardOriginCandidate
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq
private def base : EqualityNormalize.Constraints := [[[0],[1]]]
private def bad : EqualityNormalize.Constraints := [[[0],[0,0]]]
private def first : Guard := ⟨some base,.same [0] [0,0]⟩
private def second : Guard := ⟨some [],.not .top⟩
private def joined : Guard := ⟨some base,.and [.same [0] [0,0],.not .top]⟩
private theorem base_normalized : SourceCompactGuards.normalize base = some base := by
  have small : EqualityNormalize.mkEqConstraints 2 base = .normalized base := by cbv
  have array := SourceEqualityNormalizationReceipt.array_eq 2 base
    (by rw [small]; intro impossible; cases impossible)
  unfold SourceCompactGuards.normalize
  rw [array,small]
  rfl
private theorem bad_normalized : SourceCompactGuards.normalize bad = none := by
  have small : EqualityNormalize.mkEqConstraints 1 bad = .contradiction := by cbv
  have array := SourceEqualityNormalizationReceipt.array_eq 1 bad
    (by rw [small]; intro impossible; cases impossible)
  unfold SourceCompactGuards.normalize
  rw [array,small]
  rfl
private theorem first_own : SourceCompactGuards.sourceEqualities first = none := by
  change (match SourceCompactGuards.positiveNormalized
      (.same [0] [0,0] : SourceGuards.Guard FullSyntax.Formula) with
    | none | some (some []) => some base
    | some added => SourceCompactGuards.combineEqualities (some base) added) = none
  have positive : SourceCompactGuards.positiveNormalized
      (.same [0] [0,0] : SourceGuards.Guard FullSyntax.Formula) = some none := by
    change (if [0] ≠ [0,0] then some (SourceCompactGuards.normalize bad) else none) = _
    rw [if_pos (by decide),bad_normalized]
  rw [positive]
  rfl
private theorem combined : SourceEqualityPCSNativeEdge.conjoin first second = joined := by
  change (⟨SourceCompactGuards.normalize (base ++ []),
    GuardConjunction.merge GuardStructuralOrder.le first.guard second.guard⟩ : Guard) = _
  rw [List.append_nil,base_normalized]
  cbv
private theorem joined_own : SourceCompactGuards.sourceEqualities joined = some base := by
  unfold joined SourceCompactGuards.sourceEqualities
  simp only [SourceCompactGuards.positiveNormalized,SourceCompactGuards.positiveNormalizedList]
  rfl
private theorem accepted : SourceEqualityMkEdgeAllocation.accepted joined 2 = true := by
  unfold SourceEqualityMkEdgeAllocation.accepted
  change SourceEqualityMkEdgeAllocation.fits 2 (SourceCompactGuards.sourceEqualities joined) = true
  rw [joined_own]
  cbv
private theorem own_counterexample_proof :
    SourceCompactGuards.sourceEqualities first = none ∧
    SourceCompactGuards.sourceEqualities second = some [] ∧
    SourceEqualityPCSNativeEdge.conjoin first second = joined ∧
    SourceCompactGuards.sourceEqualities joined = some base ∧ base ≠ [] ∧
    SourceEqualityMkEdgeAllocation.accepted joined 2 = true :=
  ⟨first_own,rfl,combined,joined_own,by decide,accepted⟩
/-- A live joined own payload can retain a stored operand field whose separate accessor was contradictory. -/
theorem own_counterexample :
    SourceCompactGuards.sourceEqualities first = none ∧
    SourceCompactGuards.sourceEqualities second = some [] ∧
    SourceEqualityPCSNativeEdge.conjoin first second = joined ∧
    SourceCompactGuards.sourceEqualities joined = some base ∧ base ≠ [] ∧
    SourceEqualityMkEdgeAllocation.accepted joined 2 = true := own_counterexample_proof
end MicroCFTA.NativeGuardOriginCandidate
#check @MicroCFTA.NativeGuardOriginCandidate.own_counterexample
#print MicroCFTA.NativeGuardOriginCandidate.own_counterexample
#print axioms MicroCFTA.NativeGuardOriginCandidate.own_counterexample
