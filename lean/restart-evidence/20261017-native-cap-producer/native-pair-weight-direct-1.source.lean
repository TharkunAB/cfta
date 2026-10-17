import MicroCFTA.SourceCurrentConstrainedCapPairOccurrences
import MicroCFTA.SourceCurrentConstrainedCapNativeCoverage

/-!
# Actual source weights of scoped native pairs

Each stored operand reads back its own immutable source record. A covered
reference reads its annotated source Mu and therefore has weight zero.
The source-indexed weight of the sorted numeric pair is the request rank.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapNativePairWeight
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceEqualityAnnotationLanguage
open SourceRecursiveIntersectionControl SourceCurrentHereditaryNativeScope
open SourceCurrentConstrainedCapNativeIdentity (Covered)
open SourceCurrentConstrainedCapNonplainRank (rank pairRank)
open SourceCurrentConstrainedCapPairOccurrences (identityWeight sourceWeight)
variable {Symbol Guard : Type}

/-- A scoped actual operand has the rank of the immutable payload at its numeric identity. -/
theorem identity_weight (annotation : Guard → Prop) (source : State Symbol Guard) (facts : Facts source)
    (domain : DomainKey) (bindings : Bindings annotation source domain)
    (value : Value Symbol Guard) (available : Available source value) (covered : Covered domain value)
    (number : Nat) (actual : identity value = some number) : identityWeight annotation source number = rank annotation value := by
  cases value with
  | empty => cases actual
  | reference name =>
      cases name <;> simp only [identity, reduceCtorEq, Option.some.injEq] at actual
      subst number
      obtain ⟨stored, resident, reference, annotated⟩ := bindings _ (covered _ (by simp [Value.free]))
      cases stored <;> simp only [Value.referenceOf, reduceCtorEq] at reference
      case mu entry body depth ordinary =>
        cases reference
        have read := SourcePreparedSharedRows.read_identity source facts _ resident entry.identity rfl
        simp only [identityWeight, read, Option.map_some, Option.getD_some]
        rw [SourceCurrentConstrainedCapNonplainRank.rank_annotated annotation _ annotated,
          SourceCurrentConstrainedCapNonplainRank.reference_zero]
  | node entry edges level free | union entry members level free | mu entry body depth ordinary =>
      have same : entry.identity = number := Option.some.inj actual
      have read := SourcePreparedSharedRows.read_identity source facts _ available number (by
        simpa only [SourcePreparedSharedRows.reference, same])
      simp only [identityWeight, read, Option.map_some, Option.getD_some]

/-- The actual sorted pair has the complete ordered operand-rank sum. -/
theorem pair_weight (annotation : Guard → Prop) (source : State Symbol Guard) (facts : Facts source)
    (domain : DomainKey) (bindings : Bindings annotation source domain)
    (left right : Value Symbol Guard) (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftCovered : Covered domain left) (rightCovered : Covered domain right)
    (first second : Nat) (leftId : identity left = some first) (rightId : identity right = some second) :
    sourceWeight annotation source (.intersection (pair first second).1 (pair first second).2) = pairRank annotation left right := by
  have leftWeight := identity_weight annotation source facts domain bindings left leftAvailable leftCovered first leftId
  have rightWeight := identity_weight annotation source facts domain bindings right rightAvailable rightCovered second rightId
  by_cases order : first ≤ second
  · simpa only [sourceWeight, pair, Nat.min_eq_left order, Nat.max_eq_right order, leftWeight, rightWeight,
      SourceCurrentConstrainedCapNonplainRank.pairRank]
  · have reverse : second ≤ first := by omega
    simp only [sourceWeight, pair, Nat.min_eq_right reverse, Nat.max_eq_left reverse, leftWeight, rightWeight,
      SourceCurrentConstrainedCapNonplainRank.pairRank]
    exact Nat.add_comm _ _

end MicroCFTA.SourceCurrentConstrainedCapNativePairWeight
