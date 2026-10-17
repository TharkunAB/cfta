import MicroCFTA.SourceCurrentConstrainedCapNonplainRank
import MicroCFTA.SourceCurrentConstrainedCapNativeIdentity

/-!
# Numeric native pairs preserve the nonhereditary request rank

Sorted identity pairs can match in either operand order. Coherent source
readback identifies the records, or makes both records hereditary. In both
cases their ranks agree. A strict ordinary descent therefore cannot name
its ancestor pair. Coverage uses one explicit common source domain.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapNativePairRank
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionControl
open SourceCurrentHereditaryNativeScope (Bindings)
open SourceCurrentConstrainedCapNativeIdentity (Covered)
open SourceCurrentConstrainedCapNonplainRank (rank pairRank)
variable {Symbol Guard : Type}

/-- Equal sorted numeric pairs agree in their original order or in reverse order. -/
theorem sorted_pair_eq (first second left right : Nat) (same : pair first second = pair left right) :
    (first = left ∧ second = right) ∨ (first = right ∧ second = left) := by
  have low := congrArg Prod.fst same
  have high := congrArg Prod.snd same
  simp only [pair] at low high
  omega

/-- Exact source identity compatibility retains the rank across reference and record tags. -/
theorem same_identity_rank (annotation : Guard → Prop) (source : State Symbol Guard) (facts : Facts source)
    (domain : DomainKey) (bindings : Bindings annotation source domain)
    (left right : Value Symbol Guard) (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftCovered : Covered domain left) (rightCovered : Covered domain right) (number : Nat)
    (leftId : identity left = some number) (rightId : identity right = some number) : rank annotation left = rank annotation right :=
  SourceCurrentConstrainedCapNonplainRank.of_eq_or_annotated annotation left right
    (SourceCurrentConstrainedCapNativeIdentity.same_identity annotation source facts domain bindings left right
      leftAvailable rightAvailable leftCovered rightCovered number leftId rightId)

/-- Equal actual numeric pairs retain the complete operand-rank sum in one common domain. -/
theorem same_pair_rank (annotation : Guard → Prop) (source : State Symbol Guard) (facts : Facts source)
    (domain : DomainKey) (bindings : Bindings annotation source domain)
    (first second left right : Value Symbol Guard)
    (firstAvailable : Available source first) (secondAvailable : Available source second)
    (leftAvailable : Available source left) (rightAvailable : Available source right)
    (firstCovered : Covered domain first) (secondCovered : Covered domain second)
    (leftCovered : Covered domain left) (rightCovered : Covered domain right)
    (firstNumber secondNumber leftNumber rightNumber : Nat)
    (firstId : identity first = some firstNumber) (secondId : identity second = some secondNumber)
    (leftId : identity left = some leftNumber) (rightId : identity right = some rightNumber)
    (same : pair firstNumber secondNumber = pair leftNumber rightNumber) :
    pairRank annotation first second = pairRank annotation left right := by
  rcases sorted_pair_eq firstNumber secondNumber leftNumber rightNumber same with direct | reverse
  · have firstRank := same_identity_rank annotation source facts domain bindings first left firstAvailable leftAvailable
      firstCovered leftCovered firstNumber firstId (direct.1 ▸ leftId)
    have secondRank := same_identity_rank annotation source facts domain bindings second right secondAvailable rightAvailable
      secondCovered rightCovered secondNumber secondId (direct.2 ▸ rightId)
    change rank annotation first + rank annotation second = rank annotation left + rank annotation right
    rw [firstRank, secondRank]
  · have firstRank := same_identity_rank annotation source facts domain bindings first right firstAvailable rightAvailable
      firstCovered rightCovered firstNumber firstId (reverse.1 ▸ rightId)
    have secondRank := same_identity_rank annotation source facts domain bindings second left secondAvailable leftAvailable
      secondCovered leftCovered secondNumber secondId (reverse.2 ▸ leftId)
    change rank annotation first + rank annotation second = rank annotation left + rank annotation right
    rw [firstRank, secondRank, Nat.add_comm]

/-- A strictly smaller actual request cannot equal the ancestor's sorted numeric pair. -/
theorem strict_pair_ne (annotation : Guard → Prop) (source : State Symbol Guard) (facts : Facts source)
    (domain : DomainKey) (bindings : Bindings annotation source domain)
    (first second left right : Value Symbol Guard)
    (firstAvailable : Available source first) (secondAvailable : Available source second)
    (leftAvailable : Available source left) (rightAvailable : Available source right)
    (firstCovered : Covered domain first) (secondCovered : Covered domain second)
    (leftCovered : Covered domain left) (rightCovered : Covered domain right)
    (firstNumber secondNumber leftNumber rightNumber : Nat)
    (firstId : identity first = some firstNumber) (secondId : identity second = some secondNumber)
    (leftId : identity left = some leftNumber) (rightId : identity right = some rightNumber)
    (smaller : pairRank annotation first second < pairRank annotation left right) :
    pair firstNumber secondNumber ≠ pair leftNumber rightNumber := by
  intro same
  have equal := same_pair_rank annotation source facts domain bindings first second left right
    firstAvailable secondAvailable leftAvailable rightAvailable firstCovered secondCovered leftCovered rightCovered
    firstNumber secondNumber leftNumber rightNumber firstId secondId leftId rightId same
  omega

end MicroCFTA.SourceCurrentConstrainedCapNativePairRank
