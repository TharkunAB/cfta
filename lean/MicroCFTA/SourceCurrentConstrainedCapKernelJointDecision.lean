import MicroCFTA.SourceCurrentConstrainedCapKernelJoint
import MicroCFTA.SourceCurrentConstrainedCapNativePairWeight

/-!
# Exact repeated-pair weights and closed reset inputs

The actual decision determines the two numeric operand identities before
it selects a repeated pair. A reset requires both actual free fields to
be empty. These facts retain the complete original input contract.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapKernelJointDecision
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionThunks
open SourceCurrentConstrainedCapNativeOccurrenceCache (OriginalBindings NodeInputs)
open SourceCurrentConstrainedCapNativeIdentity (Covered)
variable {Symbol Guard : Type}

private theorem payload_not_repeated (left right : Value Symbol Guard) (key : Nat × Nat) :
    payload left right ≠ .repeated key := by
  cases left <;> cases right <;> simp [payload]

private theorem payload_not_reset (left right : Value Symbol Guard) : payload left right ≠ .reset := by
  cases left <;> cases right <;> simp [payload]

/-- A selected repeated pair has the exact immutable source weight of its actual operand identities. -/
theorem repeated_weight (annotation : Guard → Prop) (source : State Symbol Guard) (facts : Facts source)
    (domain : Interned DomainKey) (left right : Value Symbol Guard)
    (bindings : OriginalBindings annotation source domain.key) (inputs : NodeInputs source ⟨domain, left, right⟩)
    (key : Nat × Nat) (selected : decision domain.key left right = .repeated key) :
    SourceCurrentConstrainedCapPairOccurrences.sourceWeight annotation source (.intersection key.1 key.2) =
      SourceCurrentConstrainedCapNonplainRank.pairRank annotation left right := by
  unfold decision at selected
  split at selected
  · cases selected
  · split at selected
    · cases selected
    · split at selected
      · cases selected
      · split at selected
        · cases selected
        · cases firstFound : identity left with
          | none => simp only [firstFound] at selected; cases selected
          | some first =>
              cases secondFound : identity right with
              | none => simp only [firstFound, secondFound] at selected; cases selected
              | some second =>
                  simp only [firstFound, secondFound] at selected
                  split at selected
                  · have same := Branch.repeated.inj selected
                    subst key
                    exact SourceCurrentConstrainedCapNativePairWeight.pair_weight annotation source facts domain.key
                      bindings.annotated left right inputs.2.2.1 inputs.2.2.2.1 inputs.2.2.2.2.1 inputs.2.2.2.2.2
                      first second firstFound secondFound
                  · exact False.elim (payload_not_repeated left right key selected)

/-- Actual reset selection derives empty-domain coverage from both literal closed free fields. -/
theorem reset_inputs (source : State Symbol Guard) (domain : Interned DomainKey) (left right : Value Symbol Guard)
    (inputs : NodeInputs source ⟨domain, left, right⟩) (selected : decision domain.key left right = .reset) :
    NodeInputs source ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ := by
  have closed : left.free = [] ∧ right.free = [] := by
    unfold decision at selected
    split at selected
    · cases selected
    · split at selected
      · rename_i actualReset
        have fields := actualReset
        simp only [reset, Bool.and_eq_true] at fields
        exact ⟨List.isEmpty_iff.mp fields.1.1, List.isEmpty_iff.mp fields.1.2⟩
      · split at selected
        · cases selected
        · split at selected
          · cases selected
          · cases firstFound : identity left with
            | none => simp only [firstFound] at selected; cases selected
            | some first =>
                cases secondFound : identity right with
                | none => simp only [firstFound, secondFound] at selected; cases selected
                | some second =>
                    simp only [firstFound, secondFound] at selected
                    split at selected
                    · cases selected
                    · exact False.elim (payload_not_reset left right selected)
  exact ⟨inputs.1, inputs.2.1, inputs.2.2.1, inputs.2.2.2.1,
    Covered.closed _ left closed.1, Covered.closed _ right closed.2⟩

end MicroCFTA.SourceCurrentConstrainedCapKernelJointDecision
