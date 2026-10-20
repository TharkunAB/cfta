import MicroCFTA.SourceRecursiveIntersectionThunks
import MicroCFTA.SourceRecursiveIntersectionControl

/-!
# Complete operand identities exclude the direct-query branch

This snippet uses only the value codec and actual request-key definition.
It assumes no physical cache, execution, word-safety or compiler-owner law.
-/
namespace MicroCFTA.NativeOwnerKeyExclusion
open InternedConstructorTemplates SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionControl (identity)

private theorem identity_input (value : Value Symbol Guard) (name : Nat)
    (named : identity value = some name) :
    ∃ input, IntersectionFlatMemoKey.input value.referenceOf = some input := by
  cases value with
  | reference reference => cases reference <;> simp_all [identity,Value.referenceOf,IntersectionFlatMemoKey.input]
  | empty | node | mu | union => simp_all [identity,Value.referenceOf,IntersectionFlatMemoKey.input]

/-- An unresolved query key excludes a pair of complete source operand identities. -/
theorem no_identity_pair (width : Nat) (request : NodeRequest Symbol Guard)
    (missing : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = none)
    (first second : Nat) (left : identity request.left = some first) (right : identity request.right = some second) : False := by
  obtain ⟨leftInput,leftCodec⟩ := identity_input request.left first left
  obtain ⟨rightInput,rightCodec⟩ := identity_input request.right second right
  have complete := IntersectionFlatMemoKeyDomain.sourceKey_complete width request.domain _ _
    leftInput rightInput leftCodec rightCodec
  change IntersectionFlatMemoKeyDomain.sourceKey width request.domain request.left.referenceOf request.right.referenceOf = none at missing
  rw [complete] at missing
  cases missing

end MicroCFTA.NativeOwnerKeyExclusion

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.NativeOwnerKeyExclusion.no_identity_pair
#print MicroCFTA.NativeOwnerKeyExclusion.no_identity_pair
#print axioms MicroCFTA.NativeOwnerKeyExclusion.no_identity_pair
