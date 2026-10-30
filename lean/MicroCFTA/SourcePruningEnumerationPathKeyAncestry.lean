import MicroCFTA.SourcePruningEnumerationPathKeyShapes
import MicroCFTA.SourcePruningEnumerationKeyAncestry

/-!
# Actual entry preserves the finite path carrier of historical keys

The input cache supplies the finite path carrier and valid stored tries.
The proof covers the actual entry and both ancestry stores.
The theorem does not bound native handles or recursive work.
-/
namespace MicroCFTA.SourcePruningEnumerationPathKeyAncestry
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationValidity
open InternedConstructorTemplates SourcePruningEnumerationKeyAncestry
open SourcePruningEnumerationPathTransport SourcePruningEnumerationEntry
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}
attribute [local instance] entryMonadList

/-- Every historical key after actual entry retains the finite original path shape. -/
theorem enter_key_ancestry
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (fuel uv : Nat)
    (before after : EnumerationState.State Symbol EnumGuard) (target handle : Nat)
    (bucket : List Suspended) (decoded : Value Symbol NativeGuard)
    (domain : List EqualityTrie.Path) (paths : StatePaths (fun p => p ∈ domain) before)
    (canonical : Canonical before)
    (bounded : KeyAncestry (SourcePruningEnumerationPathKeyShapes.keyShapes domain) before)
    (success : Success (enter heap fuel uv) before (target, handle, bucket, decoded) after) :
    KeyAncestry (SourcePruningEnumerationPathKeyShapes.keyShapes domain) after := by
  unfold enter at success
  obtain ⟨value, read, reading, continued⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨_readFound, _lookup, stored, readSame⟩ :=
    (getValue_success fuel uv before read value).mp reading
  have readBounded : KeyAncestry (SourcePruningEnumerationPathKeyShapes.keyShapes domain) read := by
    rw [readSame]
    exact bounded
  cases value with
  | enumerated fragment => exact (reject_unsuccessful read after _ continued).elim
  | eliminated => exact (reject_unsuccessful read after _ continued).elim
  | unenumerated node scs =>
      cases node with
      | none => exact (reject_unsuccessful read after _ continued).elim
      | some storedHandle =>
          have inserted := SourcePruningEnumerationPathKeyShapes.stored_recursion_key_mem
            domain before paths canonical stored
          obtain ⟨found, compressed, compressing, continued⟩ := (success_bind _ _ _ _ _).mp continued
          obtain ⟨_resolved, _resolving, _sameRoot, compressedSame⟩ :=
            (representative_success fuel uv read compressed found).mp compressing
          have compressedBounded : KeyAncestry
              (SourcePruningEnumerationPathKeyShapes.keyShapes domain) compressed := by
            rw [compressedSame]
            exact readBounded
          cases lookup : SourcePruningEnumerationNodes.lookupNode heap storedHandle with
          | none =>
              simp only [lookup] at continued
              exact (success_failure .unresolvedReference compressed after _ continued).elim
          | some actual =>
              simp only [lookup] at continued
              obtain ⟨ignored, entered, modifying, final⟩ := (success_bind _ _ _ _ _).mp continued
              cases ignored
              obtain rfl := (EnumerationDriver.modify_success _ compressed entered).mp modifying
              obtain ⟨_same, rfl⟩ := (success_pure _ _ _ _).mp final
              refine ⟨compressedBounded.1, ?_⟩
              intro key member
              change key ∈ (if MergedOrdinaryHeight.recursiveBoundary actual then
                (recursionKey storedHandle scs :: compressed.recursionAncestry found).eraseDups
                else compressed.recursionAncestry found) at member
              by_cases boundary : MergedOrdinaryHeight.recursiveBoundary actual = true
              · simp only [ite_eq_left boundary, List.mem_eraseDups, List.mem_cons] at member
                rcases member with same | old
                · subst key
                  exact inserted
                · exact compressedBounded.1 found key old
              · exact compressedBounded.1 found key (by
                  simpa only [ite_eq_right boundary] using member)

end MicroCFTA.SourcePruningEnumerationPathKeyAncestry
