import MicroCFTA.SourcePruningEnumerationEntry
import MicroCFTA.EnumerationValidity

/-!
# Canonical inherited tries at actual pending entry

The actual read supplies its stored bucket.
Compression and ancestry changes retain that bucket and the stored trie invariant.
-/
namespace MicroCFTA.SourcePruningEnumerationEntry
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationValidity
open EnumerationSemantics InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}
attribute [local instance] entryMonadList

/-- Successful entry retains canonical storage and derives validity of its actual inherited bucket. -/
theorem enter_canonical
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (fuel uv : Nat)
    (before after : EnumerationState.State Symbol EnumGuard) (target handle : Nat)
    (bucket : List Suspended) (decoded : Value Symbol NativeGuard)
    (canonical : Canonical before)
    (success : Success (enter heap fuel uv) before (target, handle, bucket, decoded) after) :
    Canonical after ∧ ValidSuspended bucket := by
  unfold enter at success
  obtain ⟨value, read, reading, continued⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨readCanonical, storedValid⟩ := getValue_canonical fuel uv before read value canonical reading
  cases value with
  | enumerated fragment => exact (reject_unsuccessful read after _ continued).elim
  | eliminated => exact (reject_unsuccessful read after _ continued).elim
  | unenumerated node scs =>
      cases node with
      | none => exact (reject_unsuccessful read after _ continued).elim
      | some storedHandle =>
          obtain ⟨found, compressed, compressing, continued⟩ := (success_bind _ _ _ _ _).mp continued
          have compressedCanonical := representative_canonical fuel uv found read compressed readCanonical compressing
          cases lookup : SourcePruningEnumerationNodes.lookupNode heap storedHandle with
          | none =>
              simp only [lookup] at continued
              exact (success_failure .unresolvedReference compressed after _ continued).elim
          | some actual =>
              simp only [lookup] at continued
              obtain ⟨ignored, entered, modifying, final⟩ := (success_bind _ _ _ _ _).mp continued
              cases ignored
              obtain rfl := (EnumerationDriver.modify_success _ compressed entered).mp modifying
              obtain ⟨same, rfl⟩ := (success_pure _ _ _ _).mp final
              have bucketSame : scs = bucket :=
                (congrArg (fun packet : Nat × Nat × List Suspended × Value Symbol NativeGuard => packet.2.2.1) same).symm
              change ValidSuspended scs at storedValid
              exact ⟨compressedCanonical, by simpa only [← bucketSame] using storedValid⟩

end MicroCFTA.SourcePruningEnumerationEntry
