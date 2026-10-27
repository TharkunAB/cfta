import MicroCFTA.SourcePruningEnumerationEntry
import MicroCFTA.SourcePruningRecordTypes
import MicroCFTA.SourcePruningEnumerationNativeLanguage

/-!
# Assignment laws for actual entry and callback observations

Entry changes expansion ancestry after compression. This change does not
affect assignment meaning. A successful callback supplies a full frame.
These laws consume actual observations at their own state endpoints.
-/
namespace MicroCFTA.SourcePruningEnumerationEntry
open EnumerationState EnumerationCorrectness EnumerationCompressionFrame EnumerationSchedule
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}
attribute [local instance] entryMonadList

/-- Actual entry preserves assignments, including its expansion-ancestry update. -/
theorem enter_semantics
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (fuel uv : Nat)
    (before after : EnumerationState.State Symbol EnumGuard) (target handle : Nat)
    (bucket : List Suspended) (decoded : InternedConstructorTemplates.Value Symbol NativeGuard)
    (total : UnionFind.Total before.representatives)
    (observed : Success (enter heap fuel uv) before (target, handle, bucket, decoded) after) :
    ∀ (language : NodeLanguage Symbol) (residualMeaning : EnumGuard → Language.Term Symbol → Prop)
      (assignment : Nat → Language.Term Symbol),
      Satisfies language residualMeaning assignment after ↔
        Satisfies language residualMeaning assignment before := by
  unfold enter at observed
  obtain ⟨value, read, reading, continued⟩ := (success_bind _ _ _ _ _).mp observed
  have readFrame := (getValue_frame fuel uv before read value total reading).1
  cases value with
  | enumerated fragment => exact (reject_unsuccessful read after _ continued).elim
  | eliminated => exact (reject_unsuccessful read after _ continued).elim
  | unenumerated node scs =>
      cases node with
      | none => exact (reject_unsuccessful read after _ continued).elim
      | some storedHandle =>
          obtain ⟨found, compressed, compressing, continued⟩ := (success_bind _ _ _ _ _).mp continued
          have fullFrame := readFrame.trans
            (representative_frame fuel uv found read compressed (readFrame.total total) compressing)
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
              intro language residualMeaning assignment
              change Satisfies language residualMeaning assignment compressed ↔
                Satisfies language residualMeaning assignment before
              exact SourcePruningEnumerationNativeLanguage.satisfies_frame
                language residualMeaning assignment before compressed fullFrame

end MicroCFTA.SourcePruningEnumerationEntry

namespace MicroCFTA.SourcePruningRecordTypes
open EnumerationState EnumerationCorrectness EnumerationCompressionFrame
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard Typing : Type}

/-- Every actual successful callback preserves assignments at its exact returned core. -/
theorem recordTypes_success_semantics
    (graph : Graph Symbol EnumGuard) (templates : List (Template.Pattern Symbol))
    (fuel : Nat) (metadata : Metadata Typing) (uv : Nat) (input : Sum (Fragments.Fragment Symbol) Nat)
    (before after : EnumerationState.State Symbol EnumGuard) (result : Bool × Metadata Typing)
    (total : UnionFind.Total before.representatives)
    (observed : Success (recordTypes graph templates fuel metadata uv input) before result after) :
    ∀ (language : NodeLanguage Symbol) (residualMeaning : EnumGuard → Language.Term Symbol → Prop)
      (assignment : Nat → Language.Term Symbol),
      Satisfies language residualMeaning assignment after ↔
        Satisfies language residualMeaning assignment before := by
  intro language residualMeaning assignment
  exact SourcePruningEnumerationNativeLanguage.satisfies_frame language residualMeaning assignment
    before after (recordTypes_frame graph templates fuel metadata uv input before after result total observed)

end MicroCFTA.SourcePruningRecordTypes
