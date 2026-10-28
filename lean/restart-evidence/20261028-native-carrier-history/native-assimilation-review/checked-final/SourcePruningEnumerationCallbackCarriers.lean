import MicroCFTA.SourcePruningRecordTypes
import MicroCFTA.SourcePruningEnumerationCarrierFrame

/-!
# Graph provenance through actual callback recording

The actual callback receipt supplies a complete compression frame.
Both Boolean results retain the same graph carriers and stored references.
-/
namespace MicroCFTA.SourcePruningRecordTypes
open EnumerationState EnumerationCorrectness EnumerationCompressionFrame
open EnumerationCarriers EnumerationGraphReferences
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {Guard Typing : Type}

/-- Every successful callback record retains graph carriers and stored references. -/
theorem recordTypes_carriers
    (graph : Graph Symbol Guard) (templates : List (Template.Pattern Symbol))
    (fuel : Nat) (metadata : Metadata Typing) (uv : Nat) (input : Sum (Fragments.Fragment Symbol) Nat)
    (before after : State Symbol Guard) (result : Bool × Metadata Typing)
    (total : UnionFind.Total before.representatives) (references : ReferencesCarry before)
    (observed : Success (recordTypes graph templates fuel metadata uv input) before result after) :
    UnionFind.Total after.representatives ∧ PreservesCarriers before after ∧ ReferencesCarry after := by
  have frame := recordTypes_frame graph templates fuel metadata uv input before after result total observed
  exact ⟨frame.total total, frame.carriers, frame.references references⟩

end MicroCFTA.SourcePruningRecordTypes
