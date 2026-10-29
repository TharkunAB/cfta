import MicroCFTA.SourcePruningEnumerationStorageProgress
import MicroCFTA.SourcePruningRecordTypes

/-!
# Chosen-term cost through the actual recording callback

Path compression retains every stored slot.
The recording callback therefore retains the pending constructor count.
This is a neutral step and does not establish recursive progress.
-/
namespace MicroCFTA.EnumerationStorageProgress
open Language EnumerationState
variable {Symbol Guard : Type}

/-- A complete compression frame retains the pending constructor count. -/
theorem frame_pendingSize (before after : State Symbol Guard)
    (assignment : Nat → Term Symbol) (frame : EnumerationCompressionFrame.Frame before after) :
    pendingSize after assignment = pendingSize before assignment := by
  unfold pendingSize
  rw [frame.values]

end MicroCFTA.EnumerationStorageProgress

namespace MicroCFTA.SourcePruningEnumerationStorageProgress
open Language Fragments EnumerationState EnumerationCorrectness EnumerationStorageProgress
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {Guard Typing : Type}

/-- The actual successful recording callback retains the chosen-term cost. -/
theorem recordTypes_pendingSize
    (graph : Graph Symbol Guard) (templates : List (Template.Pattern Symbol))
    (fuel : Nat) (metadata : SourcePruningRecordTypes.Metadata Typing) (uv : Nat)
    (input : Sum (Fragment Symbol) Nat) (before after : State Symbol Guard)
    (result : Bool × SourcePruningRecordTypes.Metadata Typing)
    (assignment : Nat → Term Symbol) (total : UnionFind.Total before.representatives)
    (success : Success (SourcePruningRecordTypes.recordTypes graph templates fuel metadata uv input)
      before result after) :
    pendingSize after assignment = pendingSize before assignment :=
  frame_pendingSize before after assignment
    (SourcePruningRecordTypes.recordTypes_frame graph templates fuel metadata uv input before after result total success)

end MicroCFTA.SourcePruningEnumerationStorageProgress
