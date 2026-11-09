import MicroCFTA.SourcePruningEnumerationSharedIncomingReservation
import MicroCFTA.SourceCurrentConstrainedCapGeneratedQueryResources

/-!
# Conservative padding within one actual shared query schedule

Later positions retain the guards of earlier positions in the SAME schedule.
The existing numeric comparison and this guard inclusion transport a reached
resource packet to an unused suffix. No numeric comparison follows from guard
inclusion between unrelated schedules.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedIncomingReservation
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Heap" => SourceEqualityAnnotationHeap.Heap

/-- A later position retains every guard of an earlier position of the same schedule. -/
theorem advance_count_alphabet_mono (seed : Seed) {first last : Nat} (counts : first ≤ last) :
    (advance seed first).1 ⊆ (advance seed last).1 := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le counts
  rw [advance_add]
  exact advance_alphabet_ge (advance seed first) extra

/-- A reached resource packet fits every later position of its original schedule. -/
theorem resources_at_later_count {width : Nat} (seed : Seed) {first last : Nat}
    (counts : first ≤ last) (checked : SourceEqualityNativeDemand.State width)
    (fits : Fits (advance seed first).2 checked)
    (known : Heap (fun guard => guard ∈ (advance seed first).1) checked.native.machine.heap) :
    Fits (advance seed last).2 checked ∧
      Heap (fun guard => guard ∈ (advance seed last).1) checked.native.machine.heap := by
  refine ⟨fits.mono (advance_count_profile_mono seed counts), ?_⟩
  intro key edge found
  exact advance_count_alphabet_mono seed counts (known key edge found)

end MicroCFTA.SourcePruningEnumerationSharedIncomingReservation
