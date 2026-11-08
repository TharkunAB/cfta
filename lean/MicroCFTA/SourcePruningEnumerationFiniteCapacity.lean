import MicroCFTA.SourcePruningEnumerationFiniteReservation
import MicroCFTA.SourceCurrentAllocatedNativeCreditProfile

/-!
# Final counter capacity for every recursive query reservation

The final forecast bounds the complete native step for every actual query.
Its three counter bounds supply entry instruction credit at the preceding
scheduled entry. No additional unexecuted query is reserved at the end.
All recursive, sibling and captured-head reservations use the same seeds.
-/
namespace MicroCFTA.SourcePruningEnumerationFiniteReservation
open SourceCurrentAllocatedNativeResourceForecast (Le)
open SourceCurrentAllocatedNativeCreditProfile (Capacity)
open SourcePruningEnumerationIncomingReservation (Seed)
attribute [local irreducible] SourcePruningEnumerationRecursiveReservation.afterHead
attribute [local irreducible] SourceCurrentConstrainedCapEditForecast.headProfile
local notation "afterHead" => SourcePruningEnumerationRecursiveReservation.afterHead
local notation "edgeCount" => SourcePruningEnumerationRecursiveReservation.edgeCount
local notation "massCeil" => SourcePruningEnumerationRecursiveReservation.massCeil
local notation "narrowSeed" => SourcePruningEnumerationExpansionAdmission.narrowSeed

/-- Capacity at the complete original forecast supplies every nested reservation. -/
theorem reserved_of_final_capacity (bits depth : Nat) (seed : Seed) (ceiling : Nat)
    (room : Capacity bits (final depth seed ceiling).2) : Reserved bits depth seed ceiling := by
  induction depth generalizing seed ceiling with
  | zero => exact reserved_zero bits seed ceiling
  | succ depth ih =>
      apply (reserved_succ_iff bits depth seed ceiling).mpr
      intro index less
      let current := stage depth (narrowSeed seed) ceiling ceiling index
      have later := count_mono depth (narrowSeed seed) ceiling ceiling
        (by omega : index + 1 ≤ rows seed)
      have ordered : Le (step depth current ceiling ceiling).2 (final (depth + 1) seed ceiling).2 := by
        simpa only [current, final_succ, stage_succ_right] using later.1
      have callbackCapacity : Capacity bits (step depth current ceiling ceiling).2 := room.mono ordered
      have headCapacity : Capacity bits (afterHead current ceiling).2 :=
        callbackCapacity.mono (afterHead_le_step depth current ceiling ceiling).1
      exact ⟨SourcePruningEnumerationIncomingReservation.reserved_of_final_capacity bits current
          (edgeCount current ceiling)
          (by simpa only [SourcePruningEnumerationRecursiveReservation.afterHead] using headCapacity),
        ih (afterHead current ceiling) (massCeil current ceiling ceiling) callbackCapacity⟩

/-- Capacity at one paired final forecast supplies its edge and recursive callback reservations. -/
theorem head_reserved_of_final_capacity (bits depth : Nat) (seed : Seed) (capturedMass inherited : Nat)
    (room : Capacity bits (step depth seed capturedMass inherited).2) :
    HeadReserved bits depth seed capturedMass inherited :=
  ⟨SourcePruningEnumerationIncomingReservation.reserved_of_final_capacity bits seed (edgeCount seed inherited)
      (by
        have headCapacity := room.mono (afterHead_le_step depth seed capturedMass inherited).1
        simpa only [SourcePruningEnumerationRecursiveReservation.afterHead] using headCapacity),
    reserved_of_final_capacity bits depth (afterHead seed inherited) (massCeil seed capturedMass inherited) room⟩

/-- Capacity at the scan's final entry supplies every paired reservation in its original prefix. -/
theorem scan_reserved_of_final_capacity (bits depth : Nat) (seed : Seed) (capturedMass inherited count : Nat)
    (room : Capacity bits (stage depth seed capturedMass inherited count).2) :
    ScanReserved bits depth seed capturedMass inherited count := by
  intro index less
  have later := count_mono depth seed capturedMass inherited (by omega : index + 1 ≤ count)
  apply head_reserved_of_final_capacity bits depth (stage depth seed capturedMass inherited index) capturedMass inherited
  exact room.mono (by simpa only [stage_succ_right] using later.1)


end MicroCFTA.SourcePruningEnumerationFiniteReservation
