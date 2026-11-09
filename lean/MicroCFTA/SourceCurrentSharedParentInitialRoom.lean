import MicroCFTA.SourceCurrentSharedParentUniformEnvelope
import MicroCFTA.SourceCurrentParentInitialRoom

/-!
# Finite initial room for resident Parent requests

The complete class profile bounds every native query entry. A finite join
of those profiles supplies one room test for the initial guard alphabet.
The computed width is mathematical. It does not assert room at host64.
-/
namespace MicroCFTA.SourceCurrentSharedParentInitialRoom
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Room at the final Scan profile reserves every predicted native query. -/
theorem scan_reserved_of_room (bits budget count : Nat) (classes : EqualityNormalize.Constraints)
    (alphabet : List Guard) (profile : Profile)
    (room : Room bits (SourceCurrentSharedScanNumericForecast.schedule budget count classes alphabet profile).2) :
    SourceCurrentSharedScanNumericForecast.Reserved bits budget count classes alphabet profile := by
  induction classes generalizing alphabet profile with
  | nil => trivial
  | cons paths classes ih =>
      have firstRoom := room.mono
        (SourceCurrentSharedScanNumericForecast.schedule_profile_ge budget count classes
          (SourceCurrentSharedScanNumericForecast.classStep budget count paths alphabet profile).1
          (SourceCurrentSharedScanNumericForecast.classStep budget count paths alphabet profile).2)
      have queryRoom := firstRoom.mono
        (SourceCurrentSharedScanNumericForecast.memoProfile_ge
          (SourceCurrentSeededGuardForecast.finalAlphabet alphabet count (paths.map (List.map Int.ofNat))
            (SourceCurrentGateFrameResources.forecast paths (SourceCurrentGateFrameResources.forecast paths profile)))
          budget (SourceCurrentConstrainedCapSeededForecast.finalProfile count (paths.map (List.map Int.ofNat))
            (SourceCurrentGateFrameResources.forecast paths (SourceCurrentGateFrameResources.forecast paths profile))))
      refine ⟨?_, ih _ _ room⟩
      cases paths with
      | nil => trivial
      | cons seed rest =>
          exact SourceCurrentConstrainedCapSeededForecast.reserved_of_final_room bits count (seed.map Int.ofNat)
            (rest.map (List.map Int.ofNat)) _ queryRoom

/-- One final class room test covers Scan and every selected continuation. -/
theorem classes_reserved_of_room (bits budget count : Nat) (records : List SourceEqualityClassOrder.Record)
    (alphabet : List Guard) (profile : Profile)
    (room : Room bits (SourceCurrentSharedClassesForecast.finalProfile budget count records alphabet profile)) :
    SourceCurrentSharedClassesForecast.Reserved bits budget count records alphabet profile := by
  have preparation := room.mono (SourceCurrentSharedClassesForecast.preparation_le budget count records alphabet profile)
  have scanRoom := preparation.mono (SourceCurrentSharedScanRequiredForecast.scan_le budget count records alphabet profile)
  refine ⟨scan_reserved_of_room bits budget count (records.map SourceEqualityClassOrder.Record.paths)
    alphabet profile scanRoom, ?_⟩
  cases records with
  | nil => trivial
  | cons record records => exact room

export SourceCurrentParentInitialRoom (roomBits room_computed)

/-- One initial room test reserves every finite own-record, child-count and ambient case. -/
theorem uniform_of_room (bits budget : Nat) (alphabet : List Guard) (profile : Profile)
    (room : Room bits (SourceCurrentSharedParentUniformEnvelope.classesProfile budget alphabet profile)) :
    SourceCurrentSharedParentAlphabetReservation.UniformReserved bits budget alphabet profile := by
  intro records selected count included ambient present
  have bounds := SourceCurrentSharedParentUniformEnvelope.case_bounds budget alphabet profile records selected count
    (by have less := List.mem_range.mp included; omega) ambient present
  exact classes_reserved_of_room bits budget count records ambient profile (room.mono bounds.1)

/-- The computed initial width supplies the complete finite Parent reservation. -/
theorem uniform_computed (budget : Nat) (alphabet : List Guard) (profile : Profile) :
    SourceCurrentSharedParentAlphabetReservation.UniformReserved
      (roomBits (SourceCurrentSharedParentUniformEnvelope.classesProfile budget alphabet profile)) budget alphabet profile :=
  uniform_of_room _ budget alphabet profile (room_computed _)

end MicroCFTA.SourceCurrentSharedParentInitialRoom
