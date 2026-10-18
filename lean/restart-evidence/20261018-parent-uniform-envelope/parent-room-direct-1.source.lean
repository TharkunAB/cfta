import MicroCFTA.SourceCurrentParentAlphabetReservation

/-!
# Finite initial room for resident Parent requests

The complete class profile bounds every native query entry. A finite join
of those profiles supplies one room test for the initial guard alphabet.
The computed width is mathematical. It does not assert room at host64.
-/
namespace MicroCFTA.SourceCurrentParentInitialRoom
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Room at the final Scan profile reserves every predicted native query. -/
theorem scan_reserved_of_room (bits budget count : Nat) (classes : EqualityNormalize.Constraints)
    (alphabet : List Guard) (profile : Profile)
    (room : Room bits (SourceCurrentScanNumericForecast.schedule budget count classes alphabet profile).2) :
    SourceCurrentScanNumericForecast.Reserved bits budget count classes alphabet profile := by
  induction classes generalizing alphabet profile with
  | nil => trivial
  | cons paths classes ih =>
      have firstRoom := room.mono
        (SourceCurrentScanNumericForecast.schedule_profile_ge budget count classes
          (SourceCurrentScanNumericForecast.classStep budget count paths alphabet profile).1
          (SourceCurrentScanNumericForecast.classStep budget count paths alphabet profile).2)
      have queryRoom := firstRoom.mono
        (SourceCurrentConjunctionAlphabetBounds.callerForecast_ge
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
    (room : Room bits (SourceCurrentClassesForecast.finalProfile budget count records alphabet profile)) :
    SourceCurrentClassesForecast.Reserved bits budget count records alphabet profile := by
  have preparation := room.mono (SourceCurrentClassesForecast.preparation_le budget count records alphabet profile)
  have scanRoom := preparation.mono (SourceCurrentScanRequiredForecast.scan_le budget count records alphabet profile)
  refine ⟨scan_reserved_of_room bits budget count (records.map SourceEqualityClassOrder.Record.paths)
    alphabet profile scanRoom, ?_⟩
  cases records with
  | nil => trivial
  | cons record records => exact room

private theorem power_large (n : Nat) : n < 2 ^ (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.add_assoc, Nat.pow_succ]
      omega

/-- A finite profile computes a sufficient mathematical word width. -/
def roomBits (profile : Profile) : Nat :=
  profile.nodes + profile.edges + profile.domains + 2 ^ (profile.nodes + profile.nodes * profile.nodes) + 1

/-- The computed mathematical width satisfies the exact native room predicate. -/
theorem room_computed (profile : Profile) : Room (roomBits profile) profile := by
  let total := profile.nodes + profile.edges + profile.domains + 2 ^ (profile.nodes + profile.nodes * profile.nodes)
  have large := power_large total
  have one := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show total + 1 ≤ total + 1 + 1 by omega)
  have two := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show total + 1 ≤ total + 1 + 2 by omega)
  change profile.nodes < 2 ^ (total + 1) ∧ profile.edges ≤ 2 ^ (total + 1 + 2) ∧
    profile.domains + 2 ^ (profile.nodes + profile.nodes * profile.nodes) < 2 ^ (total + 1 + 1)
  have nodes : profile.nodes ≤ total := by
    exact Nat.le_trans (Nat.le_trans (Nat.le_add_right profile.nodes profile.edges)
      (Nat.le_add_right (profile.nodes + profile.edges) profile.domains))
      (Nat.le_add_right (profile.nodes + profile.edges + profile.domains) _)
  have edges : profile.edges ≤ total := by
    exact Nat.le_trans (Nat.le_trans (Nat.le_add_left profile.edges profile.nodes)
      (Nat.le_add_right (profile.nodes + profile.edges) profile.domains))
      (Nat.le_add_right (profile.nodes + profile.edges + profile.domains) _)
  have domains : profile.domains + 2 ^ (profile.nodes + profile.nodes * profile.nodes) ≤ total :=
    Nat.add_le_add_right (Nat.le_add_left profile.domains (profile.nodes + profile.edges)) _
  exact ⟨Nat.lt_of_le_of_lt nodes large,
    Nat.le_trans edges (Nat.le_trans (Nat.le_of_lt large) two),
    Nat.lt_of_le_of_lt domains (Nat.lt_of_lt_of_le large one)⟩

end MicroCFTA.SourceCurrentParentInitialRoom
