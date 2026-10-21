import MicroCFTA.SourceCurrentOuterRankEnvelope
import MicroCFTA.SourceCurrentOuterInitialFuel
import MicroCFTA.SourceCurrentParentInitialRoom
import Init.Data.List.Range
import Init.Data.List.Lemmas

/-!
# Finite-round initial forecasts

Each stage covers every count and mass pair at its exact entry seed.
The final profile computes one mathematical width for all selected cases.
These numeric bounds do not assert a caller execution or a next warm packet.
-/
namespace MicroCFTA.SourceCurrentFiniteRoundForecast
open SourceCurrentAllocatedNativeResourceForecast (Profile Le Room)
open SourceCurrentInitialSelectionForecast (cover maximum)
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Seed" => List Guard × Profile
local notation "C" => SourceCurrentOuterRankEnvelope.envelope
local notation "nodeNeed" => SourceCurrentOuterInitialFuel.nodeNeed
local notation "roomBits" => SourceCurrentParentInitialRoom.roomBits

private def grid (entry : Seed) : List (Nat × Nat) :=
  (List.range (entry.2.mass + 1)).flatMap fun count =>
    (List.range (entry.2.mass + 1)).map fun mass => (count,mass)

private theorem grid_member (entry : Seed) (count mass : Nat)
    (counts : count ≤ entry.2.mass) (masses : mass ≤ entry.2.mass) :
    (count,mass) ∈ grid entry := by
  exact List.mem_flatMap.mpr ⟨count, List.mem_range.mpr (by omega),
    List.mem_map.mpr ⟨mass, List.mem_range.mpr (by omega), rfl⟩⟩

private noncomputable def caseSeed (budget count mass : Nat) (entry : Seed) : Seed :=
  let output := C budget count mass entry
  let scheduled := SourceCurrentOuterInitialSchedule.node output.1 budget entry
  (output.2.2.1 ++ scheduled.1, cover [output.2.2.2] scheduled.2)

private noncomputable def caseSeeds (budget : Nat) (entry : Seed) : List Seed :=
  (grid entry).map fun rank => caseSeed budget rank.1 rank.2 entry

private noncomputable def next (budget : Nat) (entry : Seed) : Seed :=
  (entry.1 ++ (caseSeeds budget entry).flatMap Prod.fst,
    cover ((caseSeeds budget entry).map Prod.snd) entry.2)

private theorem next_retains (budget : Nat) (entry : Seed) :
    Le entry.2 (next budget entry).2 ∧ entry.1 ⊆ (next budget entry).1 := by
  exact ⟨SourceCurrentInitialSelectionForecast.cover_ge _ _,
    fun _ member => List.mem_append_left _ member⟩

private theorem next_case (budget count mass : Nat) (entry : Seed)
    (counts : count ≤ entry.2.mass) (masses : mass ≤ entry.2.mass) :
    Le (caseSeed budget count mass entry).2 (next budget entry).2 ∧
      (caseSeed budget count mass entry).1 ⊆ (next budget entry).1 := by
  have member : caseSeed budget count mass entry ∈ caseSeeds budget entry :=
    List.mem_map.mpr ⟨(count,mass), grid_member entry count mass counts masses, rfl⟩
  refine ⟨SourceCurrentInitialSelectionForecast.cover_member entry.2
    (List.mem_map.mpr ⟨_, member, rfl⟩), ?_⟩
  intro guard present
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, member, present⟩)

/-- Join all case forecasts at each exact stage entry before choosing a width. -/
noncomputable def stage (budget : Nat) (initial : List Guard × Profile)
    (rounds : Nat) : List Guard × Profile :=
  Nat.rec initial (fun _ entry => next budget entry) rounds

private theorem stage_succ (budget : Nat) (initial : Seed) (index : Nat) :
    stage budget initial (index + 1) = next budget (stage budget initial index) := rfl

private theorem stage_retains (budget : Nat) (initial : Seed) {index rounds : Nat}
    (bound : index ≤ rounds) :
    Le (stage budget initial index).2 (stage budget initial rounds).2 ∧
      (stage budget initial index).1 ⊆ (stage budget initial rounds).1 := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le bound
  clear bound
  induction extra with
  | zero => exact ⟨Le.refl _, fun _ member => member⟩
  | succ extra ih =>
      have last := next_retains budget (stage budget initial (index + extra))
      rw [Nat.add_succ, stage_succ]
      exact ⟨ih.1.trans last.1, fun _ member => last.2 (ih.2 member)⟩

private noncomputable def boundsImage (budget rounds : Nat) (initial : Seed) :
    List (Nat × Nat) :=
  (List.range rounds).flatMap fun index =>
    let entry := stage budget initial index
    (grid entry).map fun rank =>
      let output := C budget rank.1 rank.2 entry
      (output.1, nodeNeed output.1 budget entry)

/-- Compute common outer and nine-stage lower-fuel ceilings for all finite cases. -/
noncomputable def fuelBounds (budget rounds : Nat)
    (initial : List Guard × Profile) : Nat × Nat :=
  (maximum ((boundsImage budget rounds initial).map Prod.fst),
    maximum ((boundsImage budget rounds initial).map Prod.snd))

private theorem fuel_member (budget rounds : Nat) (initial : Seed)
    {index count mass : Nat} (included : index < rounds)
    (counts : count ≤ (stage budget initial index).2.mass)
    (masses : mass ≤ (stage budget initial index).2.mass) :
    let entry := stage budget initial index
    let output := C budget count mass entry
    (output.1, nodeNeed output.1 budget entry) ∈ boundsImage budget rounds initial := by
  exact List.mem_flatMap.mpr ⟨index, List.mem_range.mpr included,
    List.mem_map.mpr ⟨(count,mass), grid_member _ count mass counts masses, rfl⟩⟩

private theorem fuel_limits (budget rounds : Nat) (initial : Seed)
    {index count mass : Nat} (included : index < rounds)
    (counts : count ≤ (stage budget initial index).2.mass)
    (masses : mass ≤ (stage budget initial index).2.mass) :
    let entry := stage budget initial index
    let output := C budget count mass entry
    output.1 ≤ (fuelBounds budget rounds initial).1 ∧
      nodeNeed output.1 budget entry ≤ (fuelBounds budget rounds initial).2 := by
  have member := fuel_member budget rounds initial included counts masses
  exact ⟨SourceCurrentInitialSelectionForecast.maximum_member
      (List.mem_map.mpr ⟨_, member, rfl⟩),
    SourceCurrentInitialSelectionForecast.maximum_member
      (List.mem_map.mpr ⟨_, member, rfl⟩)⟩

/-- Every bounded stage case has final room, alphabet coverage and common fuel bounds. -/
theorem stage_bounds (budget rounds : Nat) (initial : List Guard × Profile) :
    let final := stage budget initial rounds
    let bits := roomBits final.2
    (∀ index, index ≤ rounds →
      Le (stage budget initial index).2 final.2 ∧
        (stage budget initial index).1 ⊆ final.1) ∧
    ∀ index, index < rounds →
      let entry := stage budget initial index
      ∀ count mass, count ≤ entry.2.mass → mass ≤ entry.2.mass →
        let output := C budget count mass entry
        let scheduled := SourceCurrentOuterInitialSchedule.node output.1 budget entry
        let joined : List Guard × Profile :=
          (output.2.2.1 ++ scheduled.1, cover [output.2.2.2] scheduled.2)
        Le joined.2 final.2 ∧ joined.1 ⊆ final.1 ∧ Room bits joined.2 ∧
          output.1 ≤ (fuelBounds budget rounds initial).1 ∧
          SourceCurrentOuterInitialFuel.nodeNeed output.1 budget entry ≤
            (fuelBounds budget rounds initial).2
 := by
  dsimp only
  refine ⟨fun index bound => stage_retains budget initial bound, ?_⟩
  intro index included
  intro count mass counts masses
  let entry := stage budget initial index
  let joined := caseSeed budget count mass entry
  have first := next_case budget count mass entry counts masses
  have later := stage_retains budget initial (show index + 1 ≤ rounds by omega)
  rw [stage_succ] at later
  have profile : Le joined.2 (stage budget initial rounds).2 := first.1.trans later.1
  have alphabet : joined.1 ⊆ (stage budget initial rounds).1 :=
    fun _ member => later.2 (first.2 member)
  have room := SourceCurrentParentInitialRoom.room_computed (stage budget initial rounds).2
  have fuels := fuel_limits budget rounds initial included counts masses
  change Le joined.2 (stage budget initial rounds).2 ∧
    joined.1 ⊆ (stage budget initial rounds).1 ∧
    Room (roomBits (stage budget initial rounds).2) joined.2 ∧
    (C budget count mass entry).1 ≤ (fuelBounds budget rounds initial).1 ∧
    nodeNeed (C budget count mass entry).1 budget entry ≤ (fuelBounds budget rounds initial).2
  exact ⟨profile, alphabet, room.mono profile, fuels.1, fuels.2⟩

end MicroCFTA.SourceCurrentFiniteRoundForecast
