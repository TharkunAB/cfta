import MicroCFTA.SourcePruningEnumerationExpansionAdmission

/-!
# Reservations from an upper bound on suspended mass

The upper bound can be fixed before an edge returns its cache. A smaller
actual mass uses a prefix of the same incoming-query reservation.
-/
namespace MicroCFTA.SourcePruningEnumerationOriginalForecast
open SourcePruningEnumerationIncomingReservation (Seed)

/-- A larger inherited bucket bound covers the same original scan. -/
theorem count_mono (seed : Seed) {first last : Nat} (bounded : first ≤ last) :
    count seed first ≤ count seed last := by
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.add_le_add_right bounded _) 1)

end MicroCFTA.SourcePruningEnumerationOriginalForecast

namespace MicroCFTA.SourcePruningEnumerationExpansionAdmission
open SourcePruningEnumerationIncomingReservation (Seed Reserved)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Core" => EnumerationState.State Symbol Constraint

/-- An original mass ceiling bounds the count at the actual returned cache. -/
theorem count_le_mass (seed : Seed) (before : Core) (ceiling : Nat)
    (bounded : SourcePruningEnumerationPrefixAdmission.suspendedBound before ≤ ceiling) :
    count seed before ≤ SourcePruningEnumerationOriginalForecast.count (narrowSeed seed) ceiling :=
  SourcePruningEnumerationOriginalForecast.count_mono (narrowSeed seed) bounded

/-- A reservation at the original mass ceiling pays the actual smaller scan. -/
theorem reserved_of_mass (bits : Nat) (seed : Seed) (before : Core) (ceiling : Nat)
    (bounded : SourcePruningEnumerationPrefixAdmission.suspendedBound before ≤ ceiling)
    (reserved : Reserved bits (narrowSeed seed)
      (SourcePruningEnumerationOriginalForecast.count (narrowSeed seed) ceiling)) :
    Reserved bits (narrowSeed seed) (count seed before) :=
  reserved.prefix (count_le_mass seed before ceiling bounded)

end MicroCFTA.SourcePruningEnumerationExpansionAdmission

namespace MicroCFTA.SourcePruningEnumerationIncomingReservation

/-- A later entry of the same schedule retains the guards at every earlier entry. -/
theorem advance_count_alphabet_mono (seed : Seed) {first last : Nat} (counts : first ≤ last) :
    (advance seed first).1 ⊆ (advance seed last).1 := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le counts
  rw [advance_add]
  exact advance_alphabet_ge (advance seed first) extra

end MicroCFTA.SourcePruningEnumerationIncomingReservation
