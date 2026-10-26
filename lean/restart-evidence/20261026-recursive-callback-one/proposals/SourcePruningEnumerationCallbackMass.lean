import MicroCFTA.SourcePruningEnumerationExpansionAdmission

namespace MicroCFTA.SourcePruningEnumerationPrefixAdmission
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Core" => EnumerationState.State Symbol Constraint

/-- Equal stored slots retain the complete pending-bucket mass, including repeated entries. -/
theorem suspendedBound_values (before after : Core) (values : after.values = before.values) :
    suspendedBound after = suspendedBound before := by
  simp only [suspendedBound, values]

end MicroCFTA.SourcePruningEnumerationPrefixAdmission

namespace MicroCFTA.SourcePruningEnumerationExpansionAdmission
open SourcePruningEnumerationIncomingReservation (Seed Reserved)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Core" => EnumerationState.State Symbol Constraint

/-- Equal stored slots retain the expansion count fixed at the original native seed. -/
theorem count_values (seed : Seed) (before after : Core) (values : after.values = before.values) :
    count seed after = count seed before := by
  unfold count
  rw [SourcePruningEnumerationPrefixAdmission.suspendedBound_values before after values]

/-- The original reservation applies after a callback that retains every stored slot. -/
theorem reserved_values (bits : Nat) (seed : Seed) (before after : Core)
    (values : after.values = before.values)
    (reserved : Reserved bits (narrowSeed seed) (count seed before)) :
    Reserved bits (narrowSeed seed) (count seed after) := by
  rw [count_values seed before after values]
  exact reserved

end MicroCFTA.SourcePruningEnumerationExpansionAdmission
