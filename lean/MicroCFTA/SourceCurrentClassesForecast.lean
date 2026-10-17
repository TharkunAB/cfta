import MicroCFTA.SourceCurrentScanRequiredForecast

/-!
# Initial forecasts for complete local class reduction

The original records bound Scan, Required, and the later selected class
pass. The class pass starts at the joined preparation profile. No future
selection or returned forest enters the initial reservation.
-/
namespace MicroCFTA.SourceCurrentClassesForecast
open SourceCurrentAllocatedNativeResourceForecast (Profile Le)
open SourceEqualityClassOrder (Record)
namespace Preparation
export SourceCurrentScanRequiredForecast (finalProfile fuel)
end Preparation
namespace Classes
export SourceCurrentConstrainedCapClassForecast (foldProfile foldFuel Reserved)
end Classes
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- The original class fold bounds every selected continuation after preparation. -/
noncomputable def finalProfile (budget count : Nat) (records : List Record) (alphabet : List Guard)
    (entry : Profile) : Profile :=
  Classes.foldProfile records count (Preparation.finalProfile budget count records alphabet entry)

/-- The complete class forecast retains the joined preparation entry. -/
theorem preparation_le (budget count : Nat) (records : List Record) (alphabet : List Guard) (entry : Profile) :
    Le (Preparation.finalProfile budget count records alphabet entry) (finalProfile budget count records alphabet entry) :=
  SourceCurrentConstrainedCapClassForecast.fold_ge _ _ _

/-- One initial ceiling covers all nine independently larger local class fuels. -/
noncomputable def fuel (budget count : Nat) (records : List Record) (alphabet : List Guard) (entry : Profile) : Nat :=
  max (Preparation.fuel budget count records alphabet entry)
    (Classes.foldFuel records count (Preparation.finalProfile budget count records alphabet entry))

/-- The common class ceiling supplies the complete preparation. -/
theorem preparation_fuel (budget count : Nat) (records : List Record) (alphabet : List Guard) (entry : Profile) :
    Preparation.fuel budget count records alphabet entry ≤ fuel budget count records alphabet entry :=
  Nat.le_max_left _ _

/-- Every positional selected class pass fits the original common ceiling. -/
theorem class_fuel {records kept : List Record} (selected : kept.Sublist records)
    (budget count : Nat) (alphabet : List Guard) (entry : Profile) :
    Classes.foldFuel kept count (Preparation.finalProfile budget count records alphabet entry) ≤
      fuel budget count records alphabet entry :=
  Nat.le_trans (SourceCurrentInitialSelectionForecast.class_fuel_selected selected _ _) (Nat.le_max_right _ _)

/-- Every selected class return fits the original complete class profile. -/
theorem class_profile {records kept : List Record} (selected : kept.Sublist records)
    (budget count : Nat) (alphabet : List Guard) (entry : Profile) :
    Le (Classes.foldProfile kept count (Preparation.finalProfile budget count records alphabet entry))
      (finalProfile budget count records alphabet entry) :=
  SourceCurrentInitialSelectionForecast.class_profile_selected selected _ _

/-- Initial reservations cover preparation and the original class schedule. -/
noncomputable def Reserved (bits budget count : Nat) (records : List Record) (alphabet : List Guard)
    (entry : Profile) : Prop :=
  SourceCurrentScanNumericForecast.Reserved bits budget count (records.map Record.paths) alphabet entry ∧
    Classes.Reserved bits records count (Preparation.finalProfile budget count records alphabet entry)

/-- The original reservation supplies every selected continuation without an empty-pass Room test. -/
theorem class_reserved {records kept : List Record} (selected : kept.Sublist records)
    (bits budget count : Nat) (alphabet : List Guard) (entry : Profile)
    (reserved : Reserved bits budget count records alphabet entry) :
    Classes.Reserved bits kept count (Preparation.finalProfile budget count records alphabet entry) := by
  cases kept with
  | nil => trivial
  | cons first rest =>
      cases records with
      | nil => have impossible := selected.length_le; simp only [List.length_cons, List.length_nil] at impossible; omega
      | cons record records => exact reserved.2.mono (class_profile selected budget count alphabet entry)

end MicroCFTA.SourceCurrentClassesForecast
