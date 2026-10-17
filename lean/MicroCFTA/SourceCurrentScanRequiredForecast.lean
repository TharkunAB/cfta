import MicroCFTA.SourceCurrentInitialSelectionForecast
import MicroCFTA.SourceCurrentScanNumericForecast

/-!
# Initial complete Scan and Required prefix forecasts

The original class schedule bounds the Scan return. Every possible
positional record selection supplies a Required forecast from that entry.
One initial ceiling bounds all six preparation fuels independently.
-/
namespace MicroCFTA.SourceCurrentScanRequiredForecast
open SourceCurrentAllocatedNativeResourceForecast (Profile Le)
open SourceEqualityClassOrder (Record)
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
namespace Selection
export SourceCurrentInitialSelectionForecast (requiredProfile requiredWorker requiredReader)
end Selection

/-- The initial Scan schedule supplies the common Required entry profile. -/
noncomputable def scanProfile (budget count : Nat) (records : List Record) (alphabet : List Guard) (entry : Profile) : Profile :=
  (SourceCurrentScanNumericForecast.schedule budget count (records.map Record.paths) alphabet entry).2

/-- Original record selections determine one complete preparation profile. -/
noncomputable def finalProfile (budget count : Nat) (records : List Record) (alphabet : List Guard) (entry : Profile) : Profile :=
  Selection.requiredProfile records count (scanProfile budget count records alphabet entry)

/-- A stopped Scan fits the same complete preparation profile. -/
theorem scan_le (budget count : Nat) (records : List Record) (alphabet : List Guard) (entry : Profile) :
    Le (scanProfile budget count records alphabet entry) (finalProfile budget count records alphabet entry) :=
  SourceCurrentInitialSelectionForecast.required_ge _ _ _

/-- One initial ceiling covers the Scan and both Required fuels. -/
noncomputable def fuel (budget count : Nat) (records : List Record) (alphabet : List Guard) (entry : Profile) : Nat :=
  max (SourceCurrentScanNumericForecast.fuel budget count (records.map Record.paths) alphabet entry)
    (max (Selection.requiredWorker records) (Selection.requiredReader records count (scanProfile budget count records alphabet entry)))

/-- The common preparation ceiling supplies the Scan at its original entry. -/
theorem scan_fuel (budget count : Nat) (records : List Record) (alphabet : List Guard) (entry : Profile) :
    SourceCurrentScanNumericForecast.fuel budget count (records.map Record.paths) alphabet entry ≤
      fuel budget count records alphabet entry := Nat.le_max_left _ _

/-- Every actual selected Required worker fits the same initial preparation ceiling. -/
theorem required_worker {records kept : List Record} (selected : kept.Sublist records)
    (budget count : Nat) (alphabet : List Guard) (entry : Profile) :
    SourceCurrentConstrainedCapRequiredInitialNumeric.workerFuel (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) ≤
      fuel budget count records alphabet entry :=
  Nat.le_trans (SourceCurrentInitialSelectionForecast.required_worker_selected selected)
    (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))

/-- Every actual selected Required reader fits the same initial preparation ceiling. -/
theorem required_reader {records kept : List Record} (selected : kept.Sublist records)
    (budget count : Nat) (alphabet : List Guard) (entry : Profile) :
    SourceCurrentConstrainedCapRequiredInitialNumeric.readerFuel (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) count
      (scanProfile budget count records alphabet entry) ≤ fuel budget count records alphabet entry :=
  Nat.le_trans (SourceCurrentInitialSelectionForecast.required_reader_selected selected count _)
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))

end MicroCFTA.SourceCurrentScanRequiredForecast
