import MicroCFTA.SourceCurrentClassesForecast
import MicroCFTA.SourceCurrentAllocatedPrecheck

/-!
# Initial forecasts for the allocated local precheck

The original stored fields and equality operations determine the pure
precheck branch. Only its live original records reserve class work.
Early returns require no native query room and use zero worker fuel.
-/
namespace MicroCFTA.SourceCurrentLocalForecast
open SourceCurrentAllocatedNativeResourceForecast (Profile)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "runPrefix" => SourceEqualityPartialPrecheckAllocation.run
local notation "guards" => SourceCurrentConjunctionGuardUniverse.guards
variable {width : Nat}

/-- The initial source fields determine the final local profile. -/
noncomputable def finalProfile (budget count : Nat) (loaded : Allocated) (inherited : EqValue)
    (before : Checked width) (profile : Profile) : Profile :=
  match (runPrefix loaded.stored loaded.guard inherited before.operations).1 with
  | .ok (.classes records) =>
      SourceCurrentClassesForecast.finalProfile budget count records (guards before.native.machine.heap) profile
  | _ => profile

/-- One initial ceiling covers all nine independently larger local fuels. -/
noncomputable def fuel (budget count : Nat) (loaded : Allocated) (inherited : EqValue)
    (before : Checked width) (profile : Profile) : Nat :=
  match (runPrefix loaded.stored loaded.guard inherited before.operations).1 with
  | .ok (.classes records) =>
      SourceCurrentClassesForecast.fuel budget count records (guards before.native.machine.heap) profile
  | _ => 0

/-- Only a live branch reserves its original record schedule. -/
noncomputable def Reserved (bits budget count : Nat) (loaded : Allocated) (inherited : EqValue)
    (before : Checked width) (profile : Profile) : Prop :=
  match (runPrefix loaded.stored loaded.guard inherited before.operations).1 with
  | .ok (.classes records) =>
      SourceCurrentClassesForecast.Reserved bits budget count records (guards before.native.machine.heap) profile
  | _ => True

end MicroCFTA.SourceCurrentLocalForecast
