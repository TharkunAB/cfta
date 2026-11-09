import MicroCFTA.SourceCurrentSharedClassesForecast
import MicroCFTA.SourceCurrentAllocatedPrecheck

/-!
# Initial forecasts for the shared local precheck

The original stored fields and equality operations determine the pure
precheck branch. Only its live original records reserve class work.
Early returns require no native query room and use zero worker fuel.
-/
namespace MicroCFTA.SourceCurrentSharedLocalForecast
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
      SourceCurrentSharedClassesForecast.finalProfile budget count records (guards before.native.machine.heap) profile
  | _ => profile

/-- One initial ceiling covers all nine independently larger local fuels. -/
noncomputable def fuel (budget count : Nat) (loaded : Allocated) (inherited : EqValue)
    (before : Checked width) (profile : Profile) : Nat :=
  match (runPrefix loaded.stored loaded.guard inherited before.operations).1 with
  | .ok (.classes records) =>
      SourceCurrentSharedClassesForecast.fuel budget count records (guards before.native.machine.heap) profile
  | _ => 0

/-- Only a live branch reserves its original record schedule. -/
noncomputable def Reserved (bits budget count : Nat) (loaded : Allocated) (inherited : EqValue)
    (before : Checked width) (profile : Profile) : Prop :=
  match (runPrefix loaded.stored loaded.guard inherited before.operations).1 with
  | .ok (.classes records) =>
      SourceCurrentSharedClassesForecast.Reserved bits budget count records (guards before.native.machine.heap) profile
  | _ => True

/-- An unchanged precheck retains its profile and requires no local worker or reservation. -/
theorem unchanged (bits budget count : Nat) (loaded : Allocated) (inherited : EqValue)
    (before : Checked width) (profile : Profile)
    (actual : (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok .unchanged) :
    finalProfile budget count loaded inherited before profile = profile ∧
      fuel budget count loaded inherited before profile = 0 ∧
      Reserved bits budget count loaded inherited before profile := by
  simp [finalProfile, fuel, Reserved, actual]

end MicroCFTA.SourceCurrentSharedLocalForecast
