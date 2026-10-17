import MicroCFTA.SourceCurrentMkEdgeNumeric
import MicroCFTA.SourceCurrentLocalForecast
import MicroCFTA.SourceCurrentAllocatedPartialState

/-!
# Initial forecasts for complete parent edge construction

Raw contradiction precedes field lookup and child work. A live original
field reserves local reduction and one constructor at its returned profile.
Resident forecasts read only the original field and initial operations.
-/
namespace MicroCFTA.SourceCurrentParentForecast
open SourceCurrentAllocatedNativeResourceForecast (Profile)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Request" => SourceCurrentAllocatedPartialState.EdgeRequest
local notation "contradictory" => SourceEqualityMkEdgeAllocation.contradictory
local notation "load" => SourceEqualityConstraintFieldLookup.load
variable {width : Nat}

/-- Initial raw fields determine the local schedule and final constructor profile. -/
noncomputable def finalProfile (budget count : Nat) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (before : Checked width) (profile : Profile) : Profile :=
  if contradictory original then SourceCurrentMkEdgeNumeric.finalProfile 0 profile
  else SourceCurrentMkEdgeNumeric.finalProfile count
    (SourceCurrentLocalForecast.finalProfile budget count loaded inherited before profile)

/-- Raw rejection uses no local worker fuel. A live field uses its initial local ceiling. -/
noncomputable def fuel (budget count : Nat) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (before : Checked width) (profile : Profile) : Nat :=
  if contradictory original then 0 else SourceCurrentLocalForecast.fuel budget count loaded inherited before profile

/-- Only a live raw edge reserves local query work. -/
noncomputable def Reserved (bits budget count : Nat) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (before : Checked width) (profile : Profile) : Prop :=
  if contradictory original then True else SourceCurrentLocalForecast.Reserved bits budget count loaded inherited before profile

/-- The initial resident request supplies its own selected loaded-field profile. -/
noncomputable def residentProfile (budget : Nat) (request : Request) (before : Checked width) (profile : Profile) : Profile :=
  if contradictory request.value.entry.key.constraint then SourceCurrentMkEdgeNumeric.finalProfile 0 profile
  else match load request.value.entry.key.constraint before.operations.constraints with
    | .ok (some loaded) => finalProfile budget request.value.children.length request.value.entry.key.constraint
        loaded request.inherited before profile
    | _ => profile

/-- The initial resident field fixes the complete parent worker ceiling. -/
noncomputable def residentFuel (budget : Nat) (request : Request) (before : Checked width) (profile : Profile) : Nat :=
  if contradictory request.value.entry.key.constraint then 0
  else match load request.value.entry.key.constraint before.operations.constraints with
    | .ok (some loaded) => fuel budget request.value.children.length request.value.entry.key.constraint
        loaded request.inherited before profile
    | _ => 0

/-- Raw rejection omits field lookup. A live resident request reserves its own initial field. -/
noncomputable def residentReserved (bits budget : Nat) (request : Request) (before : Checked width) (profile : Profile) : Prop :=
  if contradictory request.value.entry.key.constraint then True
  else match load request.value.entry.key.constraint before.operations.constraints with
    | .ok (some loaded) => Reserved bits budget request.value.children.length request.value.entry.key.constraint
        loaded request.inherited before profile
    | _ => False

end MicroCFTA.SourceCurrentParentForecast
