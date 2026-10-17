import MicroCFTA.SourceCurrentConstrainedCapRequiredInitialNumeric
import MicroCFTA.SourceCurrentConstrainedCapClassForecast

/-!
# Initial resource bounds for every positional record selection

The original record list supplies a finite list of all its sublists.
Repeated records remain separate occurrences. Each possible Required
forecast enters a numeric join. No actual Scan result is an input.
-/
namespace MicroCFTA.SourceCurrentInitialSelectionForecast
open SourceCurrentAllocatedNativeResourceForecast (Profile Le)
open SourceCurrentConstrainedCapEditForecast (join join_left join_right)
local notation "Record" => SourceEqualityClassOrder.Record
namespace Required
export SourceCurrentConstrainedCapRequiredInitialNumeric (forecast workerFuel readerFuel)
end Required
namespace Classes
export SourceCurrentConstrainedCapClassForecast (foldProfile foldFuel)
end Classes

/-- Enumerate positional sublists without identifying repeated occurrences. -/
def selections {α : Type u} : List α → List (List α)
  | [] => [[]]
  | first :: rest => selections rest ++ (selections rest).map (first :: ·)

/-- Every enumerated selection retains original order and multiplicity. -/
theorem selection_sublist {α : Type u} {kept records : List α}
    (member : kept ∈ selections records) : kept.Sublist records := by
  induction records generalizing kept with
  | nil =>
      have same : kept = [] := List.mem_singleton.mp member
      subst kept
      exact .refl _
  | cons first rest ih =>
      rcases List.mem_append.mp member with omitted | included
      · exact .cons first (ih omitted)
      · obtain ⟨tail, present, rfl⟩ := List.mem_map.mp included
        exact .cons_cons first (ih present)

/-- Every positional original sublist occurs in the initial enumeration. -/
theorem sublist_selection {α : Type u} {kept records : List α}
    (selected : kept.Sublist records) : kept ∈ selections records := by
  induction selected with
  | slnil => exact List.mem_cons_self
  | cons first selected ih => exact List.mem_append_left _ ih
  | cons_cons first selected ih =>
      exact List.mem_append_right _ (List.mem_map.mpr ⟨_, ih, rfl⟩)

/-- Join a fixed list of numeric profiles with its original entry profile. -/
def cover (profiles : List Profile) (entry : Profile) : Profile :=
  profiles.foldr join entry

/-- The profile join retains the original entry. -/
theorem cover_ge (profiles : List Profile) (entry : Profile) : Le entry (cover profiles entry) := by
  induction profiles with
  | nil => exact Le.refl _
  | cons first rest ih => exact ih.trans (join_right _ _)

/-- Every listed profile fits the same initial join. -/
theorem cover_member {profiles : List Profile} {profile : Profile} (entry : Profile)
    (member : profile ∈ profiles) : Le profile (cover profiles entry) := by
  induction profiles with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | included
      · exact join_left _ _
      · exact (ih included).trans (join_right _ _)

/-- The original records determine every possible selected Required profile. -/
noncomputable def requiredProfile (records : List Record) (count : Nat) (entry : Profile) : Profile :=
  cover ((selections records).map fun kept =>
    Required.forecast (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) count entry) entry

/-- The Required join retains the original entry. -/
theorem required_ge (records : List Record) (count : Nat) (entry : Profile) :
    Le entry (requiredProfile records count entry) := cover_ge _ _

/-- Every actual positional selection fits the initial Required join. -/
theorem required_selected {records kept : List Record} (selected : kept.Sublist records)
    (count : Nat) (entry : Profile) :
    Le (Required.forecast (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) count entry)
      (requiredProfile records count entry) :=
  cover_member entry (List.mem_map.mpr ⟨kept, sublist_selection selected, rfl⟩)

/-- A finite original list supplies a common natural-number ceiling. -/
def maximum (values : List Nat) : Nat := values.foldr max 0

/-- Each original listed value fits its computed maximum. -/
theorem maximum_member {values : List Nat} {value : Nat} (member : value ∈ values) :
    value ≤ maximum values := by
  induction values with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | included
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih included) (Nat.le_max_right _ _)

/-- Original record selections determine one common Required worker ceiling. -/
noncomputable def requiredWorker (records : List Record) : Nat :=
  maximum ((selections records).map fun kept =>
    Required.workerFuel (SourceEqualitySelectedRequired.paths (kept.map Record.paths)))

/-- Each selected Required worker fits the original common ceiling. -/
theorem required_worker_selected {records kept : List Record} (selected : kept.Sublist records) :
    Required.workerFuel (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) ≤ requiredWorker records :=
  maximum_member (List.mem_map.mpr ⟨kept, sublist_selection selected, rfl⟩)

/-- The common Required profile supplies a shared reader ceiling. -/
noncomputable def requiredReader (records : List Record) (count : Nat) (entry : Profile) : Nat :=
  SourceCurrentConstrainedCapRequiredResources.readFuel (requiredProfile records count entry)

/-- Each selected reader forecast fits the original common reader ceiling. -/
theorem required_reader_selected {records kept : List Record} (selected : kept.Sublist records)
    (count : Nat) (entry : Profile) :
    Required.readerFuel (SourceEqualitySelectedRequired.paths (kept.map Record.paths)) count entry ≤
      requiredReader records count entry :=
  SourceCurrentConstrainedCapRequiredResources.readFuel_mono (required_selected selected count entry)

/-- A selected class fold fits the original right-fold profile. -/
theorem class_profile_selected {records kept : List Record} (selected : kept.Sublist records)
    (count : Nat) (entry : Profile) :
    Le (Classes.foldProfile kept count entry) (Classes.foldProfile records count entry) := by
  induction selected with
  | slnil => exact Le.refl _
  | cons first selected ih => exact ih.trans (SourceCurrentConstrainedCapClassForecast.class_ge first count _)
  | cons_cons first selected ih => exact SourceCurrentConstrainedCapClassForecast.class_mono first count ih

/-- A selected class fold fits the original common worker ceiling. -/
theorem class_fuel_selected {records kept : List Record} (selected : kept.Sublist records)
    (count : Nat) (entry : Profile) :
    Classes.foldFuel kept count entry ≤ Classes.foldFuel records count entry := by
  induction selected with
  | slnil => exact Nat.le_refl _
  | cons first selected ih => exact Nat.le_trans ih (Nat.le_max_left _ _)
  | cons_cons first selected ih =>
      exact Nat.max_le.mpr ⟨Nat.le_trans ih (Nat.le_max_left _ _),
        Nat.le_trans (SourceCurrentConstrainedCapClassForecast.classFuel_mono first count
          (class_profile_selected selected count entry)) (Nat.le_max_right _ _)⟩

end MicroCFTA.SourceCurrentInitialSelectionForecast
