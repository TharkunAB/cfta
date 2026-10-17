import MicroCFTA.SourceCurrentConstrainedCapEditListNumeric
import MicroCFTA.SourceCurrentAllocatedClassEditPlan

/-!
# Initial class and right-fold resource forecasts

Each class uses the literal compiled edit and the retained forest length.
The tail executes before the head. Its forecast enters the head unchanged.
These pure schedules do not assert class or pass completion.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapClassForecast
open SourceCurrentAllocatedNativeResourceForecast (Profile Le Room)
open SourceCurrentAllocatedClassEditPlan (compiled)
namespace Edit
export SourceCurrentConstrainedCapEditListNumeric (finalProfile fuel Reserved)
end Edit

/-- A class reserves its literal compiled edit over the fixed forest length. -/
noncomputable def classProfile (record : SourceEqualityClassOrder.Record) (count : Nat)
    (profile : Profile) : Profile := Edit.finalProfile record count (compiled record) count profile

/-- One class ceiling supplies all six literal forest edit worker fuels. -/
noncomputable def classFuel (record : SourceEqualityClassOrder.Record) (count : Nat)
    (profile : Profile) : Nat := Edit.fuel record count (compiled record) count profile

/-- A class forecast retains every initial profile component. -/
theorem class_ge (record : SourceEqualityClassOrder.Record) (count : Nat) (profile : Profile) :
    Le profile (classProfile record count profile) := by
  unfold classProfile Edit.finalProfile
  cases compiled record with
  | editAt token => exact Le.refl _
  | editBelow entries =>
      exact SourceCurrentConstrainedCapEditForecast.scan_ge _
        (SourceCurrentConstrainedCapEditForecast.plan_ge record count _) count profile

/-- Larger initial profiles retain the class return forecast. -/
theorem class_mono (record : SourceEqualityClassOrder.Record) (count : Nat)
    {first last : Profile} (increase : Le first last) :
    Le (classProfile record count first) (classProfile record count last) := by
  unfold classProfile Edit.finalProfile
  cases compiled record with
  | editAt token => exact increase
  | editBelow entries =>
      exact SourceCurrentConstrainedCapEditForecast.scan_mono _
        (SourceCurrentConstrainedCapEditForecast.plan_mono record count _) count increase

/-- Larger initial profiles retain the class common worker fuel. -/
theorem classFuel_mono (record : SourceEqualityClassOrder.Record) (count : Nat)
    {first last : Profile} (increase : Le first last) :
    classFuel record count first ≤ classFuel record count last := by
  have returned := class_mono record count increase
  unfold classProfile at returned
  unfold classFuel Edit.fuel
  cases built : compiled record with
  | editAt token => exact Nat.le_refl _
  | editBelow entries =>
      rw [built] at returned
      exact Nat.max_le.mpr ⟨Nat.le_max_left _ _,
        Nat.le_trans (SourceCurrentConstrainedCapEditForecast.stageFuel_mono record count returned)
          (Nat.le_max_right _ _)⟩

/-- Room at the class return supplies the literal forest-edit reservation. -/
theorem class_reserved (bits : Nat) (record : SourceEqualityClassOrder.Record) (count : Nat)
    (profile : Profile) (room : Room bits (classProfile record count profile)) :
    Edit.Reserved bits record count (compiled record) count profile := by
  unfold classProfile at room
  unfold Edit.Reserved
  cases built : compiled record with
  | editAt token => trivial
  | editBelow entries => simpa only [built] using room

/-- The right fold passes the complete tail profile to its head class. -/
noncomputable def foldProfile : List SourceEqualityClassOrder.Record → Nat → Profile → Profile
  | [], _, profile => profile
  | record :: records, count, profile => classProfile record count (foldProfile records count profile)

/-- The common fold ceiling covers the tail and its exact head entry. -/
noncomputable def foldFuel : List SourceEqualityClassOrder.Record → Nat → Profile → Nat
  | [], _, _ => 0
  | record :: records, count, profile =>
      max (foldFuel records count profile) (classFuel record count (foldProfile records count profile))

/-- The empty fold needs no room. A nonempty fold reserves its complete return. -/
noncomputable def Reserved (bits : Nat) (records : List SourceEqualityClassOrder.Record)
    (count : Nat) (profile : Profile) : Prop :=
  match records with
  | [] => True
  | _ :: _ => Room bits (foldProfile records count profile)

/-- The empty fold keeps its initial profile. -/
theorem foldProfile_nil (count : Nat) (profile : Profile) : foldProfile [] count profile = profile := rfl

/-- The head receives the profile returned by the tail. -/
theorem foldProfile_cons (record : SourceEqualityClassOrder.Record) (records : List SourceEqualityClassOrder.Record)
    (count : Nat) (profile : Profile) :
    foldProfile (record :: records) count profile = classProfile record count (foldProfile records count profile) := rfl

/-- The empty fold makes no worker call. -/
theorem foldFuel_nil (count : Nat) (profile : Profile) : foldFuel [] count profile = 0 := rfl

/-- The common ceiling preserves the literal tail-before-head schedule. -/
theorem foldFuel_cons (record : SourceEqualityClassOrder.Record) (records : List SourceEqualityClassOrder.Record)
    (count : Nat) (profile : Profile) :
    foldFuel (record :: records) count profile =
      max (foldFuel records count profile) (classFuel record count (foldProfile records count profile)) := rfl

/-- The complete right fold retains its initial profile. -/
theorem fold_ge (records : List SourceEqualityClassOrder.Record) (count : Nat) (profile : Profile) :
    Le profile (foldProfile records count profile) := by
  induction records with
  | nil => exact Le.refl _
  | cons record records ih => exact ih.trans (class_ge record count _)

/-- Larger initial profiles retain every tail and head forecast. -/
theorem fold_mono (records : List SourceEqualityClassOrder.Record) (count : Nat)
    {first last : Profile} (increase : Le first last) :
    Le (foldProfile records count first) (foldProfile records count last) := by
  induction records with
  | nil => exact increase
  | cons record records ih => exact class_mono record count ih

/-- Larger initial profiles retain the complete common fold fuel. -/
theorem foldFuel_mono (records : List SourceEqualityClassOrder.Record) (count : Nat)
    {first last : Profile} (increase : Le first last) :
    foldFuel records count first ≤ foldFuel records count last := by
  induction records with
  | nil => exact Nat.le_refl _
  | cons record records ih =>
      exact Nat.max_le.mpr ⟨Nat.le_trans ih (Nat.le_max_left _ _),
        Nat.le_trans (classFuel_mono record count (fold_mono records count increase)) (Nat.le_max_right _ _)⟩

/-- The tail return fits the whole fold return. -/
theorem fold_tail (record : SourceEqualityClassOrder.Record) (records : List SourceEqualityClassOrder.Record)
    (count : Nat) (profile : Profile) :
    Le (foldProfile records count profile) (foldProfile (record :: records) count profile) := class_ge record count _

/-- The tail worker fuel fits the common fold ceiling. -/
theorem foldFuel_tail (record : SourceEqualityClassOrder.Record) (records : List SourceEqualityClassOrder.Record)
    (count : Nat) (profile : Profile) : foldFuel records count profile ≤ foldFuel (record :: records) count profile :=
  Nat.le_max_left _ _

/-- The head worker fuel uses the literal tail return. -/
theorem foldFuel_head (record : SourceEqualityClassOrder.Record) (records : List SourceEqualityClassOrder.Record)
    (count : Nat) (profile : Profile) :
    classFuel record count (foldProfile records count profile) ≤ foldFuel (record :: records) count profile :=
  Nat.le_max_right _ _

/-- One final room test supplies the initial entry. -/
theorem fold_room_initial (bits : Nat) (records : List SourceEqualityClassOrder.Record) (count : Nat)
    (profile : Profile) (room : Room bits (foldProfile records count profile)) : Room bits profile :=
  room.mono (fold_ge records count profile)

/-- One final room test supplies the complete tail. -/
theorem fold_room_tail (bits : Nat) (record : SourceEqualityClassOrder.Record)
    (records : List SourceEqualityClassOrder.Record) (count : Nat) (profile : Profile)
    (room : Room bits (foldProfile (record :: records) count profile)) :
    Room bits (foldProfile records count profile) := room.mono (fold_tail record records count profile)

/-- One final room test supplies the class at its exact tail-return entry. -/
theorem fold_reserved_head (bits : Nat) (record : SourceEqualityClassOrder.Record)
    (records : List SourceEqualityClassOrder.Record) (count : Nat) (profile : Profile)
    (room : Room bits (foldProfile (record :: records) count profile)) :
    Edit.Reserved bits record count (compiled record) count (foldProfile records count profile) :=
  class_reserved bits record count _ room

/-- A nonempty fold reservation supplies its literal head return room. -/
theorem reserved_head (bits : Nat) (record : SourceEqualityClassOrder.Record)
    (records : List SourceEqualityClassOrder.Record) (count : Nat) (profile : Profile)
    (reserved : Reserved bits (record :: records) count profile) :
    Room bits (classProfile record count (foldProfile records count profile)) := reserved

/-- The complete reservation supplies the remaining tail without an empty-fold room test. -/
theorem reserved_tail (bits : Nat) (record : SourceEqualityClassOrder.Record)
    (records : List SourceEqualityClassOrder.Record) (count : Nat) (profile : Profile)
    (reserved : Reserved bits (record :: records) count profile) :
    Reserved bits records count profile := by
  cases records with
  | nil => trivial
  | cons next rest => exact fold_room_tail bits record (next :: rest) count profile reserved

/-- The fold reservation supplies the compiled edit at the exact head entry. -/
theorem reserved_class (bits : Nat) (record : SourceEqualityClassOrder.Record)
    (records : List SourceEqualityClassOrder.Record) (count : Nat) (profile : Profile)
    (reserved : Reserved bits (record :: records) count profile) :
    Edit.Reserved bits record count (compiled record) count (foldProfile records count profile) :=
  class_reserved bits record count _ (reserved_head bits record records count profile reserved)

/-- Concatenated record lists execute the last list before the first list. -/
theorem foldProfile_append (first last : List SourceEqualityClassOrder.Record) (count : Nat) (profile : Profile) :
    foldProfile (first ++ last) count profile = foldProfile first count (foldProfile last count profile) := by
  induction first with
  | nil => rfl
  | cons record records ih => exact congrArg (classProfile record count) ih

/-- A common concatenated ceiling covers both literal fold phases. -/
theorem foldFuel_append (first last : List SourceEqualityClassOrder.Record) (count : Nat) (profile : Profile) :
    foldFuel (first ++ last) count profile =
      max (foldFuel last count profile) (foldFuel first count (foldProfile last count profile)) := by
  induction first with
  | nil => simp only [List.nil_append, foldFuel, Nat.max_zero]
  | cons record records ih =>
      simp only [List.cons_append, foldFuel, ih, foldProfile_append, Nat.max_assoc]

end MicroCFTA.SourceCurrentConstrainedCapClassForecast
