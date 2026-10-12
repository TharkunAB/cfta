import MicroCFTA.Probability

/-!
# The distribution returned by pool minimization

After similarity and minimization return retained symbols, the source filters
the original entries and builds a new namedPool. Each retained occurrence has
unit weight. Removed occurrences do not transfer mass to a representative.
-/
namespace MicroCFTA.PoolMinimization
open Probability

/-- The source retains the original order and multiplicity of surviving entries. -/
def retained (keep : Entry → Bool) (entries : List Entry) : List Entry := entries.filter keep

/-- namedPool gives the retained entries a fresh uniform member distribution. -/
def distribution (keep : Entry → Bool) (entries : List Entry) : Distribution Entry :=
  normalize (counting (retained keep entries))

/-- The returned pool contains exactly the retained original occurrences. -/
theorem retained_member (keep : Entry → Bool) (entries : List Entry) (entry : Entry) :
    entry ∈ retained keep entries ↔ entry ∈ entries ∧ keep entry = true := by
  simp [retained]

/-- Actual output probabilities count retained occurrences of an event. -/
theorem distribution_event (keep event : Entry → Bool) (entries : List Entry) :
    eventMass event (distribution keep entries) =
      ((retained keep entries).countP event : Rat) / (retained keep entries).length :=
  uniform_event_probability event _

/-- Mapping each old member to a representative retains that member's old mass. -/
theorem representative_event (representative : Entry → Value) (event : Value → Bool)
    (entries : List Entry) :
    eventMass event (Probability.map representative (normalize (counting entries))) =
      (entries.countP (event ∘ representative) : Rat) / entries.length := by
  rw [eventMass_map, uniform_event_probability]

/-- Rebuilding a retained pool is exactly conditioning its original unit masses. -/
theorem retained_condition (keep : Entry → Bool) (entries : List Entry) :
    distribution keep entries = condition keep (counting entries) := by
  unfold distribution condition retained
  congr 1
  induction entries with
  | nil => rfl
  | cons first rest ih =>
      cases found : keep first <;> simp [counting, restrict, found] at * <;> exact ih

/-- The documented three-entry example retains the first equivalent representative. -/
def keepExample (value : Nat) : Bool := value != 1

/-- Both original entries in the first class map to its representative. -/
def representativeExample (value : Nat) : Nat := if value < 2 then 0 else 2

/-- Minimization removes a distinct term that belonged to the original pool. -/
theorem removed_member : (1 : Nat) ∈ [0, 1, 2] ∧ 1 ∉ retained keepExample [0, 1, 2] := by decide

/-- Source pool rebuilding gives the retained first class mass one half. -/
theorem retained_half : eventMass (fun value => value == 0) (distribution keepExample [0, 1, 2]) = 1 / 2 := by
  cbv

/-- Preserving original mass through representatives gives that class two thirds. -/
theorem representative_two_thirds :
    eventMass (fun value => value == 0)
      (Probability.map representativeExample (normalize (counting [0, 1, 2]))) = 2 / 3 := by cbv

/-- Source minimization therefore does not generally preserve class probability. -/
theorem class_mass_changes :
    eventMass (fun value => value == 0) (distribution keepExample [0, 1, 2]) ≠
      eventMass (fun value => value == 0)
        (Probability.map representativeExample (normalize (counting [0, 1, 2]))) := by
  rw [retained_half, representative_two_thirds]
  intro same
  have numerators := congrArg Rat.num same
  cbv at numerators
  cases numerators

end MicroCFTA.PoolMinimization
