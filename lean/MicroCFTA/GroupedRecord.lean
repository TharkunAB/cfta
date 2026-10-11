import MicroCFTA.ObservationMass
import MicroCFTA.RecursiveSource

/-!
# Grouped size-class records

Each recursive key stores a mass beside its count, decoder, and sampler.
Merging keys selects by mass; it retains structural ranks in list order.
Products multiply key masses and preserve both conditional distributions.
Empty classes have zero mass and no rank.
-/

namespace MicroCFTA.GroupedRecord
open Probability SamplerReplay

/-- The parallel fields read by a grouped recursive class. -/
structure Group (α : Type) where
  mass : Rat
  members : Record α

/-- Live key mass agrees with structural productivity, and each member rank has coherent probability. -/
def Valid (group : Group α) : Prop :=
  LiveValid group.members ∧ 0 ≤ group.mass ∧ (0 < group.mass ↔ 0 < Decoder.count group.members.plan)

/-- A class with no members contributes neither mass nor ranks. -/
def empty : Group α := ⟨0, FiniteSource.empty⟩

/-- An empty grouped class satisfies all record invariants. -/
theorem empty_valid : Valid (empty : Group α) := by
  exact ⟨FiniteSource.empty_live, by change (0 : Rat) ≤ 0; decide,
    by simp [empty, FiniteSource.empty, source, Decoder.count]⟩

/-- An ordinary source class contributes its member count to the family mass. -/
def counted (record : Record α) : Group α := ⟨(Decoder.count record.plan : Rat), record⟩

/-- Count-mass conversion needs no independent cardinality or sampler assumption. -/
theorem counted_valid (record : Record α) (live : LiveValid record) : Valid (counted record) := by
  exact ⟨live, Rat.natCast_nonneg, Rat.natCast_pos⟩

/-- Finite source classes enter a recursive family by the source's ordinary count policy. -/
def finiteClass (description : FiniteSource.Source α) (size : Nat) : Group α := counted (FiniteSource.atSize description size)

/-- Every ordinary finite source class constructs a valid grouped record. -/
theorem finiteClass_valid (description : FiniteSource.Source α) (size : Nat) : Valid (finiteClass description size) :=
  counted_valid _ (FiniteSource.class_live description size)

/-- Retain an independently computed positive key mass whenever its class has members. -/
def retained (mass : Rat) (record : Record α) : Group α :=
  ⟨if 0 < Decoder.count record.plan then mass else 0, record⟩

/-- Retained atomic or grouped mass does not change the class decoder or conditional sampler. -/
theorem retained_valid (mass : Rat) (positive : 0 < mass) (record : Record α) (live : LiveValid record) :
    Valid (retained mass record) := by
  refine ⟨live, ?_, ?_⟩
  · dsimp [retained]
    split <;> grind
  · dsimp [retained]
    split <;> simp_all

/-- Add all alternative key masses without normalizing their family scale. -/
def massSum : List (Group α) → Rat
  | [] => 0
  | first :: rest => first.mass + massSum rest

/-- Add structural member counts independently of key masses. -/
def countSum : List (Group α) → Nat
  | [] => 0
  | first :: rest => Decoder.count first.members.plan + countSum rest

/-- Merge the same-key alternatives with the actual source's mass-weighted sampler. -/
def merge (groups : List (Group α)) : Group α :=
  ⟨massSum groups, manyRecord (groups.map fun group => (group.mass, group.members))⟩

/-- Merging preserves every structural member in its original alternative order. -/
theorem merge_values (groups : List (Group α)) :
    Decoder.values (merge groups).members.plan = groups.flatMap (fun group => Decoder.values group.members.plan) := by
  simp [merge, manyRecord, manyPlan_values, List.flatMap_map]

/-- Group masses cannot change the finite rank range. -/
theorem merge_count (groups : List (Group α)) : Decoder.count (merge groups).members.plan = countSum groups := by
  rw [Decoder.count_correct, merge_values]
  induction groups with
  | nil => rfl
  | cons first rest ih => simp [countSum, Decoder.count_correct, ih]

/-- The combined mass is nonnegative and is positive exactly when some structural member exists. -/
theorem massSum_live (groups : List (Group α)) (valid : ∀ group ∈ groups, Valid group) :
    0 ≤ massSum groups ∧ (0 < massSum groups ↔ 0 < countSum groups) := by
  induction groups with
  | nil => simp [massSum, countSum]
  | cons first rest ih =>
      have head := valid first (by simp)
      have firstNonnegative := head.2.1
      have tail := ih (fun group member => valid group (by simp [member]))
      dsimp only [massSum, countSum]
      constructor
      · grind
      · constructor
        · intro positive
          by_cases firstLive : 0 < Decoder.count first.members.plan
          · omega
          · have firstZero : first.mass = 0 := by
              have absent : ¬0 < first.mass := fun live => firstLive (head.2.2.mp live)
              grind
            have restLive : 0 < countSum rest := tail.2.mp (by simpa [firstZero, Rat.zero_add] using positive)
            omega
        · intro positive
          have cases : 0 < Decoder.count first.members.plan ∨ 0 < countSum rest := by omega
          rcases cases with firstLive | restLive
          · have massPositive := head.2.2.mpr firstLive
            grind
          · have massPositive := tail.2.mpr restLive
            grind

/-- Same-key recursive merging builds a complete coherent mass and member record. -/
theorem merge_valid (groups : List (Group α)) (valid : ∀ group ∈ groups, Valid group) : Valid (merge groups) := by
  have mass := massSum_live groups valid
  refine ⟨?_, mass.1, ?_⟩
  · apply many_live
    · intro entry present
      obtain ⟨group, member, rfl⟩ := List.mem_map.mp present
      exact (valid group member).1
    · intro entry present live
      obtain ⟨group, member, rfl⟩ := List.mem_map.mp present
      exact (valid group member).2.2.mpr live
  · rw [merge_count]
    exact mass.2

/-- The group choice probability is its retained mass, followed by its conditional source distribution. -/
theorem merge_probability (groups : List (Group α)) :
    (merge groups).members.sampling.values = weightedChoice (groups.map fun group =>
      (Decoder.count group.members.plan, group.mass, group.members.sampling.values)) := by
  simp [merge, many_values, List.map_map, Function.comp_def]

/-- Mapping a grouped value preserves key mass and structural ranks. -/
def map (transform : α → β) (group : Group α) : Group β :=
  ⟨group.mass, mapRecord transform group.members⟩

/-- Value mapping preserves the complete grouped record invariant. -/
theorem map_valid (transform : α → β) (group : Group α) (valid : Valid group) : Valid (map transform group) :=
  ⟨map_live transform group.members valid.1, valid.2.1, valid.2.2⟩

/-- One product split multiplies the two key masses and applies independent member samplers. -/
def apply (functions : Group (α → β)) (arguments : Group α) : Group β :=
  ⟨functions.mass * arguments.mass, applyRecord functions.members arguments.members⟩

/-- A product has positive mass exactly when both finite member factors are nonempty. -/
theorem apply_valid (functions : Group (α → β)) (arguments : Group α)
    (left : Valid functions) (right : Valid arguments) : Valid (apply functions arguments) := by
  have leftNonnegative := left.2.1
  have rightNonnegative := right.2.1
  refine ⟨apply_live _ _ left.1 right.1, Rat.mul_nonneg left.2.1 right.2.1, ?_⟩
  change 0 < functions.mass * arguments.mass ↔
    0 < Decoder.count functions.members.plan * Decoder.count arguments.members.plan
  constructor
  · intro positive
    have leftPositive : 0 < functions.mass := by
      by_cases live : 0 < functions.mass
      · exact live
      · have zero : functions.mass = 0 := by grind
        simp [zero] at positive
    have rightPositive : 0 < arguments.mass := by
      by_cases live : 0 < arguments.mass
      · exact live
      · have zero : arguments.mass = 0 := by grind
        simp [zero] at positive
    exact Nat.mul_pos (left.2.2.mp leftPositive) (right.2.2.mp rightPositive)
  · intro positive
    exact Rat.mul_pos (left.2.2.mpr (Nat.pos_of_mul_pos_right positive))
      (right.2.2.mpr (Nat.pos_of_mul_pos_left positive))

/-- Product values and probabilities retain the source's independent factor semantics. -/
theorem apply_probability (functions : Group (α → β)) (arguments : Group α) :
    (apply functions arguments).members.sampling.values =
      Probability.map (fun pair => pair.1 pair.2) (product functions.members.sampling.values arguments.members.sampling.values) := rfl

/-- A recursive key has one grouped record at each exact size. -/
abbrev Classes (α : Type) := Nat → Group α

/-- Pay shifts counts, retained masses, decoders, and samplers together. -/
def pay (classes : Classes α) : Classes α
  | 0 => empty
  | size + 1 => classes size

/-- Pay preserves the complete grouped class invariant, including empty size zero. -/
theorem pay_valid (classes : Classes α) (valid : ∀ size, Valid (classes size)) : ∀ size, Valid (pay classes size) := by
  intro size
  cases size with
  | zero => exact empty_valid
  | succ size => exact valid size

/-- Recursive alternatives of the same key merge their mass and member fields at each size. -/
def choice (alternatives : List (Classes α)) : Classes α := fun size => merge (alternatives.map fun classes => classes size)

/-- Every size of a recursive grouped choice retains normalized member sampling and positive rank coverage. -/
theorem choice_valid (alternatives : List (Classes α)) (valid : ∀ classes ∈ alternatives, ∀ size, Valid (classes size)) :
    ∀ size, Valid (choice alternatives size) := by
  intro size
  apply merge_valid
  intro group present
  obtain ⟨classes, member, rfl⟩ := List.mem_map.mp present
  exact valid classes member size

/-- Grouped products enumerate every zero-inclusive size split and choose splits by their product masses. -/
def productClasses (functions : Classes (α → β)) (arguments : Classes α) : Classes β := fun size =>
  merge ((List.range (size + 1)).map fun split => apply (functions split) (arguments (size - split)))

/-- The count, decoder, and mass-weighted product sampler remain coherent across every size split. -/
theorem productClasses_valid (functions : Classes (α → β)) (arguments : Classes α)
    (left : ∀ size, Valid (functions size)) (right : ∀ size, Valid (arguments size)) :
    ∀ size, Valid (productClasses functions arguments size) := by
  intro size
  apply merge_valid
  intro group present
  obtain ⟨split, _, rfl⟩ := List.mem_map.mp present
  exact apply_valid _ _ (left split) (right (size - split))

/-- The product's member stream retains each structural pair at its exact size split. -/
theorem productClasses_values (functions : Classes (α → β)) (arguments : Classes α) (size : Nat) :
    Decoder.values (productClasses functions arguments size).members.plan =
      (List.range (size + 1)).flatMap fun split =>
        Decoder.applyValues (Decoder.values (functions split).members.plan) (Decoder.values (arguments (size - split)).members.plan) := by
  simp [productClasses, merge_values, List.flatMap_map, apply, applyRecord, Decoder.values]

/-- Split probabilities use retained masses while rank offsets use structural counts. -/
theorem productClasses_probability (functions : Classes (α → β)) (arguments : Classes α) (size : Nat) :
    (productClasses functions arguments size).members.sampling.values =
      weightedChoice ((List.range (size + 1)).map fun split =>
        (Decoder.count (functions split).members.plan * Decoder.count (arguments (size - split)).members.plan,
          (functions split).mass * (arguments (size - split)).mass,
          Probability.map (fun pair => pair.1 pair.2)
            (product (functions split).members.sampling.values (arguments (size - split)).members.sampling.values))) := by
  simp [productClasses, merge_probability, List.map_map, Function.comp_def, apply, applyRecord, Decoder.count, Sampler.productSampler]

/-- Bounding chooses sizes by count; retained masses still control each key's within-class distribution. -/
def bounded (classes : Classes α) (bound : Nat) : Record α := boundedRecord (fun size => (classes size).members) bound

/-- A bounded grouped language has a coherent finite decoder and exact normalized sampler. -/
theorem bounded_valid (classes : Classes α) (valid : ∀ size, Valid (classes size)) (bound : Nat) :
    LiveValid (bounded classes bound) := bounded_live _ _ (fun size => (valid size).1)

/-- Public recursive counts retain a key precisely when that class has structural members. -/
def counts (groups : List (Key × Group α)) : List (Key × Nat) :=
  groups.filterMap fun (key, group) =>
    if 0 < Decoder.count group.members.plan then some (key, Decoder.count group.members.plan) else none

/-- Public recursive mass inspection normalizes exactly the positive retained key masses. -/
def masses (groups : List (Key × Group α)) : Distribution Key :=
  normalize (groups.filterMap fun (key, group) => if 0 < group.mass then some (group.mass, key) else none)

/-- Counts and masses identify the same live entries when grouped records are coherent. -/
theorem counts_mass_filter (groups : List (Key × Group α)) (valid : ∀ entry ∈ groups, Valid entry.2) :
    groups.filter (fun entry => decide (0 < Decoder.count entry.2.members.plan)) =
      groups.filter (fun entry => decide (0 < entry.2.mass)) := by
  apply List.filter_congr
  intro entry present
  simp only [(valid entry present).2.2]

end MicroCFTA.GroupedRecord
