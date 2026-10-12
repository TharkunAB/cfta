import MicroCFTA.GroupedRecord
import MicroCFTA.RecursiveChoiceAssociativity

/-!
# Flat and nested mass-weighted grouped alternatives

Rank offsets use counts. Choice probabilities use the separate key masses.
Regrouping a suffix preserves both fields and the complete ordered runs.
-/
namespace MicroCFTA.GroupedMergeAssociativity
open Probability Sampler SamplerReplay

/-- One branch retains its structural count, key mass, and conditional law. -/
abbrev Branch (α : Type) := Nat × Rat × Distribution α

/-- Valid key masses are nonnegative and live exactly when the count is live. -/
def Proper (branch : Branch α) : Prop :=
  0 ≤ branch.2.1 ∧ (0 < branch.2.1 ↔ 0 < branch.1)

def amount (branches : List (Branch α)) : Nat := (branches.map Prod.fst).sum

def weight : List (Branch α) → Rat
  | [] => 0
  | first :: rest => first.2.1 + weight rest

/-- The source removes zero-count or nonpositive-mass branches before sampling. -/
def live : List (Branch α) → List (Rat × Distribution α)
  | [] => []
  | first :: rest => if 0 < first.1 ∧ 0 < first.2.1 then (first.2.1, first.2.2) :: live rest else live rest

def law (branches : List (Branch α)) : Distribution α := frequency (live branches)

/-- The normalization denominator is the sum of every declared valid key mass. -/
theorem live_weight (branches : List (Branch α)) (proper : ∀ branch ∈ branches, Proper branch) :
    branchWeight (live branches) = weight branches := by
  induction branches with
  | nil => rfl
  | cons first rest ih =>
      have head := proper first (by simp)
      have tail := ih (fun branch member => proper branch (by simp [member]))
      by_cases positive : 0 < first.1
      · simp only [live, positive, head.2.mpr positive, and_self, ↓reduceIte, branchWeight, weight, tail]
      · have zero : first.2.1 = 0 := by
          have absent : ¬0 < first.2.1 := fun mass => positive (head.2.mp mass)
          have nonnegative := head.1
          grind
        simp [live, positive, weight, zero, tail, Rat.zero_add]

/-- Aggregate mass is positive exactly when an original branch has a member. -/
theorem weight_live (branches : List (Branch α)) (proper : ∀ branch ∈ branches, Proper branch) :
    0 ≤ weight branches ∧ (0 < weight branches ↔ 0 < amount branches) := by
  induction branches with
  | nil => simp [weight, amount]
  | cons first rest ih =>
      have head := proper first (by simp)
      have tail := ih (fun branch member => proper branch (by simp [member]))
      have firstNonnegative := head.1
      have tailNonnegative := tail.1
      simp only [weight, amount, List.map_cons, List.sum_cons]
      constructor
      · grind
      · constructor
        · intro positive
          by_cases firstLive : 0 < first.1
          · omega
          · have firstZero : first.2.1 = 0 := by
              have absent : ¬0 < first.2.1 := fun live => firstLive (head.2.mp live)
              grind
            have restLive := tail.2.mp (by simpa [firstZero, Rat.zero_add] using positive)
            change 0 < (rest.map Prod.fst).sum at restLive
            omega
        · intro positive
          have cases : 0 < first.1 ∨ 0 < amount rest := by simp only [amount]; omega
          rcases cases with firstLive | restLive
          · have massPositive := head.2.mpr firstLive
            grind
          · have massPositive := tail.2.mpr restLive
            grind

/-- An empty structural suffix supplies no sampled branch. -/
theorem live_empty (branches : List (Branch α)) (zero : amount branches = 0) : live branches = [] := by
  induction branches with
  | nil => rfl
  | cons first rest ih =>
      have counts : first.1 = 0 ∧ amount rest = 0 := by
        simpa only [amount, List.map_cons, List.sum_cons, Nat.add_eq_zero_iff] using zero
      simp [live, counts.1, ih counts.2]

/-- Restoring a group's mass recovers its exact original ordered runs. -/
theorem grouped_mix (branches : List (Branch α)) (proper : ∀ branch ∈ branches, Proper branch) :
    mix (live [(amount branches, weight branches, law branches)]) = mix (live branches) := by
  have valid := weight_live branches proper
  by_cases positive : 0 < amount branches
  · have mass := valid.2.mpr positive
    simp only [live, positive, mass, and_self, ↓reduceIte, mix, List.append_nil]
    rw [law, frequency, live_weight branches proper, scale_scale,
      Rat.mul_inv_cancel _ (Rat.ne_of_gt mass), scale_one]
  · have zero : amount branches = 0 := by omega
    simp [live, zero, live_empty branches zero, mix]

/-- A child followed by a grouped suffix has the same exact normalized law. -/
theorem law_cons (first : Branch α) (rest : List (Branch α))
    (properFirst : Proper first) (properRest : ∀ branch ∈ rest, Proper branch) :
    law [first, (amount rest, weight rest, law rest)] = law (first :: rest) := by
  have groupedProper : Proper (amount rest, weight rest, law rest) := weight_live rest properRest
  have properGrouped : ∀ branch ∈ [first, (amount rest, weight rest, law rest)], Proper branch := by
    intro branch member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> assumption
  have properAll : ∀ branch ∈ first :: rest, Proper branch := by
    intro branch member
    rcases List.mem_cons.mp member with rfl | member
    · exact properFirst
    · exact properRest branch member
  change scale (branchWeight (live _))⁻¹ (mix (live _)) = scale (branchWeight (live _))⁻¹ (mix (live _))
  rw [live_weight _ properGrouped, live_weight _ properAll]
  simp only [weight, Rat.add_zero]
  congr 1
  have grouped := grouped_mix rest properRest
  by_cases positive : 0 < first.1 ∧ 0 < first.2.1
  · simpa only [live, positive, and_self, ↓reduceIte, mix] using congrArg (scale first.2.1 first.2.2 ++ ·) grouped
  · simpa only [live, positive, ↓reduceIte] using grouped

/-- Mapping outcomes commutes with mass normalization without changing counts. -/
theorem law_map (transform : α → β) (branches : List (Branch α)) :
    law (branches.map fun branch => (branch.1, branch.2.1, Probability.map transform branch.2.2)) =
      Probability.map transform (law branches) := by
  rw [law, law, map_frequency]
  congr 1
  induction branches with
  | nil => rfl
  | cons first rest ih => simp only [List.map_cons, live]; split <;> simp_all

/-- One value branch reads the source group without changing either scale. -/
def valueBranch (group : GroupedRecord.Group α) : Branch α :=
  (Decoder.count group.members.plan, group.mass, group.members.sampling.values)

theorem value_proper (group : GroupedRecord.Group α) (valid : GroupedRecord.Valid group) : Proper (valueBranch group) := valid.2

/-- The source value sampler is the exact weighted branch law. -/
theorem merge_values_law (groups : List (GroupedRecord.Group α)) :
    (GroupedRecord.merge groups).members.sampling.values = law (groups.map valueBranch) := by
  rw [GroupedRecord.merge_probability]
  unfold weightedChoice law
  congr 1
  induction groups with
  | nil => rfl
  | cons first rest ih => simp only [List.map_cons, List.filterMap_cons, live, valueBranch]; split <;> simp_all

/-- Rank branches retain each original source count offset and key mass. -/
def rankBranches (offset : Nat) : List (GroupedRecord.Group α) → List (Branch (Nat × α))
  | [] => []
  | first :: rest =>
      (Decoder.count first.members.plan, first.mass,
        Probability.map (fun entry => (offset + entry.1, entry.2)) first.members.sampling.ranked) ::
      rankBranches (offset + Decoder.count first.members.plan) rest

/-- Valid grouped producers supply the local positive-mass metadata. -/
theorem ranks_proper (groups : List (GroupedRecord.Group α))
    (valid : ∀ group ∈ groups, GroupedRecord.Valid group) (offset : Nat) :
    ∀ branch ∈ rankBranches offset groups, Proper branch := by
  induction groups generalizing offset with
  | nil => simp [rankBranches]
  | cons first rest ih =>
      intro branch member
      rcases List.mem_cons.mp member with rfl | member
      · exact (valid first (by simp)).2
      · exact ih (fun group present => valid group (by simp [present])) _ branch member

/-- The live ranked branches are exactly the source offset worker's rows. -/
theorem parts_live (groups : List (GroupedRecord.Group α)) (offset : Nat) :
    (choiceParts offset (alternatives (groups.map fun group => (group.mass, group.members)))).map
      (fun part => (part.mass, Probability.map (fun entry => (part.offset + entry.1, entry.2)) part.sampling.ranked)) =
      live (rankBranches offset groups) := by
  induction groups generalizing offset with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.map_cons, alternatives, choiceParts, rankBranches, live]
      split
      · simp only [List.map_cons]
        exact congrArg (_ :: ·) (ih _)
      · exact ih _

/-- Grouped selection preserves every sampled source rank before value projection. -/
theorem merge_ranked_law (groups : List (GroupedRecord.Group α)) :
    (GroupedRecord.merge groups).members.sampling.ranked = law (rankBranches 0 groups) := by
  change frequency (_) = frequency (_)
  rw [parts_live]

theorem value_totals (groups : List (GroupedRecord.Group α)) :
    amount (groups.map valueBranch) = GroupedRecord.countSum groups ∧
      weight (groups.map valueBranch) = GroupedRecord.massSum groups := by
  induction groups with
  | nil => exact ⟨rfl, rfl⟩
  | cons first rest ih => simp [amount, weight, valueBranch, GroupedRecord.countSum, GroupedRecord.massSum, ih.2] at *; omega

theorem rank_totals (groups : List (GroupedRecord.Group α)) (offset : Nat) :
    amount (rankBranches offset groups) = GroupedRecord.countSum groups ∧
      weight (rankBranches offset groups) = GroupedRecord.massSum groups := by
  induction groups generalizing offset with
  | nil => exact ⟨rfl, rfl⟩
  | cons first rest ih =>
      have tail := ih (offset + Decoder.count first.members.plan)
      simp only [rankBranches, amount, List.map_cons, List.sum_cons, weight, GroupedRecord.countSum, GroupedRecord.massSum]
      exact ⟨congrArg _ tail.1, congrArg _ tail.2⟩

/-- A parent offset changes only ranks, not any choice mass. -/
theorem rankBranches_shift (groups : List (GroupedRecord.Group α)) (offset base : Nat) :
    rankBranches (offset + base) groups =
      (rankBranches base groups).map fun branch =>
        (branch.1, branch.2.1, Probability.map (fun entry => (offset + entry.1, entry.2)) branch.2.2) := by
  induction groups generalizing base with
  | nil => rfl
  | cons first rest ih =>
      simp only [rankBranches, List.map_cons]
      congr 1
      · simp [Probability.map, List.map_map, Function.comp_def, Nat.add_assoc]
      · simpa only [Nat.add_assoc] using ih (base + Decoder.count first.members.plan)

theorem law_rankBranches_shift (groups : List (GroupedRecord.Group α)) (offset : Nat) :
    law (rankBranches offset groups) =
      Probability.map (fun entry => (offset + entry.1, entry.2)) (law (rankBranches 0 groups)) := by
  have shifted := rankBranches_shift groups offset 0
  rw [Nat.add_zero] at shifted
  rw [shifted, law_map]

theorem merge_mass (groups : List (GroupedRecord.Group α)) :
    (GroupedRecord.merge groups).mass = GroupedRecord.massSum groups := rfl

/-- Grouping a valid suffix preserves the full ordered value distribution. -/
theorem merge_cons_values (first : GroupedRecord.Group α) (rest : List (GroupedRecord.Group α))
    (firstValid : GroupedRecord.Valid first) (restValid : ∀ group ∈ rest, GroupedRecord.Valid group) :
    (GroupedRecord.merge [first, GroupedRecord.merge rest]).members.sampling.values =
      (GroupedRecord.merge (first :: rest)).members.sampling.values := by
  rw [merge_values_law, merge_values_law]
  simp only [List.map_cons, List.map_nil, valueBranch, GroupedRecord.merge_count, merge_values_law, merge_mass]
  rw [← (value_totals rest).1, ← (value_totals rest).2]
  exact law_cons (valueBranch first) (rest.map valueBranch) firstValid.2 (by
    intro branch member
    obtain ⟨group, present, rfl⟩ := List.mem_map.mp member
    exact (restValid group present).2)

/-- Grouping a suffix preserves complete rank/value/mass runs in the original order. -/
theorem merge_cons_ranked (first : GroupedRecord.Group α) (rest : List (GroupedRecord.Group α))
    (firstValid : GroupedRecord.Valid first) (restValid : ∀ group ∈ rest, GroupedRecord.Valid group) :
    (GroupedRecord.merge [first, GroupedRecord.merge rest]).members.sampling.ranked =
      (GroupedRecord.merge (first :: rest)).members.sampling.ranked := by
  rw [merge_ranked_law, merge_ranked_law]
  simp only [rankBranches, Nat.zero_add, GroupedRecord.merge_count, merge_mass]
  rw [merge_ranked_law, ← law_rankBranches_shift]
  rw [← (rank_totals rest (Decoder.count first.members.plan)).1,
    ← (rank_totals rest (Decoder.count first.members.plan)).2]
  exact law_cons _ _ firstValid.2 (ranks_proper rest restValid _)

/-- A live singleton's normalization retains its exact original distribution. -/
theorem law_single (count : Nat) (mass : Rat) (distribution : Distribution α)
    (countPositive : 0 < count) (massPositive : 0 < mass) :
    law [(count, mass, distribution)] = distribution := by
  simp only [law, live, countPositive, massPositive, and_self, ↓reduceIte, frequency, branchWeight,
    mix, Rat.add_zero, List.append_nil, scale_scale]
  rw [Rat.inv_mul_cancel _ (Rat.ne_of_gt massPositive), scale_one]

/-- Compare the observable group fields without requiring identical plan trees. -/
def Fields (left right : GroupedRecord.Group α) : Prop :=
  left.mass = right.mass ∧ Decoder.values left.members.plan = Decoder.values right.members.plan ∧
    left.members.sampling.values = right.members.sampling.values ∧
    left.members.sampling.ranked = right.members.sampling.ranked

theorem fields_count (left right : GroupedRecord.Group α) (same : Fields left right) :
    Decoder.count left.members.plan = Decoder.count right.members.plan := by
  rw [Decoder.count_correct, Decoder.count_correct, same.2.1]

/-- All source-visible fields agree when the suffix is grouped once. -/
theorem merge_cons (first : GroupedRecord.Group α) (rest : List (GroupedRecord.Group α))
    (firstValid : GroupedRecord.Valid first) (restValid : ∀ group ∈ rest, GroupedRecord.Valid group) :
    Fields (GroupedRecord.merge [first, GroupedRecord.merge rest]) (GroupedRecord.merge (first :: rest)) := by
  refine ⟨by simp [merge_mass, GroupedRecord.massSum, Rat.add_zero], ?_,
    merge_cons_values first rest firstValid restValid, merge_cons_ranked first rest firstValid restValid⟩
  simp [GroupedRecord.merge_values]

/-- Empty and live singleton classes both retain every source-visible field. -/
theorem merge_single (group : GroupedRecord.Group α) (valid : GroupedRecord.Valid group) :
    Fields (GroupedRecord.merge [group]) group := by
  refine ⟨by simp [merge_mass, GroupedRecord.massSum, Rat.add_zero], by simp [GroupedRecord.merge_values], ?_⟩
  rw [merge_values_law, merge_ranked_law]
  simp only [List.map_cons, List.map_nil, valueBranch, rankBranches, Nat.zero_add]
  by_cases positive : 0 < Decoder.count group.members.plan
  · rw [law_single _ _ _ positive (valid.2.2.mpr positive), law_single _ _ _ positive (valid.2.2.mpr positive)]
    exact ⟨rfl, by simp [Probability.map]⟩
  · have zero : Decoder.count group.members.plan = 0 := by omega
    obtain ⟨ranked, values⟩ := RecursiveChoiceAssociativity.zero_sampling group.members valid.1.1 zero
    simp [law, live, zero, ranked, values, frequency, mix, scale]

/-- Equal child fields produce identical observable fields in the flat choice. -/
theorem merge_fields_congr (left right : List (GroupedRecord.Group α))
    (related : RecursiveRankMass.Related Fields left right) :
    Fields (GroupedRecord.merge left) (GroupedRecord.merge right) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [merge_mass]
    induction related with
    | nil => rfl
    | cons fields remaining ih => simp only [GroupedRecord.massSum]; rw [fields.1, ih]
  · rw [GroupedRecord.merge_values, GroupedRecord.merge_values]
    induction related with
    | nil => rfl
    | cons fields remaining ih => simp only [List.flatMap_cons]; rw [fields.2.1, ih]
  · rw [merge_values_law, merge_values_law]
    congr 1
    induction related with
    | nil => rfl
    | cons fields remaining ih =>
        simp only [List.map_cons, valueBranch]
        rw [fields_count _ _ fields, fields.1, fields.2.2.1, ih]
  · rw [merge_ranked_law, merge_ranked_law]
    congr 1
    have aligned : ∀ offset, rankBranches offset left = rankBranches offset right := by
      intro offset
      induction related generalizing offset with
      | nil => rfl
      | cons fields remaining ih =>
          simp only [rankBranches]
          rw [fields_count _ _ fields, fields.1, fields.2.2.2, ih]
    exact aligned 0

/-- The empty merge has exactly the empty grouped record's observable fields. -/
theorem merge_empty : Fields (GroupedRecord.merge ([] : List (GroupedRecord.Group α))) GroupedRecord.empty := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end MicroCFTA.GroupedMergeAssociativity
