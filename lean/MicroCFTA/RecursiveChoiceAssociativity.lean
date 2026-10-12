import MicroCFTA.RecursiveRankMass

/-!
# Flat and nested count-weighted alternatives

Grouping consecutive branches preserves the ordered probability fields.
Empty branches have no mass and retain their structural count of zero.
-/
namespace MicroCFTA.RecursiveChoiceAssociativity
open Probability Sampler SamplerReplay FiniteSource

/-- Retain the declared natural count next to each child distribution. -/
abbrev Branch (α : Type) := Nat × Distribution α

/-- Total member count before the sampler removes empty branches. -/
def amount (branches : List (Branch α)) : Nat := (branches.map Prod.fst).sum

/-- The source sampler removes count-zero branches before normalization. -/
def live : List (Branch α) → List (Rat × Distribution α)
  | [] => []
  | branch :: rest => if 0 < branch.1 then ((branch.1 : Rat), branch.2) :: live rest else live rest

/-- An exact count-weighted choice preserves every run in each live branch. -/
def law (branches : List (Branch α)) : Distribution α := frequency (live branches)

/-- Removing zero counts does not change the normalization denominator. -/
theorem live_weight (branches : List (Branch α)) :
    branchWeight (live branches) = (amount branches : Rat) := by
  induction branches with
  | nil => rfl
  | cons branch rest ih =>
      simp only [live]
      by_cases positive : 0 < branch.1
      · simp only [positive, ↓reduceIte, branchWeight]
        rw [ih]
        simp [amount, Rat.natCast_add]
      · have zero : branch.1 = 0 := by omega
        simpa [zero, amount, live] using ih

/-- No count means no retained branch, even if an invalid child supplied runs. -/
theorem live_empty (branches : List (Branch α)) (zero : amount branches = 0) :
    live branches = [] := by
  induction branches with
  | nil => rfl
  | cons branch rest ih =>
      have counts : branch.1 = 0 ∧ amount rest = 0 := by
        simpa only [amount, List.map_cons, List.sum_cons, Nat.add_eq_zero_iff] using zero
      simp [live, counts.1, ih counts.2]

/-- Regrouping restores the exact unnormalized ordered child runs. -/
theorem restore_law (branches : List (Branch α))
    (positive : 0 < amount branches) :
    scale (amount branches : Rat) (law branches) = mix (live branches) := by
  rw [law, frequency, live_weight, scale_scale]
  have nonzero : (amount branches : Rat) ≠ 0 := Rat.ne_of_gt (Rat.natCast_pos.mpr positive)
  rw [Rat.mul_inv_cancel _ nonzero, scale_one]

/-- A group of zero total count contributes no rows to the parent choice. -/
theorem grouped_mix (branches : List (Branch α)) :
    mix (live [(amount branches, law branches)]) = mix (live branches) := by
  by_cases positive : 0 < amount branches
  · simpa [live, positive, mix] using restore_law branches positive
  · have zero : amount branches = 0 := by omega
    simp [live_empty branches zero, live, zero, mix]

/-- One child followed by a grouped suffix has the same exact ordered law. -/
theorem law_cons (first : Branch α) (rest : List (Branch α)) :
    law [first, (amount rest, law rest)] = law (first :: rest) := by
  change scale (branchWeight (live [first, (amount rest, law rest)]))⁻¹
      (mix (live [first, (amount rest, law rest)])) =
    scale (branchWeight (live (first :: rest)))⁻¹ (mix (live (first :: rest)))
  rw [live_weight, live_weight]
  have counts : amount [first, (amount rest, law rest)] = amount (first :: rest) := by
    simp [amount]
  rw [counts]
  congr 1
  have grouped := grouped_mix rest
  by_cases positive : 0 < first.1
  · simpa only [live, positive, ↓reduceIte, mix, law] using
      congrArg (scale (first.1 : Rat) first.2 ++ ·) grouped
  · simpa only [live, positive, ↓reduceIte, law] using grouped

/-- Mapping preserves counts and commutes with the complete ordered law. -/
theorem law_map (transform : α → β) (branches : List (Branch α)) :
    law (branches.map fun branch => (branch.1, Probability.map transform branch.2)) =
      Probability.map transform (law branches) := by
  rw [law, law, map_frequency]
  congr 1
  induction branches with
  | nil => rfl
  | cons first rest ih => simp only [List.map_cons, live]; split <;> simp_all

/-- The record's source value field is the natural-count law. -/
theorem countChoice_values (records : List (Record α)) :
    (countChoice records).sampling.values =
      law (records.map fun record => (Decoder.count record.plan, record.sampling.values)) := by
  rw [countChoice, many_values]
  unfold weightedChoice law
  congr 1
  induction records with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.map_cons, List.filterMap_cons, live]
      by_cases positive : 0 < Decoder.count first.plan
      · have mass : (0 : Rat) < Decoder.count first.plan := Rat.natCast_pos.mpr positive
        simp only [positive, mass, and_self, ↓reduceIte]
        exact congrArg (_ :: ·) ih
      · simp only [positive, false_and, ↓reduceIte]
        exact ih

/-- Branch rank offsets advance by the declared count, including empty branches. -/
def rankBranches (offset : Nat) : List (Record α) → List (Branch (Nat × α))
  | [] => []
  | first :: rest =>
      (Decoder.count first.plan,
        Probability.map (fun entry => (offset + entry.1, entry.2)) first.sampling.ranked) ::
      rankBranches (offset + Decoder.count first.plan) rest

/-- The actual choice parts contain exactly these natural-count ranked branches. -/
theorem parts_live (records : List (Record α)) (offset : Nat) :
    (choiceParts offset (alternatives (records.map fun record => ((Decoder.count record.plan : Rat), record)))).map
      (fun part => (part.mass, Probability.map (fun entry => (part.offset + entry.1, entry.2)) part.sampling.ranked)) =
      live (rankBranches offset records) := by
  induction records generalizing offset with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.map_cons, alternatives, choiceParts, rankBranches, live]
      by_cases positive : 0 < Decoder.count first.plan
      · have mass : (0 : Rat) < Decoder.count first.plan := Rat.natCast_pos.mpr positive
        simp only [positive, mass, and_self, ↓reduceIte, List.map_cons]
        congr 1
        exact ih _
      · simp only [positive, false_and, ↓reduceIte]
        exact ih _

/-- Flat source choice has the exact ranked law before duplicate values are projected. -/
theorem countChoice_ranked (records : List (Record α)) :
    (countChoice records).sampling.ranked = law (rankBranches 0 records) := by
  change frequency (_) = frequency (_)
  rw [parts_live]

/-- Structural counts are the sum of the original child counts. -/
theorem countChoice_count (records : List (Record α)) :
    Decoder.count (countChoice records).plan = (records.map fun record => Decoder.count record.plan).sum := by
  induction records with
  | nil => rfl
  | cons first rest ih =>
      simpa only [countChoice, manyRecord, List.map_cons, manyPlan, Decoder.count, List.sum_cons] using
        congrArg (Decoder.count first.plan + ·) ih

/-- Rank offsets do not change the normalization denominator. -/
theorem rankBranches_amount (records : List (Record α)) (offset : Nat) :
    amount (rankBranches offset records) = Decoder.count (countChoice records).plan := by
  rw [countChoice_count]
  induction records generalizing offset with
  | nil => rfl
  | cons first rest ih => simp only [rankBranches, amount, List.map_cons, List.sum_cons]; exact congrArg _ (ih _)

/-- A parent offset changes only the ranks in every retained source run. -/
theorem rankBranches_shift (records : List (Record α)) (offset base : Nat) :
    rankBranches (offset + base) records =
      (rankBranches base records).map fun branch =>
        (branch.1, Probability.map (fun entry => (offset + entry.1, entry.2)) branch.2) := by
  induction records generalizing base with
  | nil => rfl
  | cons first rest ih =>
      simp only [rankBranches, List.map_cons]
      congr 1
      · simp [Probability.map, List.map_map, Function.comp_def, Nat.add_assoc]
      · simpa only [Nat.add_assoc] using ih (base + Decoder.count first.plan)

/-- Offsets commute with count normalization, including empty choices. -/
theorem law_rankBranches_shift (records : List (Record α)) (offset : Nat) :
    law (rankBranches offset records) =
      Probability.map (fun entry => (offset + entry.1, entry.2)) (law (rankBranches 0 records)) := by
  have shifted := rankBranches_shift records offset 0
  rw [Nat.add_zero] at shifted
  rw [shifted, law_map]

/-- Grouping a suffix preserves the entire flat source value distribution. -/
theorem countChoice_cons_values (first : Record α) (rest : List (Record α)) :
    (countChoice [first, countChoice rest]).sampling.values =
      (countChoice (first :: rest)).sampling.values := by
  rw [countChoice_values, countChoice_values]
  simp only [List.map_cons, List.map_nil, countChoice_values, countChoice_count]
  simpa only [amount, List.map_map, Function.comp_def] using
    law_cons (Decoder.count first.plan, first.sampling.values)
      (rest.map fun record => (Decoder.count record.plan, record.sampling.values))

/-- Grouping a suffix preserves exact rank, value, mass, and run order. -/
theorem countChoice_cons_ranked (first : Record α) (rest : List (Record α)) :
    (countChoice [first, countChoice rest]).sampling.ranked =
      (countChoice (first :: rest)).sampling.ranked := by
  rw [countChoice_ranked, countChoice_ranked]
  simp only [rankBranches, Nat.zero_add]
  rw [countChoice_ranked, ← law_rankBranches_shift]
  rw [← rankBranches_amount rest (Decoder.count first.plan)]
  simpa only [Probability.map, List.map_id_fun] using
    law_cons (Decoder.count first.plan,
      Probability.map (fun entry : Nat × α => (entry.1, entry.2)) first.sampling.ranked)
      (rankBranches (Decoder.count first.plan) rest)

/-- A positive singleton retains its exact child law. -/
theorem law_single (count : Nat) (distribution : Distribution α) (positive : 0 < count) :
    law [(count, distribution)] = distribution := by
  simp only [law, live, positive, ↓reduceIte, frequency, branchWeight, mix, Rat.add_zero,
    List.append_nil, scale_scale]
  rw [Rat.inv_mul_cancel _ (Rat.ne_of_gt (Rat.natCast_pos.mpr positive)), scale_one]

/-- Valid replay excludes all sampled runs from a zero-count record. -/
theorem zero_sampling (record : Record α) (coherent : Coherent record)
    (zero : Decoder.count record.plan = 0) :
    record.sampling.ranked = [] ∧ record.sampling.values = [] := by
  have ranked : record.sampling.ranked = [] := by
    cases found : record.sampling.ranked with
    | nil => rfl
    | cons first rest =>
        have selected := coherent.2 first (by simp [found])
        have bound := decoded_bound record.plan _ _ selected
        omega
  refine ⟨ranked, ?_⟩
  rw [← coherent.1, ranked]
  rfl

/-- A singleton source choice keeps the exact child value and ranked distributions. -/
theorem countChoice_single (record : Record α) (coherent : Coherent record) :
    (countChoice [record]).sampling.values = record.sampling.values ∧
      (countChoice [record]).sampling.ranked = record.sampling.ranked := by
  rw [countChoice_values, countChoice_ranked]
  simp only [List.map_cons, List.map_nil, rankBranches, Nat.zero_add]
  by_cases positive : 0 < Decoder.count record.plan
  · rw [law_single _ _ positive, law_single _ _ positive]
    exact ⟨rfl, by simp [Probability.map]⟩
  · have zero : Decoder.count record.plan = 0 := by omega
    obtain ⟨ranked, values⟩ := zero_sampling record coherent zero
    simp [law, live, zero, ranked, values, frequency, mix, scale]

/-- Equal child counts and sampler fields give equal choice value and ranked fields. -/
theorem countChoice_fields_congr (left : List (Record α)) (right : List (Record α))
    (related : RecursiveRankMass.Related (fun first second =>
      Decoder.count first.plan = Decoder.count second.plan ∧
      first.sampling.values = second.sampling.values ∧
      first.sampling.ranked = second.sampling.ranked) left right) :
    (countChoice left).sampling.values = (countChoice right).sampling.values ∧
      (countChoice left).sampling.ranked = (countChoice right).sampling.ranked := by
  constructor
  · rw [countChoice_values, countChoice_values]
    congr 1
    induction related with
    | nil => rfl
    | cons fields remaining ih => simp only [List.map_cons]; rw [fields.1, fields.2.1, ih]
  · rw [countChoice_ranked, countChoice_ranked]
    congr 1
    have aligned : ∀ offset, rankBranches offset left = rankBranches offset right := by
      intro offset
      induction related generalizing offset with
      | nil => rfl
      | cons fields remaining ih => simp only [rankBranches]; rw [fields.1, fields.2.2, ih]
    exact aligned 0

end MicroCFTA.RecursiveChoiceAssociativity
