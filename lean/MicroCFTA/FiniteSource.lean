import MicroCFTA.SamplerReplay

/-!
# Finite source records and exact-size sampling

This executable source algebra follows the finite `Static` composition rules.
Finite branch weights choose whole alternatives. Size classes choose by member
counts and retain component atomic distributions. Pure has size zero; sources
have size one; pay increments size; products add sizes. Counts and decoder
plans are constructed with the samplers, not supplied as desired postconditions.
-/

namespace MicroCFTA.FiniteSource
open Probability SamplerReplay

/-- Positive finite sources and choices after their public input checks. -/
inductive Source : Type → Type 1 where
  | source (outcomes : Distribution α) (positive : ∀ entry ∈ outcomes, 0 < entry.1) : Source α
  | pure (value : α) : Source α
  | map (transform : α → β) (inner : Source α) : Source β
  | pay (inner : Source α) : Source α
  | atomic (inner : Source α) : Source α
  | shared (key : Nat) (inner : Source α) : Source α
  | choice (leftWeight rightWeight : Rat) (leftPositive : 0 < leftWeight) (rightPositive : 0 < rightWeight)
      (left right : Source α) : Source α
  | ap (functions : Source (α → β)) (arguments : Source α) : Source β
  | sized (classes : Nat → Distribution α) (positive : ∀ size entry, entry ∈ classes size → 0 < entry.1)
      (bound : Nat) : Source α

/-- Whole-language finite records preserve their declared source and branch probabilities. -/
def finite : Source α → Record α
  | .source outcomes _ => SamplerReplay.source outcomes
  | .pure value => SamplerReplay.source [(1, value)]
  | .map transform inner => mapRecord transform (finite inner)
  | .pay inner | .atomic inner | .shared _ inner => finite inner
  | .choice lw rw _ _ left right => manyRecord [(lw, finite left), (rw, finite right)]
  | .ap functions arguments => applyRecord (finite functions) (finite arguments)
  | .sized classes _ bound => boundedRecord (fun size => SamplerReplay.source (classes size)) bound

/-- Empty size classes contain no replay ranks. -/
def empty : Record α := SamplerReplay.source []

/-- Choose class alternatives by their derived member counts. -/
def countChoice (records : List (Record α)) : Record α :=
  manyRecord (records.map fun record => ((Decoder.count record.plan : Rat), record))

/-- Build exact-size records using the source's finite and atomic weighting policy. -/
def atSize : Source α → Nat → Record α
  | .source outcomes _, size => if size = 1 then SamplerReplay.source (counting (outcomes.map Prod.snd)) else empty
  | .pure value, size => if size = 0 then SamplerReplay.source [(1, value)] else empty
  | .map transform inner, size => mapRecord transform (atSize inner size)
  | .pay inner, size => match size with | 0 => empty | next + 1 => atSize inner next
  | .atomic inner, size => if size = 1 then finite inner else empty
  | .shared _ inner, size => atSize inner size
  | .choice _ _ _ _ left right, size => countChoice [atSize left size, atSize right size]
  | .ap functions arguments, size => countChoice ((List.range (size + 1)).map fun split =>
      applyRecord (atSize functions split) (atSize arguments (size - split)))
  | .sized classes _ bound, size => if size ≤ bound then SamplerReplay.source (classes size) else empty

/-- The independent whole-language member list retains every source occurrence. -/
def members : Source α → List α
  | .source outcomes _ => outcomes.map Prod.snd
  | .pure value => [value]
  | .map transform inner => (members inner).map transform
  | .pay inner | .atomic inner | .shared _ inner => members inner
  | .choice _ _ _ _ left right => members left ++ members right
  | .ap functions arguments => Decoder.applyValues (members functions) (members arguments)
  | .sized classes _ bound => (List.range (bound + 1)).flatMap fun size => (classes size).map Prod.snd

/-- The independent exact-size member language uses all nonnegative product splits. -/
def classMembers : Source α → Nat → List α
  | .source outcomes _, size => if size = 1 then outcomes.map Prod.snd else []
  | .pure value, size => if size = 0 then [value] else []
  | .map transform inner, size => (classMembers inner size).map transform
  | .pay inner, size => match size with | 0 => [] | next + 1 => classMembers inner next
  | .atomic inner, size => if size = 1 then members inner else []
  | .shared _ inner, size => classMembers inner size
  | .choice _ _ _ _ left right, size => classMembers left size ++ classMembers right size
  | .ap functions arguments, size => (List.range (size + 1)).flatMap fun split =>
      Decoder.applyValues (classMembers functions split) (classMembers arguments (size - split))
  | .sized classes _ bound, size => if size ≤ bound then (classes size).map Prod.snd else []

/-- Count-weighted choice preserves every member, including those in repeated branches. -/
theorem countChoice_members (records : List (Record α)) :
    Decoder.values (countChoice records).plan = records.flatMap (fun record => Decoder.values record.plan) := by
  simp [countChoice, manyRecord, manyPlan_values, List.flatMap_map]

/-- Whole-language decoding has exactly the independent member semantics. -/
theorem finite_members (description : Source α) : Decoder.values (finite description).plan = members description := by
  induction description with
  | source outcomes positive => rfl
  | pure value => rfl
  | map transform inner ih => simp [finite, mapRecord, Decoder.values, members, ih]
  | pay inner ih | atomic inner ih | shared key inner ih => exact ih
  | choice lw rw lp rp left right ihl ihr =>
      simp [finite, manyRecord, manyPlan_values, members, ihl, ihr]
  | ap functions arguments ihf iha => simp [finite, applyRecord, members, Decoder.values, ihf, iha]
  | sized classes positive bound =>
      simp [finite, boundedRecord, manyRecord, manyPlan_values, SamplerReplay.source, members,
        Decoder.values, List.flatMap_map]

/-- Exact-size decoding has precisely the independent exact-size member language. -/
theorem class_members (description : Source α) (size : Nat) :
    Decoder.values (atSize description size).plan = classMembers description size := by
  induction description generalizing size with
  | source outcomes positive =>
      by_cases same : size = 1 <;>
        simp [atSize, classMembers, same, empty, SamplerReplay.source, Decoder.values, counting, List.map_map, Function.comp_def]
  | pure value =>
      by_cases same : size = 0 <;> simp [atSize, classMembers, same, empty, SamplerReplay.source, Decoder.values]
  | map transform inner ih => simp [atSize, classMembers, mapRecord, Decoder.values, ih]
  | pay inner ih => cases size <;> simp [atSize, classMembers, empty, SamplerReplay.source, Decoder.values, ih]
  | atomic inner ih =>
      by_cases same : size = 1 <;> simp [atSize, classMembers, same, empty, SamplerReplay.source, Decoder.values, finite_members]
  | shared key inner ih => exact ih size
  | choice lw rw lp rp left right ihl ihr => simp [atSize, classMembers, countChoice_members, ihl, ihr]
  | ap functions arguments ihf iha =>
      simp [atSize, classMembers, countChoice_members, List.flatMap_map, applyRecord, Decoder.values, ihf, iha]
  | sized classes positive bound =>
      by_cases within : size ≤ bound <;> simp [atSize, classMembers, within, empty, SamplerReplay.source, Decoder.values]

/-- A uniform source lists positive unit weights, even if its input list is empty. -/
theorem counting_positive (values : List α) : ∀ entry ∈ counting values, 0 < entry.1 := by
  intro entry present
  obtain ⟨value, _, rfl⟩ := List.mem_map.mp present
  change (0 : Rat) < 1
  decide +kernel

/-- The empty class satisfies the live-record invariant. -/
theorem empty_live : LiveValid (empty : Record α) :=
  source_live [] (by intro entry present; simp at present)

/-- Every exact-size count choice derives positive branch masses from its actual live counts. -/
theorem countChoice_live (records : List (Record α)) (valid : ∀ record ∈ records, LiveValid record) :
    LiveValid (countChoice records) := by
  apply many_live
  · intro entry present
    obtain ⟨record, found, rfl⟩ := List.mem_map.mp present
    exact valid record found
  · intro entry present positive
    obtain ⟨record, _, rfl⟩ := List.mem_map.mp present
    exact Rat.natCast_pos.mpr positive

/-- Whole-language construction derives the complete decoder/sampler invariant for every finite source tree. -/
theorem finite_live (description : Source α) : LiveValid (finite description) := by
  induction description with
  | source outcomes positive => exact source_live outcomes positive
  | pure value => exact source_live [(1, value)] (by
      intro entry present
      have same := List.mem_singleton.mp present
      subst entry
      change (0 : Rat) < 1
      decide +kernel)
  | map transform inner ih => exact map_live transform _ ih
  | pay inner ih | atomic inner ih | shared key inner ih => exact ih
  | choice lw rw lp rp left right ihl ihr =>
      apply many_live
      · intro entry present
        rcases List.mem_cons.mp present with rfl | present
        · exact ihl
        · have same : entry = (rw, finite right) := List.mem_singleton.mp present
          subst entry
          exact ihr
      · intro entry present _
        rcases List.mem_cons.mp present with rfl | present
        · exact lp
        · have same : entry = (rw, finite right) := List.mem_singleton.mp present
          subst entry
          exact rp
  | ap functions arguments ihf iha => exact apply_live _ _ ihf iha
  | sized classes positive bound => exact bounded_live _ _ (fun size => source_live _ (positive size))

/-- Each exact-size record is derived from valid source, atomic, choice, and product operations. -/
theorem class_live (description : Source α) (size : Nat) : LiveValid (atSize description size) := by
  induction description generalizing size with
  | source outcomes positive =>
      simp only [atSize]
      split
      · exact source_live _ (counting_positive _)
      · exact empty_live
  | pure value =>
      simp only [atSize]
      split
      · exact finite_live (.pure value)
      · exact empty_live
  | map transform inner ih => exact map_live _ _ (ih size)
  | pay inner ih => cases size with | zero => exact empty_live | succ size => exact ih size
  | atomic inner ih =>
      simp only [atSize]
      split
      · exact finite_live inner
      · exact empty_live
  | shared key inner ih => exact ih size
  | choice lw rw lp rp left right ihl ihr =>
      apply countChoice_live
      intro record present
      rcases List.mem_cons.mp present with rfl | present
      · exact ihl size
      · have same := List.mem_singleton.mp present
        subst record
        exact ihr size
  | ap functions arguments ihf iha =>
      apply countChoice_live
      intro record present
      obtain ⟨split, _, rfl⟩ := List.mem_map.mp present
      exact apply_live _ _ (ihf split) (iha (size - split))
  | sized classes positive bound =>
      simp only [atSize]
      split
      · exact source_live _ (positive size)
      · exact empty_live

/-- Bounded source replay and probability need no assumed exact-size sampler invariant. -/
theorem bounded_source_live (description : Source α) (bound : Nat) :
    LiveValid (boundedRecord (atSize description) bound) := bounded_live _ _ (class_live description)

/-- Every bounded accepted member has a decoder rank and positive sampling mass, and no others do. -/
theorem bounded_member_exact (description : Source α) (bound : Nat) (value : α) :
    value ∈ (List.range (bound + 1)).flatMap (classMembers description) ↔
      ∃ rank mass, 0 < mass ∧ (mass, (rank, value)) ∈
        (boundedRecord (atSize description) bound).sampling.ranked := by
  have valid := bounded_source_live description bound
  have semantic : Decoder.values (boundedRecord (atSize description) bound).plan =
      (List.range (bound + 1)).flatMap (classMembers description) := by
    simp [boundedRecord, manyRecord, manyPlan_values, List.flatMap_map, class_members]
  constructor
  · intro present
    rw [← semantic, Decoder.mem_values_iff] at present
    obtain ⟨rank, within, decoded⟩ := present
    obtain ⟨mass, found, positive, member, selected⟩ := valid.2.1 rank within
    have same : found = value := Option.some.inj (selected.symm.trans decoded)
    subst found
    exact ⟨rank, mass, positive, member⟩
  · rintro ⟨rank, mass, _, member⟩
    have decoded := valid.1.2 _ member
    rw [← semantic, Decoder.mem_values_iff]
    exact ⟨rank, decoded_bound _ _ _ decoded, decoded⟩

/-- Independent finite distribution semantics use declared branch masses and complete member counts. -/
def distribution : Source α → Distribution α
  | .source outcomes _ => normalize outcomes
  | .pure value => normalize [(1, value)]
  | .map transform inner => Probability.map transform (distribution inner)
  | .pay inner | .atomic inner | .shared _ inner => distribution inner
  | .choice lw rw _ _ left right => weightedChoice
      [(members left |>.length, lw, distribution left), (members right |>.length, rw, distribution right)]
  | .ap functions arguments => Probability.map (fun pair => pair.1 pair.2)
      (product (distribution functions) (distribution arguments))
  | .sized classes _ bound => weightedChoice ((List.range (bound + 1)).map fun size =>
      ((classes size).length, ((classes size).length : Rat), normalize (classes size)))

/-- Independent exact-size probabilities use count weighting and retained atomic distributions. -/
def classDistribution : Source α → Nat → Distribution α
  | .source outcomes _, size => if size = 1 then normalize (counting (outcomes.map Prod.snd)) else []
  | .pure value, size => if size = 0 then normalize [(1, value)] else []
  | .map transform inner, size => Probability.map transform (classDistribution inner size)
  | .pay inner, size => match size with | 0 => [] | next + 1 => classDistribution inner next
  | .atomic inner, size => if size = 1 then distribution inner else []
  | .shared _ inner, size => classDistribution inner size
  | .choice _ _ _ _ left right, size => weightedChoice
      [((classMembers left size).length, ((classMembers left size).length : Rat), classDistribution left size),
       ((classMembers right size).length, ((classMembers right size).length : Rat), classDistribution right size)]
  | .ap functions arguments, size => weightedChoice ((List.range (size + 1)).map fun split =>
      let count := (classMembers functions split).length * (classMembers arguments (size - split)).length
      (count, (count : Rat), Probability.map (fun pair => pair.1 pair.2)
        (product (classDistribution functions split) (classDistribution arguments (size - split)))))
  | .sized classes _ bound, size => if size ≤ bound then normalize (classes size) else []

/-- Whole-language record sampling respects the independent declared distribution. -/
theorem finite_distribution (description : Source α) :
    (finite description).sampling.values = distribution description := by
  induction description with
  | source outcomes positive => rfl
  | pure value => rfl
  | map transform inner ih => simp [finite, distribution, mapRecord, Sampler.mapSampler, ih]
  | pay inner ih | atomic inner ih | shared key inner ih => exact ih
  | choice lw rw lp rp left right ihl ihr =>
      simp [finite, many_values, distribution, Decoder.count_correct, finite_members, ihl, ihr]
  | ap functions arguments ihf iha =>
      simp [finite, applyRecord, Sampler.productSampler, distribution, ihf, iha]
  | sized classes positive bound =>
      simp [finite, boundedRecord, many_values, distribution, SamplerReplay.source, Decoder.count,
        List.map_map, Function.comp_def]

/-- Exact-size record sampling has precisely the source's count and atomic weighting policy. -/
theorem class_distribution (description : Source α) (size : Nat) :
    (atSize description size).sampling.values = classDistribution description size := by
  induction description generalizing size with
  | source outcomes positive =>
      by_cases same : size = 1 <;> simp [atSize, classDistribution, same, empty, SamplerReplay.source, normalize, scale]
  | pure value =>
      by_cases same : size = 0 <;> simp [atSize, classDistribution, same, empty, SamplerReplay.source, normalize, scale]
  | map transform inner ih => simp [atSize, classDistribution, mapRecord, Sampler.mapSampler, ih]
  | pay inner ih => cases size <;> simp [atSize, classDistribution, empty, SamplerReplay.source, normalize, scale, ih]
  | atomic inner ih =>
      by_cases same : size = 1 <;> simp [atSize, classDistribution, same, finite_distribution, empty, SamplerReplay.source, normalize, scale]
  | shared key inner ih => exact ih size
  | choice lw rw lp rp left right ihl ihr =>
      simp [atSize, countChoice, many_values, classDistribution, Decoder.count_correct, class_members, ihl, ihr]
  | ap functions arguments ihf iha =>
      simp [atSize, countChoice, many_values, classDistribution, List.map_map, Function.comp_def,
        applyRecord, Sampler.productSampler, Decoder.count_correct, Decoder.values,
        Decoder.length_applyValues, class_members, ihf, iha]
  | sized classes positive bound =>
      by_cases within : size ≤ bound <;> simp [atSize, classDistribution, within, empty, SamplerReplay.source, normalize, scale]

/-- Bounding uses exact class counts and the independently specified probability within each class. -/
theorem bounded_distribution (description : Source α) (bound : Nat) :
    (boundedRecord (atSize description) bound).sampling.values =
      weightedChoice ((List.range (bound + 1)).map fun size =>
        ((classMembers description size).length, ((classMembers description size).length : Rat),
          classDistribution description size)) := by
  simp [boundedRecord, many_values, List.map_map, Function.comp_def, Decoder.count_correct,
    class_members, class_distribution]

end MicroCFTA.FiniteSource
