import MicroCFTA.Sampler
import MicroCFTA.PlanVariants

/-!
# Sampler fields and decoder replay

The source keeps an outcome plan, a compiled decoder, and value/rank samplers
in parallel fields. This module connects the independently composed exact
sampler fields to the decoder. Equal values retain distinct replay ranks.
-/

namespace MicroCFTA.SamplerReplay
open Probability Sampler

/-- Every sampled rank decodes to its sampled value. -/
def Replays (decode : Nat → Option α) (ranked : Distribution (Nat × α)) : Prop :=
  ∀ entry ∈ ranked, decode entry.2.1 = some entry.2.2

/-- A finite record contains independently constructed plan and sampler fields. -/
structure Record (α : Type) where
  plan : Decoder.Plan α
  sampling : ExactSampler α

/-- Value-only sampling agrees with ranked sampling, and every sampled rank replays. -/
def Coherent (record : Record α) : Prop :=
  Sampler.Coherent record.sampling ∧ Replays (Decoder.decode record.plan) record.sampling.ranked

/-- Multiplying masses changes no sampled rank or value. -/
theorem replays_scale (decode : Nat → Option α) (factor : Rat) (ranked : Distribution (Nat × α))
    (replays : Replays decode ranked) : Replays decode (scale factor ranked) := by
  intro entry present
  obtain ⟨old, member, rfl⟩ := List.mem_map.mp present
  exact replays old member

/-- Normalization changes no sampled rank or value. -/
theorem replays_normalize (decode : Nat → Option α) (ranked : Distribution (Nat × α))
    (replays : Replays decode ranked) : Replays decode (normalize ranked) :=
  replays_scale decode _ ranked replays

/-- Attach the exact stored replay index to each source occurrence. -/
def rankedSource (outcomes : Distribution α) : Distribution (Nat × α) :=
  outcomes.zipIdx.map fun entry => (entry.1.1, (entry.2, entry.1.2))

/-- Discarding the stored source indices returns the original weighted members. -/
theorem rankedSource_values (outcomes : Distribution α) :
    Probability.map Prod.snd (rankedSource outcomes) = outcomes := by
  change (outcomes.zipIdx.map _).map _ = outcomes
  rw [List.map_map]
  exact List.zipIdx_map_fst 0 outcomes

/-- Indexed source ranks retrieve the exact input occurrence, even for repeated values. -/
theorem rankedSource_replays (outcomes : Distribution α) :
    Replays (fun rank => (outcomes.map Prod.snd)[rank]?) (rankedSource outcomes) := by
  intro entry present
  obtain ⟨original, member, rfl⟩ := List.mem_map.mp present
  have found := List.mem_zipIdx_iff_getElem?.mp member
  simp [List.getElem?_map, found]

/-- A weighted finite source constructs its decoder and exact sampler from the same stored occurrences. -/
def source (outcomes : Distribution α) : Record α :=
  ⟨.source (outcomes.map Prod.snd), ⟨normalize outcomes, normalize (rankedSource outcomes)⟩⟩

/-- Source records satisfy both parallel-field invariants without an injectivity assumption on values. -/
theorem source_coherent (outcomes : Distribution α) : Coherent (source outcomes) := by
  constructor
  · change Probability.map Prod.snd (normalize (rankedSource outcomes)) = normalize outcomes
    rw [map_normalize, rankedSource_values]
  · exact replays_normalize _ _ (rankedSource_replays outcomes)

/-- A mapped record maps both the plan and the sampler. -/
def mapRecord (transform : α → β) (record : Record α) : Record β :=
  ⟨.map transform record.plan, mapSampler transform record.sampling⟩

/-- Mapping preserves exact sampled replay and the value-only sampler field. -/
theorem map_coherent (transform : α → β) (record : Record α) (coherent : Coherent record) :
    Coherent (mapRecord transform record) := by
  refine ⟨mapSampler_coherent transform record.sampling coherent.1, ?_⟩
  intro entry present
  obtain ⟨original, member, rfl⟩ := List.mem_map.mp present
  change (Decoder.decode record.plan original.2.1).map transform = some (transform original.2.2)
  rw [coherent.2 original member]
  rfl

/-- Products use the decoder's actual right cardinality as the sampler radix. -/
def applyRecord (functions : Record (α → β)) (arguments : Record α) : Record β :=
  ⟨.ap functions.plan arguments.plan,
    productSampler (Decoder.count arguments.plan) functions.sampling arguments.sampling⟩

/-- Decoding success proves the same strict rank bound that the sampler's product radix requires. -/
theorem decoded_bound (plan : Decoder.Plan α) (rank : Nat) (value : α)
    (decoded : Decoder.decode plan rank = some value) : rank < Decoder.count plan := by
  by_cases bound : rank < Decoder.count plan
  · exact bound
  · have impossible := (Decoder.decode_none_iff plan rank).mpr (by omega)
    simp [decoded] at impossible

/-- Independent product sampling replays through the actual mixed-radix decoder. -/
theorem apply_coherent (functions : Record (α → β)) (arguments : Record α)
    (functionsCoherent : Coherent functions) (argumentsCoherent : Coherent arguments) :
    Coherent (applyRecord functions arguments) := by
  refine ⟨productSampler_coherent _ _ _ functionsCoherent.1 argumentsCoherent.1, ?_⟩
  intro entry present
  obtain ⟨pair, member, rfl⟩ := List.mem_map.mp present
  obtain ⟨left, leftMember, right, rightMember, same⟩ :=
    (by simpa [Probability.product] using member :
      ∃ left, left ∈ functions.sampling.ranked ∧ ∃ right, right ∈ arguments.sampling.ranked ∧
        (left.1 * right.1, (left.2, right.2)) = pair)
  subst pair
  have leftFound := functionsCoherent.2 left leftMember
  have rightFound := argumentsCoherent.2 right rightMember
  have leftBound := decoded_bound _ _ _ leftFound
  have rightBound := decoded_bound _ _ _ rightFound
  have bound := Probability.pairRank_lt leftBound rightBound
  change Decoder.decode (.ap functions.plan arguments.plan)
    (pairRank (Decoder.count arguments.plan) left.2.1 right.2.1) = _
  rw [Decoder.decode, ite_eq_left bound]
  have split := Probability.split_pair (left := left.2.1) rightBound
  have first := congrArg Prod.fst split
  have second := congrArg Prod.snd split
  simp only [Probability.splitRank] at first second
  rw [first, second, leftFound, rightFound]
  rfl

/-- A mixture can only sample members of one of its branches. -/
theorem replays_mix (decode : Nat → Option α) (branches : List (Rat × Distribution (Nat × α)))
    (replays : ∀ branch ∈ branches, Replays decode branch.2) : Replays decode (mix branches) := by
  induction branches with
  | nil => intro entry present; simp [mix] at present
  | cons branch rest ih =>
      intro entry present
      rcases List.mem_append.mp present with first | later
      · exact replays_scale decode branch.1 branch.2 (replays branch (by simp)) entry first
      · exact ih (fun b h => replays b (by simp [h])) entry later

/-- Branch-weight normalization preserves every branch's decoder relation. -/
theorem replays_frequency (decode : Nat → Option α) (branches : List (Rat × Distribution (Nat × α)))
    (replays : ∀ branch ∈ branches, Replays decode branch.2) : Replays decode (frequency branches) :=
  replays_scale decode _ _ (replays_mix decode branches replays)

/-- A binary choice uses the same structural offset in its plan and sampled ranks. -/
def choiceRecord (leftWeight rightWeight : Rat) (left right : Record α) : Record α :=
  ⟨.choice left.plan right.plan,
    chooseSampler [⟨leftWeight, 0, left.sampling⟩, ⟨rightWeight, Decoder.count left.plan, right.sampling⟩]⟩

/-- Choice offsets preserve replay and agreement of both sampler fields. -/
theorem choice_coherent (leftWeight rightWeight : Rat) (left right : Record α)
    (leftCoherent : Coherent left) (rightCoherent : Coherent right) :
    Coherent (choiceRecord leftWeight rightWeight left right) := by
  constructor
  · apply chooseSampler_coherent
    intro part present
    rcases List.mem_cons.mp present with rfl | present
    · exact leftCoherent.1
    · have same : part = ⟨rightWeight, Decoder.count left.plan, right.sampling⟩ := by simpa using present
      subst part
      exact rightCoherent.1
  · apply replays_frequency
    intro branch present
    obtain ⟨part, member, rfl⟩ := List.mem_map.mp present
    rcases List.mem_cons.mp member with rfl | member
    · intro entry present
      obtain ⟨original, belongs, rfl⟩ := List.mem_map.mp present
      have decoded := leftCoherent.2 original belongs
      have bound := decoded_bound _ _ _ decoded
      simpa [choiceRecord, Decoder.decode, bound] using decoded
    · have same : part = ⟨rightWeight, Decoder.count left.plan, right.sampling⟩ := by simpa using member
      subst part
      intro entry present
      obtain ⟨original, belongs, rfl⟩ := List.mem_map.mp present
      have decoded := rightCoherent.2 original belongs
      have outside : ¬ Decoder.count left.plan + original.2.1 < Decoder.count left.plan := by omega
      simp [choiceRecord, Decoder.decode, decoded, outside]

/-- Each valid decoder rank has a positive-probability sampled occurrence. -/
def Covers (record : Record α) : Prop :=
  ∀ rank, rank < Decoder.count record.plan → ∃ mass value,
    0 < mass ∧ (mass, (rank, value)) ∈ record.sampling.ranked ∧ Decoder.decode record.plan rank = some value

/-- Positive nonempty source weights normalize to positive sampled mass at every rank. -/
theorem source_covers (outcomes : Distribution α) (nonempty : outcomes ≠ [])
    (positive : ∀ entry ∈ outcomes, 0 < entry.1) : Covers (source outcomes) := by
  intro rank bound
  have valid : rank < outcomes.length := by simpa [source, Decoder.count] using bound
  let entry := outcomes[rank]
  have selected : outcomes[rank]? = some entry := List.getElem?_eq_getElem valid
  have belongs : (entry, rank) ∈ outcomes.zipIdx := List.mk_mem_zipIdx_iff_getElem?.mpr selected
  have sourceMember : (entry.1, (rank, entry.2)) ∈ rankedSource outcomes := List.mem_map.mpr ⟨(entry, rank), belongs, rfl⟩
  have totalEq : total (rankedSource outcomes) = total outcomes := by
    rw [← total_map Prod.snd, rankedSource_values]
  have totalPositive := Sized.total_positive outcomes nonempty positive
  refine ⟨(total outcomes)⁻¹ * entry.1, entry.2,
    Rat.mul_pos (Rat.inv_pos.mpr totalPositive) (positive entry (List.getElem_mem valid)), ?_, ?_⟩
  · change _ ∈ scale (total (rankedSource outcomes))⁻¹ (rankedSource outcomes)
    rw [totalEq]
    exact List.mem_map.mpr ⟨(entry.1, (rank, entry.2)), sourceMember, rfl⟩
  · simp [source, Decoder.decode, List.getElem?_map, selected]

/-- A mapped value can merge observations without removing any positive replay position. -/
theorem map_covers (transform : α → β) (record : Record α) (covers : Covers record) :
    Covers (mapRecord transform record) := by
  intro rank bound
  obtain ⟨mass, value, positive, member, decoded⟩ := covers rank bound
  refine ⟨mass, transform value, positive, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨(mass, (rank, value)), member, rfl⟩
  · change (Decoder.decode record.plan rank).map transform = some (transform value)
    rw [decoded]
    rfl

/-- Every product rank is sampled with positive mass and replays to its independent component values. -/
theorem apply_covers (functions : Record (α → β)) (arguments : Record α)
    (functionsCover : Covers functions) (argumentsCover : Covers arguments) :
    Covers (applyRecord functions arguments) := by
  intro rank bound
  have within : rank < Decoder.count functions.plan * Decoder.count arguments.plan := bound
  have split := Probability.split_lt within
  obtain ⟨leftMass, function, leftPositive, leftMember, leftDecoded⟩ := functionsCover _ split.1
  obtain ⟨rightMass, value, rightPositive, rightMember, rightDecoded⟩ := argumentsCover _ split.2
  refine ⟨leftMass * rightMass, function value, Rat.mul_pos leftPositive rightPositive, ?_, ?_⟩
  · apply List.mem_map.mpr
    refine ⟨(leftMass * rightMass, ((rank / Decoder.count arguments.plan, function),
      (rank % Decoder.count arguments.plan, value))), ?_, ?_⟩
    · exact List.mem_flatMap.mpr ⟨(leftMass, (rank / Decoder.count arguments.plan, function)), leftMember,
        List.mem_map.mpr ⟨(rightMass, (rank % Decoder.count arguments.plan, value)), rightMember, rfl⟩⟩
    · have combined := Probability.pair_split (Decoder.count arguments.plan) rank
      simpa [Probability.splitRank] using congrArg (fun r => (leftMass * rightMass, (r, function value))) combined
  · change Decoder.decode (.ap functions.plan arguments.plan) rank = some (function value)
    simp [Decoder.decode, within, leftDecoded, rightDecoded, Probability.splitRank] at *

/-- A mixture retains every member of every branch with its multiplied mass. -/
theorem mix_member (branches : List (Rat × Distribution α)) (branch : Rat × Distribution α)
    (found : branch ∈ branches) (entry : Rat × α) (present : entry ∈ branch.2) :
    (branch.1 * entry.1, entry.2) ∈ mix branches := by
  induction branches with
  | nil => simp at found
  | cons first rest ih =>
      rcases List.mem_cons.mp found with rfl | later
      · exact List.mem_append_left _ (List.mem_map.mpr ⟨entry, present, rfl⟩)
      · exact List.mem_append_right _ (ih later)

/-- Frequency retains that member with the source branch normalization factor. -/
theorem frequency_member (branches : List (Rat × Distribution α)) (branch : Rat × Distribution α)
    (found : branch ∈ branches) (entry : Rat × α) (present : entry ∈ branch.2) :
    ((branchWeight branches)⁻¹ * (branch.1 * entry.1), entry.2) ∈ frequency branches :=
  List.mem_map.mpr ⟨(branch.1 * entry.1, entry.2), mix_member branches branch found entry present, rfl⟩

/-- Positive branch choices retain positive sampled mass at every structural rank. -/
theorem choice_covers (leftWeight rightWeight : Rat) (left right : Record α)
    (leftPositive : 0 < leftWeight) (rightPositive : 0 < rightWeight)
    (leftCover : Covers left) (rightCover : Covers right) :
    Covers (choiceRecord leftWeight rightWeight left right) := by
  intro rank bound
  let branches := [(leftWeight, Probability.map (fun entry : Nat × α => (0 + entry.1, entry.2)) left.sampling.ranked),
    (rightWeight, Probability.map (fun entry : Nat × α => (Decoder.count left.plan + entry.1, entry.2)) right.sampling.ranked)]
  have totalPositive : 0 < branchWeight branches := by
    have more : leftWeight < leftWeight + rightWeight := by
      simpa [Rat.add_zero] using (Rat.add_lt_add_left (c := leftWeight)).mpr rightPositive
    simp only [branches, branchWeight, Rat.add_zero]
    grind
  by_cases first : rank < Decoder.count left.plan
  · obtain ⟨mass, value, positive, member, decoded⟩ := leftCover rank first
    refine ⟨(branchWeight branches)⁻¹ * (leftWeight * mass), value,
      Rat.mul_pos (Rat.inv_pos.mpr totalPositive) (Rat.mul_pos leftPositive positive), ?_, ?_⟩
    · change _ ∈ frequency branches
      apply frequency_member branches (leftWeight, Probability.map (fun entry : Nat × α => (0 + entry.1, entry.2)) left.sampling.ranked)
        (by simp [branches]) (mass, (rank, value))
      exact List.mem_map.mpr ⟨(mass, (rank, value)), member, by simp⟩
    · simpa [choiceRecord, Decoder.decode, first] using decoded
  · have rightBound : rank - Decoder.count left.plan < Decoder.count right.plan := by
      change rank < Decoder.count left.plan + Decoder.count right.plan at bound
      omega
    obtain ⟨mass, value, positive, member, decoded⟩ := rightCover _ rightBound
    refine ⟨(branchWeight branches)⁻¹ * (rightWeight * mass), value,
      Rat.mul_pos (Rat.inv_pos.mpr totalPositive) (Rat.mul_pos rightPositive positive), ?_, ?_⟩
    · change _ ∈ frequency branches
      apply frequency_member branches (rightWeight, Probability.map (fun entry : Nat × α => (Decoder.count left.plan + entry.1, entry.2)) right.sampling.ranked)
        (by simp [branches]) (mass, (rank, value))
      exact List.mem_map.mpr ⟨(mass, (rank - Decoder.count left.plan, value)), member, by simp [Nat.add_sub_of_le (by omega : Decoder.count left.plan ≤ rank)]⟩
    · simpa [choiceRecord, Decoder.decode, first] using decoded

/-- Positive nonempty finite sources give probability distributions in both sampler fields. -/
theorem source_probability (outcomes : Distribution α) (nonempty : outcomes ≠ [])
    (positive : ∀ entry ∈ outcomes, 0 < entry.1) :
    IsProbability (source outcomes).sampling.values ∧ IsProbability (source outcomes).sampling.ranked := by
  have totalPositive := Sized.total_positive outcomes nonempty positive
  constructor
  · exact normalize_probability outcomes (fun entry member => Rat.le_of_lt (positive entry member)) totalPositive
  · apply normalize_probability
    · intro entry present
      obtain ⟨original, member, rfl⟩ := List.mem_map.mp present
      exact Rat.le_of_lt (positive original.1 (List.fst_mem_of_mem_zipIdx member))
    · rw [← total_map Prod.snd, rankedSource_values]
      exact totalPositive

/-- A complete finite record connects normalized sampling, exact replay, and positive coverage. -/
def Valid (record : Record α) : Prop :=
  Coherent record ∧ IsProbability record.sampling.values ∧ IsProbability record.sampling.ranked ∧ Covers record

/-- Source construction derives the full finite record invariant from accepted positive weights. -/
theorem source_valid (outcomes : Distribution α) (nonempty : outcomes ≠ [])
    (positive : ∀ entry ∈ outcomes, 0 < entry.1) : Valid (source outcomes) :=
  ⟨source_coherent outcomes, (source_probability outcomes nonempty positive).1,
    (source_probability outcomes nonempty positive).2, source_covers outcomes nonempty positive⟩

/-- Mapping any value function preserves the complete finite record invariant. -/
theorem map_valid (transform : α → β) (record : Record α) (valid : Valid record) :
    Valid (mapRecord transform record) :=
  ⟨map_coherent transform record valid.1,
    map_probability transform record.sampling.values valid.2.1,
    map_probability (fun entry : Nat × α => (entry.1, transform entry.2)) record.sampling.ranked valid.2.2.1,
    map_covers transform record valid.2.2.2⟩

/-- Product construction preserves normalized mass, positive coverage, and decoder replay together. -/
theorem apply_valid (functions : Record (α → β)) (arguments : Record α)
    (functionsValid : Valid functions) (argumentsValid : Valid arguments) :
    Valid (applyRecord functions arguments) :=
  ⟨apply_coherent functions arguments functionsValid.1 argumentsValid.1,
    (productSampler_probability _ _ _ ⟨functionsValid.2.1, functionsValid.2.2.1⟩
      ⟨argumentsValid.2.1, argumentsValid.2.2.1⟩).1,
    (productSampler_probability _ _ _ ⟨functionsValid.2.1, functionsValid.2.2.1⟩
      ⟨argumentsValid.2.1, argumentsValid.2.2.1⟩).2,
    apply_covers functions arguments functionsValid.2.2.2 argumentsValid.2.2.2⟩

/-- Positive finite choices preserve the complete record invariant. -/
theorem choice_valid (leftWeight rightWeight : Rat) (left right : Record α)
    (leftPositive : 0 < leftWeight) (rightPositive : 0 < rightWeight)
    (leftValid : Valid left) (rightValid : Valid right) :
    Valid (choiceRecord leftWeight rightWeight left right) := by
  have probability := chooseSampler_probability
    [⟨leftWeight, 0, left.sampling⟩, ⟨rightWeight, Decoder.count left.plan, right.sampling⟩]
    (by simp)
    (by
      intro part present
      rcases List.mem_cons.mp present with rfl | present
      · exact leftPositive
      · have same : part = ⟨rightWeight, Decoder.count left.plan, right.sampling⟩ := by simpa using present
        subst part
        exact rightPositive)
    (by
      intro part present
      rcases List.mem_cons.mp present with rfl | present
      · exact ⟨leftValid.2.1, leftValid.2.2.1⟩
      · have same : part = ⟨rightWeight, Decoder.count left.plan, right.sampling⟩ := by simpa using present
        subst part
        exact ⟨rightValid.2.1, rightValid.2.2.1⟩)
  exact ⟨choice_coherent _ _ _ _ leftValid.1 rightValid.1, probability.1, probability.2,
    choice_covers _ _ _ _ leftPositive rightPositive leftValid.2.2.2 rightValid.2.2.2⟩

/-- Positive sampled occurrences are exactly the decoder's successful rank/value pairs. -/
theorem sampled_iff_decoded (record : Record α) (valid : Valid record) (rank : Nat) (value : α) :
    (∃ mass, 0 < mass ∧ (mass, (rank, value)) ∈ record.sampling.ranked) ↔
      Decoder.decode record.plan rank = some value := by
  constructor
  · rintro ⟨mass, _, member⟩
    exact valid.1.2 _ member
  · intro decoded
    obtain ⟨mass, found, positive, member, selected⟩ := valid.2.2.2 rank (decoded_bound _ _ _ decoded)
    have same : found = value := Option.some.inj (selected.symm.trans decoded)
    subst found
    exact ⟨mass, positive, member⟩

/-- The source's ordered choice plan retains even empty alternatives in its structural offsets. -/
def manyPlan : List (Rat × Record α) → Decoder.Plan α
  | [] => .source []
  | first :: rest => .choice first.2.plan (manyPlan rest)

/-- Supply the count and sampler fields that the source choice worker reads. -/
def alternatives (records : List (Rat × Record α)) : List (Alternative α) :=
  records.map fun entry => ⟨Decoder.count entry.2.plan, entry.1, entry.2.sampling⟩

/-- A retained sampler part decodes under the exact accumulated structural offset. -/
theorem choiceParts_replay (records : List (Rat × Record α)) (offset : Nat)
    (coherent : ∀ entry ∈ records, Coherent entry.2) (part : ChoicePart α)
    (present : part ∈ choiceParts offset (alternatives records)) (entry : Rat × Nat × α)
    (sampled : entry ∈ part.sampling.ranked) :
    Decoder.decode (manyPlan records) (part.offset + entry.2.1 - offset) = some entry.2.2 := by
  induction records generalizing offset with
  | nil => simp [alternatives, choiceParts] at present
  | cons first rest ih =>
      have later (member : part ∈ choiceParts (offset + Decoder.count first.2.plan) (alternatives rest)) :
          Decoder.decode (manyPlan (first :: rest)) (part.offset + entry.2.1 - offset) = some entry.2.2 := by
        have selected := ih (offset + Decoder.count first.2.plan)
          (fun other found => coherent other (by simp [found])) member
        have origin := choiceParts_origin (alternatives rest) (offset + Decoder.count first.2.plan) part member
        obtain ⟨_, _, _, _, _, _, lower, _⟩ := origin
        have branch : ¬ part.offset + entry.2.1 - offset < Decoder.count first.2.plan := by omega
        have rankEq : part.offset + entry.2.1 - offset - Decoder.count first.2.plan =
            part.offset + entry.2.1 - (offset + Decoder.count first.2.plan) := by omega
        simpa [manyPlan, Decoder.decode, branch, rankEq] using selected
      simp only [alternatives, List.map_cons, choiceParts] at present
      split at present
      · rcases List.mem_cons.mp present with same | remaining
        · subst part
          have selected := (coherent first (by simp)).2 entry sampled
          have bound := decoded_bound _ _ _ selected
          simpa [manyPlan, Decoder.decode, bound] using selected
        · exact later remaining
      · exact later present

/-- The source's n-way choice composes the structural plan and independent sampler fields. -/
def manyRecord (records : List (Rat × Record α)) : Record α :=
  ⟨manyPlan records, chooseSampler (choiceParts 0 (alternatives records))⟩

/-- The actual n-way offset worker preserves replay, including omitted empty alternatives. -/
theorem many_coherent (records : List (Rat × Record α))
    (coherent : ∀ entry ∈ records, Coherent entry.2) : Coherent (manyRecord records) := by
  constructor
  · apply choiceParts_coherent
    intro alternative present
    obtain ⟨entry, member, rfl⟩ := List.mem_map.mp present
    exact (coherent entry member).1
  · apply replays_frequency
    intro branch member
    obtain ⟨part, present, rfl⟩ := List.mem_map.mp member
    intro entry sampled
    obtain ⟨original, found, rfl⟩ := List.mem_map.mp sampled
    simpa [manyRecord] using choiceParts_replay records 0 coherent part present original found

/-- Bound an exact-size family in ascending size order, using derived class counts. -/
def boundedRecord (classes : Nat → Record α) (bound : Nat) : Record α :=
  manyRecord ((List.range (bound + 1)).map fun size => ((Decoder.count (classes size).plan : Rat), classes size))

/-- The bounded record uses the source's actual `boundedSampler` class weighting and offsets. -/
theorem bounded_sampler (classes : Nat → Record α) (bound : Nat) :
    (boundedRecord classes bound).sampling =
      boundedSampler ((List.range (bound + 1)).map fun size => (size, Decoder.count (classes size).plan))
        (fun size => (classes size).sampling) := by
  simp [boundedRecord, manyRecord, alternatives, boundedSampler, List.map_map, Function.comp_def]

/-- A bounded recursive family samples the same value that its size-major replay decoder returns. -/
theorem bounded_coherent (classes : Nat → Record α) (bound : Nat)
    (coherent : ∀ size, Coherent (classes size)) : Coherent (boundedRecord classes bound) := by
  apply many_coherent
  intro entry present
  obtain ⟨size, _, rfl⟩ := List.mem_map.mp present
  exact coherent size

/-- The n-way structural plan lists each member exactly once in branch order. -/
theorem manyPlan_values (records : List (Rat × Record α)) :
    Decoder.values (manyPlan records) = records.flatMap (fun entry => Decoder.values entry.2.plan) := by
  induction records with
  | nil => rfl
  | cons first rest ih => simp [manyPlan, Decoder.values, ih]

/-- The bounded decoder is the existing sized-plan decoder with the exact same class order. -/
theorem bounded_decode (classes : Nat → Record α) (bound rank : Nat) :
    Decoder.decode (boundedRecord classes bound).plan rank =
      Decoder.decode (PlanVariants.erase (.sized (fun size => Decoder.values (classes size).plan) bound)) rank := by
  rw [Decoder.decode_correct, Decoder.decode_correct]
  simp [boundedRecord, manyRecord, manyPlan_values, PlanVariants.erase, Decoder.values, List.flatMap_map]

/-- The count of a bounded record is the exact sum of its class counts. -/
theorem bounded_count (classes : Nat → Record α) (bound : Nat) :
    Decoder.count (boundedRecord classes bound).plan =
      ((List.range (bound + 1)).map fun size => Decoder.count (classes size).plan).sum := by
  rw [Decoder.count_correct]
  simp [boundedRecord, manyRecord, manyPlan_values, List.flatMap_map, List.length_flatMap,
    Decoder.count_correct]

/-- Every structural rank belongs to a retained live choice part with positive sampled member mass. -/
theorem choiceParts_cover (records : List (Rat × Record α))
    (covers : ∀ entry ∈ records, Covers entry.2)
    (positive : ∀ entry ∈ records, 0 < Decoder.count entry.2.plan → 0 < entry.1)
    (offset rank : Nat) (bound : rank < Decoder.count (manyPlan records)) :
    ∃ part, part ∈ choiceParts offset (alternatives records) ∧ ∃ entry,
      entry ∈ part.sampling.ranked ∧ 0 < entry.1 ∧ part.offset + entry.2.1 = offset + rank := by
  induction records generalizing offset rank with
  | nil => simp [manyPlan, Decoder.count] at bound
  | cons first rest ih =>
      by_cases inside : rank < Decoder.count first.2.plan
      · obtain ⟨mass, value, massPositive, member, _⟩ := covers first (by simp) rank inside
        have countPositive : 0 < Decoder.count first.2.plan := by omega
        have weightPositive := positive first (by simp) countPositive
        refine ⟨⟨first.1, offset, first.2.sampling⟩, ?_, (mass, (rank, value)), member, massPositive, rfl⟩
        simp [alternatives, choiceParts, countPositive, weightPositive]
      · have remaining : rank - Decoder.count first.2.plan < Decoder.count (manyPlan rest) := by
          change rank < Decoder.count first.2.plan + Decoder.count (manyPlan rest) at bound
          omega
        obtain ⟨part, present, entry, member, massPositive, located⟩ := ih
          (fun other found => covers other (by simp [found]))
          (fun other found => positive other (by simp [found]))
          (offset + Decoder.count first.2.plan) (rank - Decoder.count first.2.plan) remaining
        refine ⟨part, ?_, entry, member, massPositive, by omega⟩
        simp only [alternatives, List.map_cons, choiceParts]
        split
        · exact List.mem_cons_of_mem _ present
        · exact present

/-- Live n-way choices retain all structural ranks with positive sampling mass. -/
theorem many_covers (records : List (Rat × Record α))
    (coherent : ∀ entry ∈ records, Coherent entry.2)
    (covers : ∀ entry ∈ records, Covers entry.2)
    (positive : ∀ entry ∈ records, 0 < Decoder.count entry.2.plan → 0 < entry.1) :
    Covers (manyRecord records) := by
  intro rank bound
  obtain ⟨part, present, entry, member, massPositive, located⟩ :=
    choiceParts_cover records covers positive 0 rank bound
  let parts := choiceParts 0 (alternatives records)
  let branches := parts.map fun p => (p.mass, Probability.map (fun entry : Nat × α => (p.offset + entry.1, entry.2)) p.sampling.ranked)
  have partPositive : 0 < part.mass := (choiceParts_origin _ 0 part present).choose_spec.2.2.2.2.1
  have totalPositive : 0 < branchWeight branches := by
    apply positive_branchWeight
    · have listed : (part.mass, Probability.map (fun entry : Nat × α => (part.offset + entry.1, entry.2)) part.sampling.ranked) ∈ branches :=
        List.mem_map.mpr ⟨part, present, rfl⟩
      exact List.ne_nil_of_mem listed
    · intro branch found
      obtain ⟨p, partMember, rfl⟩ := List.mem_map.mp found
      exact (choiceParts_origin _ 0 p partMember).choose_spec.2.2.2.2.1
  let resultMass := (branchWeight branches)⁻¹ * (part.mass * entry.1)
  have retained : (resultMass, (rank, entry.2.2)) ∈ (manyRecord records).sampling.ranked := by
    apply frequency_member branches
      (part.mass, Probability.map (fun entry : Nat × α => (part.offset + entry.1, entry.2)) part.sampling.ranked)
      (List.mem_map.mpr ⟨part, present, rfl⟩) (entry.1, (rank, entry.2.2))
    exact List.mem_map.mpr ⟨entry, member, by simp [located]⟩
  exact ⟨resultMass, entry.2.2, Rat.mul_pos (Rat.inv_pos.mpr totalPositive) (Rat.mul_pos partPositive massPositive),
    retained, (many_coherent records coherent).2 _ retained⟩

/-- Bounding a family preserves positive sampling coverage of every size-major rank. -/
theorem bounded_covers (classes : Nat → Record α) (bound : Nat)
    (coherent : ∀ size, Coherent (classes size)) (covers : ∀ size, Covers (classes size)) :
    Covers (boundedRecord classes bound) := by
  apply many_covers
  · intro entry present
    obtain ⟨size, _, rfl⟩ := List.mem_map.mp present
    exact coherent size
  · intro entry present
    obtain ⟨size, _, rfl⟩ := List.mem_map.mp present
    exact covers size
  · intro entry present nonempty
    obtain ⟨size, _, rfl⟩ := List.mem_map.mp present
    exact Rat.natCast_pos.mpr nonempty

/-- Empty classes are valid empty indices; live classes also carry normalized sampler fields. -/
def LiveValid (record : Record α) : Prop :=
  Coherent record ∧ Covers record ∧ (0 < Decoder.count record.plan →
    IsProbability record.sampling.values ∧ IsProbability record.sampling.ranked)

/-- Positive source weights give a valid record even when the source class is empty. -/
theorem source_live (outcomes : Distribution α) (positive : ∀ entry ∈ outcomes, 0 < entry.1) :
    LiveValid (source outcomes) := by
  refine ⟨source_coherent outcomes, ?_, ?_⟩
  · by_cases empty : outcomes = []
    · subst outcomes
      intro rank bound
      simp [source, Decoder.count] at bound
    · exact source_covers outcomes empty positive
  · intro countPositive
    have nonempty : outcomes ≠ [] := by
      intro empty
      simp [empty, source, Decoder.count] at countPositive
    exact source_probability outcomes nonempty positive

/-- Mapping preserves live and empty class invariants. -/
theorem map_live (transform : α → β) (record : Record α) (valid : LiveValid record) :
    LiveValid (mapRecord transform record) := by
  refine ⟨map_coherent transform record valid.1, map_covers transform record valid.2.1, ?_⟩
  intro positive
  have probability := valid.2.2 positive
  exact ⟨map_probability transform _ probability.1,
    map_probability (fun entry : Nat × α => (entry.1, transform entry.2)) _ probability.2⟩

/-- An applicative live size split satisfies every finite record invariant. -/
theorem apply_live (functions : Record (α → β)) (arguments : Record α)
    (functionsValid : LiveValid functions) (argumentsValid : LiveValid arguments) :
    LiveValid (applyRecord functions arguments) := by
  refine ⟨apply_coherent functions arguments functionsValid.1 argumentsValid.1,
    apply_covers functions arguments functionsValid.2.1 argumentsValid.2.1, ?_⟩
  intro positive
  change 0 < Decoder.count functions.plan * Decoder.count arguments.plan at positive
  have leftPositive : 0 < Decoder.count functions.plan := Nat.pos_of_mul_pos_right positive
  have rightPositive : 0 < Decoder.count arguments.plan := Nat.pos_of_mul_pos_left positive
  exact productSampler_probability _ _ _ (functionsValid.2.2 leftPositive) (argumentsValid.2.2 rightPositive)

/-- N-way choice derives live probability from its actual retained alternatives. -/
theorem many_live (records : List (Rat × Record α))
    (valid : ∀ entry ∈ records, LiveValid entry.2)
    (positive : ∀ entry ∈ records, 0 < Decoder.count entry.2.plan → 0 < entry.1) :
    LiveValid (manyRecord records) := by
  refine ⟨many_coherent records (fun entry member => (valid entry member).1),
    many_covers records (fun entry member => (valid entry member).1)
      (fun entry member => (valid entry member).2.1) positive, ?_⟩
  intro nonempty
  obtain ⟨part, member, _⟩ := choiceParts_cover records (fun entry member => (valid entry member).2.1)
    positive 0 0 nonempty
  apply chooseSampler_probability
  · exact List.ne_nil_of_mem member
  · intro chosen present
    exact (choiceParts_origin _ 0 chosen present).choose_spec.2.2.2.2.1
  · intro chosen present
    obtain ⟨alternative, origin, _, samplingEq, live, _⟩ := choiceParts_origin _ 0 chosen present
    obtain ⟨entry, found, rfl⟩ := List.mem_map.mp origin
    rw [samplingEq]
    exact (valid entry found).2.2 live

/-- Bounded recursive sampling is a valid finite record once each exact-size record is valid. -/
theorem bounded_live (classes : Nat → Record α) (bound : Nat)
    (valid : ∀ size, LiveValid (classes size)) : LiveValid (boundedRecord classes bound) := by
  apply many_live
  · intro entry present
    obtain ⟨size, _, rfl⟩ := List.mem_map.mp present
    exact valid size
  · intro entry present nonempty
    obtain ⟨size, _, rfl⟩ := List.mem_map.mp present
    exact Rat.natCast_pos.mpr nonempty

/-- Exact weighted choice removes empty branches before normalizing their declared masses. -/
def weightedChoice (branches : List (Nat × Rat × Distribution α)) : Distribution α :=
  frequency (branches.filterMap fun (count, mass, outcomes) =>
    if 0 < count ∧ 0 < mass then some (mass, outcomes) else none)

/-- The source offset worker does not change live branch probabilities. -/
theorem choiceParts_values (alternatives : List (Sampler.Alternative α)) (offset : Nat) :
    (choiceParts offset alternatives).map (fun part => (part.mass, part.sampling.values)) =
      alternatives.filterMap (fun alternative =>
        if 0 < alternative.count ∧ 0 < alternative.mass then some (alternative.mass, alternative.sampling.values) else none) := by
  induction alternatives generalizing offset with
  | nil => rfl
  | cons first rest ih =>
      simp only [choiceParts, List.filterMap_cons]
      split <;> simp_all

/-- An independently built n-way sampler has exactly the declared live-branch distribution. -/
theorem many_values (records : List (Rat × Record α)) :
    (manyRecord records).sampling.values = weightedChoice (records.map fun entry =>
      (Decoder.count entry.2.plan, entry.1, entry.2.sampling.values)) := by
  simp [manyRecord, chooseSampler, choiceParts_values, alternatives, weightedChoice, List.filterMap_map, Function.comp_def]

end MicroCFTA.SamplerReplay
