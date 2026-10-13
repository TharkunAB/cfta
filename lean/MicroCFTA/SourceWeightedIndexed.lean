import MicroCFTA.SourcePmfQuery

/-!
# Source weighted indexed callbacks

`fromWeightedIndexedOnDemand` checks cardinality and total ticket weight.
It does not evaluate its callbacks. Valid ticket ranks and positive coverage
of every replay rank are caller obligations in the source documentation.
The theorems keep those obligations separate from the metadata checks.
-/
namespace MicroCFTA.SourceWeightedIndexed
open Probability

/-- The exact signed fields of the source WeightedIndexed input. -/
structure Input (Value : Type) where
  cardinality : Int
  totalWeight : Int
  select : Int → Value
  rankAtTicket : Int → Int

/-- Constructor and checked-selection errors retain their source payloads. -/
inductive Error where
  | emptyRanked
  | nonPositiveWeight (weight : Int)
  | insufficientWeight (cardinality weight : Int)
  | negativeRank (rank : Int)
  | selectionOutOfRange (rank cardinality : Int)
  deriving DecidableEq, Repr

/-- The actual constructor validates metadata in source guard order. -/
def compile (input : Input Value) : Except Error (Input Value) :=
  if input.cardinality ≤ 0 then .error .emptyRanked
  else if input.totalWeight ≤ 0 then .error (.nonPositiveWeight input.totalWeight)
  else if input.totalWeight < input.cardinality then
    .error (.insufficientWeight input.cardinality input.totalWeight)
  else .ok input

/-- Metadata success says nothing about either callback. -/
theorem compile_success (input : Input Value) :
    compile input = .ok input ↔
      0 < input.cardinality ∧ 0 < input.totalWeight ∧ input.cardinality ≤ input.totalWeight := by
  unfold compile
  split <;> try {simp_all; omega}
  split <;> try {simp_all; omega}
  split <;> simp_all <;> omega

/-- The public selector checks signed replay ranks before reading its value callback. -/
def unrank (input : Input Value) (rank : Int) : Except Error Value :=
  if rank < 0 then .error (.negativeRank rank)
  else if input.cardinality ≤ rank then .error (.selectionOutOfRange rank input.cardinality)
  else .ok (input.select rank)

/-- Value-only lowering selects a uniform ticket, then reads its callback rank. -/
def values (input : Input Value) : Distribution Value :=
  Probability.map (fun ticket : Nat => input.select (input.rankAtTicket (ticket : Int)))
    (Sampler.uniformRanks input.totalWeight.toNat)

/-- Ranked lowering retains the callback rank rather than the sampling ticket. -/
def ranked (input : Input Value) : Distribution (Int × Value) :=
  Probability.map (fun ticket : Nat =>
    let rank := input.rankAtTicket (ticket : Int)
    (rank, input.select rank)) (Sampler.uniformRanks input.totalWeight.toNat)

/-- Both source lowering fields observe the same sampled values. -/
theorem coherent (input : Input Value) : Probability.map Prod.snd (ranked input) = values input := by
  simp [ranked, values, Probability.map, List.map_map, Function.comp_def]

/-- Every valid sampling ticket must select a valid replay rank. -/
def ValidTickets (input : Input Value) : Prop :=
  ∀ ticket, 0 ≤ ticket → ticket < input.totalWeight →
    0 ≤ input.rankAtTicket ticket ∧ input.rankAtTicket ticket < input.cardinality

/-- Every valid replay rank must have at least one sampling ticket. -/
def Covers (input : Input Value) : Prop :=
  ∀ rank, 0 ≤ rank → rank < input.cardinality →
    ∃ ticket, 0 ≤ ticket ∧ ticket < input.totalWeight ∧ input.rankAtTicket ticket = rank

/-- Count the actual callback tickets of one replay rank. This is its integer weight. -/
def rankWeight (input : Input Value) (rank : Int) : Nat :=
  (List.range input.totalWeight.toNat).countP fun ticket : Nat =>
    decide (input.rankAtTicket (ticket : Int) = rank)

/-- Each replay rank has its callback ticket multiplicity divided by total ticket weight. -/
theorem rank_probability (input : Input Value) (rank : Int) :
    eventMass (fun sampled => decide (sampled.1 = rank)) (ranked input) =
      (rankWeight input rank : Rat) / (input.totalWeight.toNat : Rat) := by
  rw [ranked, eventMass_map]
  simpa [Sampler.uniformRanks, rankWeight, Function.comp_def] using uniform_event_probability
    (fun ticket : Nat => decide (input.rankAtTicket (ticket : Int) = rank))
    (List.range input.totalWeight.toNat)

/-- The documented coverage obligation is exactly positive integer weight at every valid rank. -/
theorem coverage_weights (input : Input Value) :
    Covers input ↔ ∀ rank, 0 ≤ rank → rank < input.cardinality → 0 < rankWeight input rank := by
  constructor
  · intro covers rank nonnegative within
    obtain ⟨ticket, ticketNonnegative, ticketBound, selected⟩ := covers rank nonnegative within
    apply List.countP_pos_iff.mpr
    refine ⟨ticket.toNat, List.mem_range.mpr (by omega), ?_⟩
    simpa only [Int.toNat_of_nonneg ticketNonnegative, decide_eq_true_eq] using selected
  · intro weights rank nonnegative within
    obtain ⟨ticket, member, selected⟩ := List.countP_pos_iff.mp (weights rank nonnegative within)
    exact ⟨(ticket : Int), by omega, by have := List.mem_range.mp member; omega,
      of_decide_eq_true selected⟩

/-- Positive metadata normalizes both lowerings even before callback validity is established. -/
theorem probability (input : Input Value) (compiled : compile input = .ok input) :
    IsProbability (values input) ∧ IsProbability (ranked input) := by
  have weightPositive := (compile_success input).mp compiled |>.2.1
  have uniform : IsProbability (Sampler.uniformRanks input.totalWeight.toNat) :=
    uniform_probability _ (by simp; omega)
  exact ⟨Sampler.map_probability _ _ uniform, Sampler.map_probability _ _ uniform⟩

/-- A valid callback ticket replays the same value through the checked source selector. -/
theorem ticket_replays (input : Input Value) (valid : ValidTickets input)
    (ticket : Int) (nonnegative : 0 ≤ ticket) (within : ticket < input.totalWeight) :
    unrank input (input.rankAtTicket ticket) = .ok (input.select (input.rankAtTicket ticket)) := by
  obtain ⟨rankNonnegative, rankBound⟩ := valid ticket nonnegative within
  simp [unrank, show ¬input.rankAtTicket ticket < 0 by omega,
    show ¬input.cardinality ≤ input.rankAtTicket ticket by omega]

/-- Every actual sampled rank/value pair replays when the callback obeys its valid-ticket contract. -/
theorem sampled_replays (input : Input Value) (valid : ValidTickets input)
    (entry : Rat × Int × Value) (sampled : entry ∈ ranked input) :
    unrank input entry.2.1 = .ok entry.2.2 := by
  obtain ⟨uniform, member, rfl⟩ := List.mem_map.mp sampled
  obtain ⟨counted, countedMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨ticket, ticketMember, rfl⟩ := List.mem_map.mp countedMember
  exact ticket_replays input valid (ticket : Int) (by omega)
    (by have := List.mem_range.mp ticketMember; omega)

/-- Coverage gives strictly positive sampled probability at every valid replay rank. -/
theorem valid_rank_positive (input : Input Value) (compiled : compile input = .ok input)
    (covered : Covers input) (rank : Int) (nonnegative : 0 ≤ rank) (within : rank < input.cardinality) :
    0 < eventMass (fun sampled => decide (sampled.1 = rank)) (ranked input) := by
  rw [rank_probability, Rat.div_def]
  have weightPositive := (compile_success input).mp compiled |>.2.1
  exact Rat.mul_pos (Rat.natCast_pos.mpr ((coverage_weights input).mp covered rank nonnegative within))
    (Rat.inv_pos.mpr (Rat.natCast_pos.mpr (by omega)))

/-- Valid ticket callbacks give no weight to a negative or out-of-range replay rank. -/
theorem invalid_rank_weight_zero (input : Input Value) (valid : ValidTickets input)
    (rank : Int) (outside : rank < 0 ∨ input.cardinality ≤ rank) : rankWeight input rank = 0 := by
  apply List.countP_eq_zero.mpr
  intro ticket member selected
  have ticketBound := List.mem_range.mp member
  obtain ⟨rankNonnegative, rankBound⟩ := valid (ticket : Int) (by omega) (by omega)
  have same := of_decide_eq_true selected
  rw [same] at rankNonnegative rankBound
  omega

/-- Metadata and both callback obligations give exactly the declared positive-probability rank support. -/
theorem rank_support (input : Input Value) (compiled : compile input = .ok input)
    (valid : ValidTickets input) (covered : Covers input) (rank : Int) :
    0 < eventMass (fun sampled => decide (sampled.1 = rank)) (ranked input) ↔
      0 ≤ rank ∧ rank < input.cardinality := by
  constructor
  · intro positive
    by_cases within : 0 ≤ rank ∧ rank < input.cardinality
    · exact within
    · rw [rank_probability, invalid_rank_weight_zero input valid rank (by omega)] at positive
      simp [Rat.div_def, Rat.zero_mul] at positive
  · rintro ⟨nonnegative, within⟩
    exact valid_rank_positive input compiled covered rank nonnegative within

/-- The complete source contract derives normalization, replay, and positive coverage separately. -/
theorem exact_api (input : Input Value) (compiled : compile input = .ok input)
    (valid : ValidTickets input) (covered : Covers input) :
    IsProbability (values input) ∧ IsProbability (ranked input) ∧
      Probability.map Prod.snd (ranked input) = values input ∧
      (∀ entry ∈ ranked input, unrank input entry.2.1 = .ok entry.2.2) ∧
      ∀ rank, 0 < eventMass (fun sampled => decide (sampled.1 = rank)) (ranked input) ↔
        0 ≤ rank ∧ rank < input.cardinality :=
  ⟨(probability input compiled).1, (probability input compiled).2, coherent input,
    sampled_replays input valid, rank_support input compiled valid covered⟩

/-- Duplicate output values collect the probabilities of every callback ticket that decodes to them. -/
theorem output_pmf [DecidableEq Value] [Ord Value] (input : Input Value) (event : Value → Bool) :
    eventMass event ((SourcePmfAggregation.pmf (values input)).map Prod.swap) =
      ((List.range input.totalWeight.toNat).countP fun ticket : Nat =>
        event (input.select (input.rankAtTicket (ticket : Int))) : Rat) /
          (input.totalWeight.toNat : Rat) := by
  rw [SourcePmfAggregation.pmf_distribution, SourcePmfAggregation.event_aggregate, values, eventMass_map]
  simpa [Sampler.uniformRanks, Function.comp_def] using uniform_event_probability
    (fun ticket : Nat => event (input.select (input.rankAtTicket (ticket : Int))))
    (List.range input.totalWeight.toNat)

/-- Metadata checks admit this callback, which violates the documented valid-rank obligation. -/
def outOfRange : Input Int := ⟨2, 2, id, fun _ => 2⟩

/-- Normalized sampling alone does not imply that sampled ranks are valid. -/
theorem metadata_does_not_validate_callback :
    compile outOfRange = .ok outOfRange ∧
    eventMass (fun sampled => decide (sampled.1 = 2)) (ranked outOfRange) = 1 ∧
    unrank outOfRange 2 = .error (.selectionOutOfRange 2 2) := by
  refine ⟨rfl, ?_, rfl⟩
  rw [rank_probability]
  have weight : rankWeight outOfRange 2 = 2 := by decide
  rw [weight]
  change (2 : Rat) / 2 = 1
  rw [Rat.div_def]
  exact Rat.mul_inv_cancel _ (by decide)

/-- A valid-rank callback can still omit one declared replay rank. -/
def missingRank : Input Int := ⟨2, 2, id, fun _ => 0⟩

/-- Coverage is an independent caller obligation, even when every ticket rank is in bounds. -/
theorem metadata_does_not_prove_coverage :
    compile missingRank = .ok missingRank ∧ ValidTickets missingRank ∧
      rankWeight missingRank 1 = 0 ∧ ¬Covers missingRank := by
  refine ⟨by rfl, ?_, by cbv, ?_⟩
  · intro ticket nonnegative within
    change 0 ≤ (0 : Int) ∧ 0 < (2 : Int)
    decide
  · intro covers
    obtain ⟨ticket, _, _, selected⟩ := covers 1 (by decide) (by decide)
    cases selected

end MicroCFTA.SourceWeightedIndexed
