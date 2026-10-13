import MicroCFTA.SourceQuickCheckFrequency
import MicroCFTA.SamplerReplay

/-!
# Ticket probabilities for the actual QuickCheck search

Only the external bounded ticket draw is assumed uniform. The cumulative
array and binary selection derive the branch distribution. Equal output
values retain every input occurrence and aggregate their event masses.
-/
namespace MicroCFTA.SourceQuickCheckFrequency
open Probability Sampler

/-- Draw one uniform ticket and execute the source array search. -/
def sampling (weighted : List (Nat × α)) : Distribution (Option α) :=
  Probability.map (select weighted) (uniformRanks (ticketCount weighted))

/-- The complete selected-branch distribution is the ordered ticket expansion. -/
theorem sampling_correct (weighted : List (Nat × α)) :
    sampling weighted = Probability.map some (normalize (counting (tickets weighted))) := by
  rw [sampling, uniformRanks, map_normalize, map_counting, map_normalize, map_counting]
  congr 2
  calc
    (List.range (ticketCount weighted)).map (select weighted) =
        (List.range (ticketCount weighted)).map (fun ticket => (tickets weighted)[ticket]?) := by
      apply List.map_congr_left
      intro ticket present
      exact select_correct weighted ticket (List.mem_range.mp present)
    _ = (tickets weighted).map some := by rw [←tickets_length]; exact map_range_get _

/-- Each branch event has its input weight sum divided by the total ticket count. -/
theorem sampling_event (weighted : List (Nat × α)) (event : α → Bool) :
    eventMass (fun selected => selected.any event) (sampling weighted) =
      (eventWeight event weighted : Rat) / ticketCount weighted := by
  rw [sampling_correct, eventMass_map]
  exact uniform_tickets_probability event weighted

/-- The source selects the machine or arbitrary-precision draw from the total. -/
def ticketDraw (maximum : Nat) (intDraw integerDraw : Nat → Distribution Nat) (bound : Nat) : Distribution Nat :=
  if bound ≤ maximum then intDraw bound else integerDraw bound

/-- Both source ticket paths have the same law when their external draw is uniform. -/
theorem ticketDraw_uniform (maximum : Nat) (intDraw integerDraw : Nat → Distribution Nat) (bound : Nat)
    (machine : intDraw bound = uniformRanks bound) (large : integerDraw bound = uniformRanks bound) :
    ticketDraw maximum intDraw integerDraw bound = uniformRanks bound := by
  simp only [ticketDraw, machine, large, ite_self]

/-- A uniform external draw suffices; no frequency backend law is assumed. -/
theorem external_sampling (maximum : Nat) (intDraw integerDraw : Nat → Distribution Nat)
    (weighted : List (Nat × α))
    (machine : intDraw (ticketCount weighted) = uniformRanks (ticketCount weighted))
    (large : integerDraw (ticketCount weighted) = uniformRanks (ticketCount weighted)) :
    Probability.map (select weighted) (ticketDraw maximum intDraw integerDraw (ticketCount weighted)) =
      Probability.map some (normalize (counting (tickets weighted))) := by
  rw [ticketDraw_uniform maximum intDraw integerDraw _ machine large]
  exact sampling_correct weighted

/-- Execute the selected generator with its own distribution. Invalid reads are unused. -/
def run (branches : List (Nat × Distribution α)) : Distribution α :=
  mix (Probability.map (fun selected => selected.getD []) (sampling branches))

/-- Running the selected generator retains all conceptual ticket occurrences. -/
theorem run_expanded (branches : List (Nat × Distribution α)) :
    run branches = frequency (counting (tickets branches)) := by
  rw [run, sampling_correct, map_map]
  change mix (Probability.map id (normalize (counting (tickets branches)))) = _
  rw [show Probability.map id (normalize (counting (tickets branches))) =
    normalize (counting (tickets branches)) by simp [Probability.map]]
  rw [←frequency_eq_mix_normalize]

theorem weightedEvent_append (event : α → Bool)
    (first second : List (Rat × Distribution α)) :
    weightedEvent event (first ++ second) = weightedEvent event first + weightedEvent event second := by
  induction first with
  | nil => simp [weightedEvent, Rat.zero_add]
  | cons head tail ih => simp [weightedEvent, ih, Rat.add_assoc]

/-- Repeating a generator once per ticket multiplies its event mass by its weight. -/
theorem weightedEvent_replicate (event : α → Bool) (weight : Nat) (outcomes : Distribution α) :
    weightedEvent event (counting (List.replicate weight outcomes)) =
      (weight : Rat) * eventMass event outcomes := by
  induction weight with
  | zero => simp [counting, weightedEvent]
  | succ weight ih =>
    simpa [counting, List.replicate_succ, weightedEvent, Rat.add_mul, Rat.add_comm] using
      congrArg (fun mass => eventMass event outcomes + mass) ih

/-- Branch expansion derives the original external weighted numerator. -/
theorem weightedEvent_tickets (branches : List (Nat × Distribution α)) (event : α → Bool) :
    weightedEvent event (counting (tickets branches)) = weightedEvent event (weightDistribution branches) := by
  induction branches with
  | nil => rfl
  | cons branch rest ih =>
    simp only [tickets, List.flatMap_cons, counting, List.map_append]
    rw [weightedEvent_append]
    change weightedEvent event (counting (List.replicate branch.1 branch.2)) +
      weightedEvent event (counting (tickets rest)) = _
    rw [weightedEvent_replicate, ih]
    rfl

/-- The source frequency result agrees on every event with the exact backend. -/
theorem run_event (branches : List (Nat × Distribution α)) (event : α → Bool) :
    eventMass event (run branches) = eventMass event (frequency (weightDistribution branches)) := by
  rw [run_expanded, eventMass_frequency, weightedEvent_tickets, eventMass_frequency]
  have branch_total (input : List (Rat × Distribution α)) : branchWeight input = total input := by
    induction input with
    | nil => rfl
    | cons head tail ih => simp [branchWeight, total, ih]
  rw [branch_total, total_counting, tickets_length, branch_total, weightDistribution_total]

/-- A ticket-selected generator always comes from an original alternative. -/
theorem mem_tickets (weighted : List (Nat × α)) (value : α) (member : value ∈ tickets weighted) :
    ∃ weight, (weight, value) ∈ weighted := by
  obtain ⟨entry, present, inside⟩ := List.mem_flatMap.mp member
  have equal : value = entry.2 := (List.mem_replicate.mp inside).2
  exact ⟨entry.1, by simpa only [equal] using present⟩

/-- The derived source distribution is normalized when every branch is a probability. -/
theorem run_probability (branches : List (Nat × Distribution α))
    (positive : 0 < ticketCount branches)
    (probability : ∀ branch ∈ branches, IsProbability branch.2) : IsProbability (run branches) := by
  rw [run_expanded]
  apply frequency_probability
  · intro branch present
    obtain ⟨outcomes, member, rfl⟩ := List.mem_map.mp present
    obtain ⟨weight, member⟩ := mem_tickets branches outcomes member
    exact ⟨by change (0 : Rat) ≤ 1; decide, probability (weight, outcomes) member⟩
  · have same : branchWeight (counting (tickets branches)) = (ticketCount branches : Rat) := by
      have count (values : List (Distribution α)) : branchWeight (counting values) = (values.length : Rat) := by
        induction values with
        | nil => rfl
        | cons head tail ih =>
          change 1 + branchWeight (counting tail) = ((tail.length + 1 : Nat) : Rat)
          rw [ih]
          simp [Rat.add_comm]
      rw [count, tickets_length]
    rw [same]
    exact_mod_cast positive

/-- The selected branch retains its actual rank/value replay relation. -/
theorem run_replays (decode : Nat → Option α) (branches : List (Nat × Distribution (Nat × α)))
    (replays : ∀ branch ∈ branches, SamplerReplay.Replays decode branch.2) :
    SamplerReplay.Replays decode (run branches) := by
  rw [run_expanded]
  apply SamplerReplay.replays_frequency
  intro branch present
  obtain ⟨outcomes, member, rfl⟩ := List.mem_map.mp present
  obtain ⟨weight, member⟩ := mem_tickets branches outcomes member
  exact replays (weight, outcomes) member

/-- The empty source branch raises the exact backend error before any draw. -/
def frequencyGen (branches : List (Nat × Distribution α)) : Except String (Distribution α) :=
  match branches with
  | [] => .error "microcfta-generator bug: no ranked QuickCheck alternative"
  | _ :: _ => .ok (run branches)

/-- Empty rejection is separate from every successful finite generator choice. -/
theorem frequencyGen_empty : frequencyGen ([] : List (Nat × Distribution α)) =
    .error "microcfta-generator bug: no ranked QuickCheck alternative" := rfl

/-- Successful source dispatch has the exact weighted event law. -/
theorem frequencyGen_event (branches : List (Nat × Distribution α)) (nonempty : branches ≠ []) :
    ∃ output, frequencyGen branches = .ok output ∧
      ∀ event, eventMass event output = eventMass event (frequency (weightDistribution branches)) := by
  cases branches with
  | nil => contradiction
  | cons first rest => exact ⟨run (first :: rest), rfl, run_event (first :: rest)⟩

/-- Ranked.fromWeighted supplies one pure generator for each input occurrence. -/
def pureBranches (weighted : List (Nat × α)) : List (Nat × Distribution α) :=
  weighted.map fun entry => (entry.1, [(1, entry.2)])

/-- The Exact interpretation of the source pure branches is the normalized input weight list. -/
theorem pureBranches_exact (weighted : List (Nat × α)) :
    frequency (weightDistribution (pureBranches weighted)) = normalize (weightDistribution weighted) := by
  have mixed : mix (weightDistribution (pureBranches weighted)) = weightDistribution weighted := by
    induction weighted with
    | nil => rfl
    | cons first rest ih =>
      simpa [pureBranches, weightDistribution, mix, scale, Rat.mul_one] using
        congrArg (fun tail => ((first.1 : Rat), first.2) :: tail) ih
  have weight : branchWeight (weightDistribution (pureBranches weighted)) = total (weightDistribution weighted) := by
    clear mixed
    induction weighted with
    | nil => rfl
    | cons first rest ih =>
      simpa [pureBranches, weightDistribution, branchWeight, total] using congrArg (fun tail => (first.1 : Rat) + tail) ih
  rw [frequency, mixed, weight]
  rfl

/-- The actual QuickCheck value field aggregates duplicate output weights exactly. -/
theorem fromWeighted_event (weighted : List (Nat × α)) (event : α → Bool) :
    eventMass event (run (pureBranches weighted)) = (eventWeight event weighted : Rat) / ticketCount weighted := by
  rw [run_event, pureBranches_exact, normalize, eventMass_scale, weightDistribution_event, weightDistribution_total]
  simp only [Rat.div_def, Rat.mul_comm]

/-- Ranked.fromWeighted retains the list position as the replay rank of each occurrence. -/
def rankedBranches (weighted : List (Nat × α)) : List (Nat × Distribution (Nat × α)) :=
  weighted.zipIdx.map fun entry => (entry.1.1, [(1, (entry.2, entry.1.2))])

/-- Concrete source ranks replay without any uniqueness assumption on output values. -/
theorem fromWeighted_replays (weighted : List (Nat × α)) :
    SamplerReplay.Replays (fun rank => (weighted.map Prod.snd)[rank]?) (run (rankedBranches weighted)) := by
  apply run_replays
  intro branch present
  obtain ⟨indexed, member, rfl⟩ := List.mem_map.mp present
  intro output present
  have same : output = (1, (indexed.2, indexed.1.2)) := by simpa using present
  subst output
  have found := List.mem_zipIdx_iff_getElem?.mp member
  simp only [List.getElem?_map, found, Option.map_some]

end MicroCFTA.SourceQuickCheckFrequency
