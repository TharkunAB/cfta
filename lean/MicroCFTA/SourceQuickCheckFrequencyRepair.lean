import MicroCFTA.SourceQuickCheckFrequencyMachine

/-!
# The repaired QuickCheck midpoint

The source subtracts the lower index before division and adds it afterward.
Every operation fits whenever the finite array length fits in signed Int.
The historical doubled-index bound and counterexamples remain unchanged.
-/
namespace MicroCFTA.SourceQuickCheckFrequencyRepair
open Probability DecoderMachineBounds
open SourceQuickCheckFrequency (upperAt cumulative pick select ticketDraw run rankedBranches)

/-- The repaired lower midpoint preserves the original mathematical position. -/
def midpoint (low high : Nat) : Nat := low + (high - low) / 2

theorem midpoint_eq (low high : Nat) (ordered : low ≤ high) :
    midpoint low high = (low + high) / 2 := by unfold midpoint; omega

/-- Subtraction and the final sum stay between the original nonnegative indices. -/
theorem midpoint_bounds (low high : Nat) (ordered : low ≤ high) :
    low ≤ midpoint low high ∧ midpoint low high ≤ high := by unfold midpoint; omega

/-- Execute signed subtraction, signed quotient by two, and machine addition. -/
def midpointMachine (bits low high : Nat) : Int :=
  let difference := signed bits (subtract bits (cast bits high) (cast bits low))
  let quotient := Int.tdiv difference 2
  signed bits (add bits (cast bits low) (cast bits quotient.toNat))

/-- The signed difference and quotient are exact and nonnegative before the final addition. -/
theorem difference_quotient (bits low high : Nat) (ordered : low ≤ high) (fits : high ≤ maximum bits) :
    signed bits (subtract bits (cast bits high) (cast bits low)) = ((high - low : Nat) : Int) ∧
      Int.tdiv (signed bits (subtract bits (cast bits high) (cast bits low))) 2 =
        (((high - low) / 2 : Nat) : Int) := by
  have difference : signed bits (subtract bits (cast bits high) (cast bits low)) = ((high - low : Nat) : Int) := by
    rw [subtract_cast bits high low fits ordered]
    exact narrow_exact bits _ (by omega)
  exact ⟨difference, by rw [difference]; rfl⟩

/-- The repaired machine midpoint needs no bound on the sum of its two indices. -/
theorem midpoint_machine (bits low high : Nat) (ordered : low ≤ high) (fits : high ≤ maximum bits) :
    midpointMachine bits low high = (midpoint low high : Int) := by
  have bounds := midpoint_bounds low high ordered
  dsimp only [midpointMachine]
  rw [(difference_quotient bits low high ordered fits).2, Int.toNat_natCast]
  exact add_exact bits low ((high - low) / 2) (by change midpoint low high ≤ maximum bits; omega)

/-- The finite source array needs only a representable length. -/
def ArrayFits (bits count : Nat) : Prop := count ≤ maximum bits

/-- Every source interval has exact indices and the original mathematical midpoint. -/
theorem search_machine (bits count low high : Nat) (fits : ArrayFits bits count)
    (ordered : low ≤ high) (within : high < count) :
    narrow bits low = (low : Int) ∧ narrow bits high = (high : Int) ∧
      midpointMachine bits low high = (((low + high) / 2 : Nat) : Int) := by
  have highFits : high ≤ maximum bits := by unfold ArrayFits at fits; omega
  refine ⟨narrow_exact bits low (by omega), narrow_exact bits high highFits, ?_⟩
  rw [midpoint_machine bits low high ordered highFits, midpoint_eq low high ordered]

/-- The source ticket guard now proves array safety for positive-weight alternatives. -/
theorem arrayFits_of_total (bits : Nat) (weighted : List (Nat × α))
    (positive : ∀ entry ∈ weighted, 0 < entry.1)
    (fits : ticketCount weighted ≤ maximum bits) : ArrayFits bits weighted.length :=
  Nat.le_trans (SourceQuickCheckFrequency.length_le_weight weighted positive) fits

/-- Execute the repaired signed search; negative intermediate indices represent failed array access. -/
def machinePick (bits : Nat) (upper : Nat → Nat) (selected : Nat) : Nat → Nat → Nat → Option Nat
  | 0, _, _ => none
  | fuel + 1, low, high =>
    if low = high then some low
    else
      let middle := midpointMachine bits low high
      if middle < 0 then none
      else if selected < upper middle.toNat then machinePick bits upper selected fuel low middle.toNat
      else
        let next := narrow bits (middle.toNat + 1)
        if next < 0 then none
        else machinePick bits upper selected fuel next.toNat high

/-- Every repaired source search terminates with the same selected array position. -/
theorem machinePick_correct (bits count : Nat) (fits : ArrayFits bits count)
    (upper : Nat → Nat) (selected fuel low high : Nat)
    (ordered : low ≤ high) (within : high < count) (enough : high - low < fuel) :
    machinePick bits upper selected fuel low high = some (pick upper selected low high ordered) := by
  induction fuel generalizing low high with
  | zero => omega
  | succ fuel ih =>
    by_cases same : low = high
    · subst low
      rw [machinePick, ite_eq_left rfl, pick, dite_eq_left rfl]
    · have strict : low < high := by omega
      have bounds := SourceQuickCheckFrequency.midpoint_bounds low high strict
      have middle := (search_machine bits count low high fits ordered within).2.2
      have next : narrow bits ((low + high) / 2 + 1) = (((low + high) / 2 + 1 : Nat) : Int) :=
        narrow_exact bits _ (by unfold ArrayFits at fits; omega)
      rw [machinePick, ite_eq_right same, middle,
        ite_eq_right (show ¬(((low + high) / 2 : Nat) : Int) < 0 by omega)]
      simp only [Int.toNat_natCast]
      rw [pick, dite_eq_right same]
      dsimp only
      split
      · exact ih low ((low + high) / 2) bounds.1 (by omega) (by omega)
      · rw [next, ite_eq_right (show ¬(((low + high) / 2 + 1 : Nat) : Int) < 0 by omega)]
        simp only [Int.toNat_natCast]
        exact ih ((low + high) / 2 + 1) high (by omega) within (by omega)

/-- One call per array entry suffices for every source search. -/
theorem search_complete (bits : Nat) (weighted : List (Nat × α)) (fits : ArrayFits bits weighted.length)
    (nonempty : 0 < weighted.length) (ticket : Nat) :
    machinePick bits (upperAt weighted) ticket weighted.length 0 (weighted.length - 1) =
      some (pick (upperAt weighted) ticket 0 (weighted.length - 1) (by omega)) :=
  machinePick_correct bits weighted.length fits (upperAt weighted) ticket weighted.length 0
    (weighted.length - 1) (by omega) (by omega) (by omega)

/-- Read the original generator at the repaired signed search result. -/
def machineSelect (bits : Nat) (weighted : List (Nat × α)) (ticket : Nat) : Option α := do
  let index ← machinePick bits (upperAt weighted) ticket weighted.length 0 (weighted.length - 1)
  ((cumulative weighted)[index]?).map Prod.snd

/-- The repair retains every selected occurrence and the original alternative order. -/
theorem machineSelect_eq (bits : Nat) (weighted : List (Nat × α)) (fits : ArrayFits bits weighted.length)
    (ticket : Nat) : machineSelect bits weighted ticket = select weighted ticket := by
  by_cases nonempty : 0 < weighted.length
  · rw [machineSelect, search_complete bits weighted fits nonempty ticket, select, dite_eq_left nonempty]
    rfl
  · have empty : weighted = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst weighted
    simp [machineSelect, machinePick, select]

/-- The source Int-ticket guard proves every conversion and the selected branch interval. -/
theorem small_ticket_path (bits : Nat) (weighted : List (Nat × α))
    (positive : ∀ entry ∈ weighted, 0 < entry.1)
    (guard : ticketCount weighted ≤ maximum bits) (ticket : Nat) (valid : ticket < ticketCount weighted) :
    narrow bits weighted.length = (weighted.length : Int) ∧
      SourceQuickCheckFrequency.ticketUpperMachine bits weighted.length = ((weighted.length - 1 : Nat) : Int) ∧
      narrow bits ticket = (ticket : Int) ∧
      ∃ index entry, weighted[index]? = some entry ∧
        SourceQuickCheckFrequency.weightBefore weighted index ≤ ticket ∧
        ticket < SourceQuickCheckFrequency.weightBefore weighted index + entry.1 ∧
        machineSelect bits weighted ticket = some entry.2 := by
  have fits := arrayFits_of_total bits weighted positive guard
  have nonempty : 0 < weighted.length := by cases weighted <;> simp_all [ticketCount]
  refine ⟨narrow_exact bits weighted.length fits,
    SourceQuickCheckFrequency.ticket_upper_machine bits weighted.length nonempty fits,
    narrow_exact bits ticket (by omega), ?_⟩
  rw [machineSelect_eq bits weighted fits]
  exact SourceQuickCheckFrequency.select_interval weighted ticket valid

/-- The repaired backend draws a ticket, executes its search, and runs the selected generator. -/
def machineRun (bits : Nat) (intDraw integerDraw : Nat → Distribution Nat)
    (branches : List (Nat × Distribution α)) : Distribution α :=
  mix (Probability.map (fun selected => selected.getD [])
    (Probability.map (machineSelect bits branches)
      (ticketDraw (maximum bits) intDraw integerDraw (ticketCount branches))))

/-- Uniform external draws give the derived branch distribution with only a representable array. -/
theorem machineRun_eq (bits : Nat) (intDraw integerDraw : Nat → Distribution Nat)
    (branches : List (Nat × Distribution α)) (fits : ArrayFits bits branches.length)
    (machine : intDraw (ticketCount branches) = Sampler.uniformRanks (ticketCount branches))
    (large : integerDraw (ticketCount branches) = Sampler.uniformRanks (ticketCount branches)) :
    machineRun bits intDraw integerDraw branches = run branches := by
  have same : machineSelect bits branches = select branches := funext (machineSelect_eq bits branches fits)
  rw [machineRun, SourceQuickCheckFrequency.ticketDraw_uniform _ _ _ _ machine large, same]
  rfl

/-- The complete repaired backend retains the Exact interpretation of every output event. -/
theorem machineRun_event (bits : Nat) (intDraw integerDraw : Nat → Distribution Nat)
    (branches : List (Nat × Distribution α)) (fits : ArrayFits bits branches.length)
    (machine : intDraw (ticketCount branches) = Sampler.uniformRanks (ticketCount branches))
    (large : integerDraw (ticketCount branches) = Sampler.uniformRanks (ticketCount branches)) (event : α → Bool) :
    eventMass event (machineRun bits intDraw integerDraw branches) =
      eventMass event (frequency (Sampler.weightDistribution branches)) := by
  rw [machineRun_eq bits intDraw integerDraw branches fits machine large]
  exact SourceQuickCheckFrequency.run_event branches event

/-- The repaired search preserves every sampled rank/value replay relation. -/
theorem machineRun_replays (bits : Nat) (intDraw integerDraw : Nat → Distribution Nat)
    (decode : Nat → Option α) (branches : List (Nat × Distribution (Nat × α)))
    (fits : ArrayFits bits branches.length)
    (machine : intDraw (ticketCount branches) = Sampler.uniformRanks (ticketCount branches))
    (large : integerDraw (ticketCount branches) = Sampler.uniformRanks (ticketCount branches))
    (replays : ∀ branch ∈ branches, SamplerReplay.Replays decode branch.2) :
    SamplerReplay.Replays decode (machineRun bits intDraw integerDraw branches) := by
  rw [machineRun_eq bits intDraw integerDraw branches fits machine large]
  exact SourceQuickCheckFrequency.run_replays decode branches replays

/-- Concrete Ranked.fromWeighted replay follows from the actual indexed pure alternatives. -/
theorem fromWeighted_replays (bits : Nat) (intDraw integerDraw : Nat → Distribution Nat)
    (weighted : List (Nat × α)) (fits : ArrayFits bits weighted.length)
    (machine : intDraw (ticketCount (rankedBranches weighted)) = Sampler.uniformRanks (ticketCount (rankedBranches weighted)))
    (large : integerDraw (ticketCount (rankedBranches weighted)) = Sampler.uniformRanks (ticketCount (rankedBranches weighted))) :
    SamplerReplay.Replays (fun rank => (weighted.map Prod.snd)[rank]?)
      (machineRun bits intDraw integerDraw (rankedBranches weighted)) := by
  rw [machineRun_eq bits intDraw integerDraw (rankedBranches weighted)
    (by simpa only [rankedBranches, List.length_map, List.length_zipIdx] using fits) machine large]
  exact SourceQuickCheckFrequency.fromWeighted_replays weighted

/-- The former failing 64-bit midpoint now stays inside its valid search interval. -/
theorem repaired_midpoint_64 :
    let count := 9223372036854775807
    let low := 4611686018427387904
    let high := count - 1
    midpointMachine 63 low high = 6917529027641081855 := by decide +kernel

end MicroCFTA.SourceQuickCheckFrequencyRepair
