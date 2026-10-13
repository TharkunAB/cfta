import MicroCFTA.SourceQuickCheckFrequencyProbability
import MicroCFTA.DecoderMachineBounds

/-!
# Historical machine bounds of the QuickCheck frequency search

The former source midpoint adds two Int indices before signed quotient by two.
The source total-weight guard checks ticket narrowing, not this index sum.
The explicit array bound below is sufficient for every recursive search.
SourceQuickCheckFrequencyRepair proves the current source expression.
-/
namespace MicroCFTA.SourceQuickCheckFrequency
open Probability DecoderMachineBounds

/-- The actual Int midpoint wraps addition before quotient truncates toward zero. -/
def midpointMachine (bits low high : Nat) : Int :=
  Int.tdiv (signed bits (add bits (cast bits low) (cast bits high))) 2

/-- A representable index sum makes the actual midpoint exact. -/
theorem midpoint_machine (bits low high : Nat) (fits : low + high ≤ maximum bits) :
    midpointMachine bits low high = (((low + high) / 2 : Nat) : Int) := by
  rw [midpointMachine, add_exact bits low high fits]
  rfl

/-- The list length and every possible midpoint sum fit the source signed Int. -/
def ArrayFits (bits count : Nat) : Prop := count ≤ maximum bits ∧ 2 * (count - 1) ≤ maximum bits

/-- Every active source array interval has exact Int indices and midpoint arithmetic. -/
theorem search_machine (bits count low high : Nat) (fits : ArrayFits bits count)
    (ordered : low ≤ high) (within : high < count) :
    narrow bits low = (low : Int) ∧ narrow bits high = (high : Int) ∧
      midpointMachine bits low high = (((low + high) / 2 : Nat) : Int) := by
  refine ⟨narrow_exact bits low (by rcases fits with ⟨_, _⟩; omega),
    narrow_exact bits high (by rcases fits with ⟨_, _⟩; omega), ?_⟩
  apply midpoint_machine
  rcases fits with ⟨_, sumFits⟩
  omega

/-- Each recursive branch retains the same global array bound. -/
theorem search_children (bits count low high : Nat) (fits : ArrayFits bits count)
    (strict : low < high) (within : high < count) :
    let middle := (low + high) / 2
    low ≤ middle ∧ middle < count ∧ middle + 1 ≤ high ∧
      narrow bits (middle + 1) = ((middle + 1 : Nat) : Int) ∧
      midpointMachine bits low high = (middle : Int) := by
  have bounds := midpoint_bounds low high strict
  refine ⟨bounds.1, by omega, by omega, narrow_exact bits _ (by rcases fits with ⟨_, _⟩; omega),
    (search_machine bits count low high fits (by omega) within).2.2⟩

/-- Positive alternative weights bound the number of array entries by their total. -/
theorem length_le_weight (weighted : List (Nat × α))
    (positive : ∀ entry ∈ weighted, 0 < entry.1) : weighted.length ≤ ticketCount weighted := by
  induction weighted with
  | nil => exact Nat.le_refl 0
  | cons first rest ih =>
    have head := positive first (by simp)
    have tail := ih (fun entry present => positive entry (by simp [present]))
    simp only [List.length_cons, ticketCount]
    omega

/-- A smaller total supplies a sufficient array bound without an independent length premise. -/
theorem arrayFits_of_total (bits : Nat) (weighted : List (Nat × α))
    (positive : ∀ entry ∈ weighted, 0 < entry.1)
    (fits : ticketCount weighted ≤ maximum bits / 2) : ArrayFits bits weighted.length := by
  have bound := length_le_weight weighted positive
  constructor <;> omega

/-- The Int ticket branch subtracts one only after its positive total fits. -/
def ticketUpperMachine (bits total : Nat) : Int :=
  signed bits (subtract bits (cast bits total) (cast bits 1))

/-- The source chooseInt upper endpoint is the exact last ticket. -/
theorem ticket_upper_machine (bits total : Nat) (positive : 0 < total) (fits : total ≤ maximum bits) :
    ticketUpperMachine bits total = ((total - 1 : Nat) : Int) := by
  rw [ticketUpperMachine, subtract_cast bits total 1 fits (by omega)]
  exact narrow_exact bits _ (by omega)

/-- Both ticket paths preserve every sampled ticket; the wide path does not narrow it. -/
theorem ticket_paths (bits total ticket : Nat) (valid : ticket < total) :
    (if total ≤ maximum bits then narrow bits ticket else (ticket : Int)) = (ticket : Int) := by
  split
  next fits => exact narrow_exact bits ticket (by omega)
  · rfl

/-- Execute signed midpoint arithmetic. None marks exhausted fuel or an invalid negative index. -/
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

/-- The source Int search terminates and equals the derived search under the array bound. -/
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
      have bounds := midpoint_bounds low high strict
      have middle := (search_machine bits count low high fits ordered within).2.2
      have next := (search_children bits count low high fits strict within).2.2.2.1
      rw [machinePick, ite_eq_right same, middle,
        ite_eq_right (show ¬(((low + high) / 2 : Nat) : Int) < 0 by omega)]
      simp only [Int.toNat_natCast]
      rw [pick, dite_eq_right same]
      dsimp only
      split
      · exact ih low ((low + high) / 2) bounds.1 (by omega) (by omega)
      · rw [next]
        rw [ite_eq_right (show ¬(((low + high) / 2 + 1 : Nat) : Int) < 0 by omega)]
        simp only [Int.toNat_natCast]
        exact ih ((low + high) / 2 + 1) high (by omega) within (by omega)

/-- At most one call per array entry suffices for every valid ticket search. -/
theorem machine_search_complete (bits : Nat) (weighted : List (Nat × α))
    (fits : ArrayFits bits weighted.length) (nonempty : 0 < weighted.length) (ticket : Nat) :
    machinePick bits (upperAt weighted) ticket weighted.length 0 (weighted.length - 1) =
      some (pick (upperAt weighted) ticket 0 (weighted.length - 1) (by omega)) :=
  machinePick_correct bits weighted.length fits (upperAt weighted) ticket weighted.length 0
    (weighted.length - 1) (by omega) (by omega) (by omega)

/-- Read the selected original generator after the bounded signed search. -/
def machineSelect (bits : Nat) (weighted : List (Nat × α)) (ticket : Nat) : Option α := do
  let index ← machinePick bits (upperAt weighted) ticket weighted.length 0 (weighted.length - 1)
  ((cumulative weighted)[index]?).map Prod.snd

/-- Safe machine execution gives exactly the same occurrence as the ordered source model. -/
theorem machineSelect_eq (bits : Nat) (weighted : List (Nat × α)) (fits : ArrayFits bits weighted.length)
    (ticket : Nat) : machineSelect bits weighted ticket = select weighted ticket := by
  by_cases nonempty : 0 < weighted.length
  · rw [machineSelect, machine_search_complete bits weighted fits nonempty ticket, select, dite_eq_left nonempty]
    rfl
  · have empty : weighted = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst weighted
    simp [machineSelect, machinePick, select]

/-- The actual signed search derives the backend's weight-over-total law. -/
theorem machine_sampling_event (bits : Nat) (weighted : List (Nat × α)) (fits : ArrayFits bits weighted.length)
    (event : α → Bool) :
    eventMass (fun selected => selected.any event)
      (Probability.map (machineSelect bits weighted) (Sampler.uniformRanks (ticketCount weighted))) =
      (eventWeight event weighted : Rat) / ticketCount weighted := by
  have same : machineSelect bits weighted = select weighted := funext (machineSelect_eq bits weighted fits)
  rw [same]
  exact sampling_event weighted event

/-- The complete backend draws its ticket, executes signed search, then runs that generator. -/
def machineRun (bits : Nat) (intDraw integerDraw : Nat → Distribution Nat)
    (branches : List (Nat × Distribution α)) : Distribution α :=
  mix (Probability.map (fun selected => selected.getD [])
    (Probability.map (machineSelect bits branches)
      (ticketDraw (maximum bits) intDraw integerDraw (ticketCount branches))))

/-- Uniform external tickets and derived array safety give the complete generator distribution. -/
theorem machineRun_eq (bits : Nat) (intDraw integerDraw : Nat → Distribution Nat)
    (branches : List (Nat × Distribution α)) (fits : ArrayFits bits branches.length)
    (machine : intDraw (ticketCount branches) = Sampler.uniformRanks (ticketCount branches))
    (large : integerDraw (ticketCount branches) = Sampler.uniformRanks (ticketCount branches)) :
    machineRun bits intDraw integerDraw branches = run branches := by
  have same : machineSelect bits branches = select branches := funext (machineSelect_eq bits branches fits)
  rw [machineRun, ticketDraw_uniform _ _ _ _ machine large, same]
  rfl

/-- The complete QuickCheck implementation has the Exact backend's weighted event law. -/
theorem machineRun_event (bits : Nat) (intDraw integerDraw : Nat → Distribution Nat)
    (branches : List (Nat × Distribution α)) (fits : ArrayFits bits branches.length)
    (machine : intDraw (ticketCount branches) = Sampler.uniformRanks (ticketCount branches))
    (large : integerDraw (ticketCount branches) = Sampler.uniformRanks (ticketCount branches)) (event : α → Bool) :
    eventMass event (machineRun bits intDraw integerDraw branches) =
      eventMass event (frequency (Sampler.weightDistribution branches)) := by
  rw [machineRun_eq bits intDraw integerDraw branches fits machine large]
  exact run_event branches event

/-- A four-bit witness shows why the total guard alone cannot justify midpoint arithmetic. -/
theorem unchecked_midpoint_small :
    7 ≤ maximum 3 ∧ 0 ≤ (4 : Nat) ∧ 4 < 6 ∧ 6 < 7 ∧
      midpointMachine 3 4 6 = -3 ∧ (4 + 6) / 2 = (5 : Nat) := by decide +kernel

/-- The same unchecked addition can wrap in the source 64-bit Int range. -/
theorem unchecked_midpoint_64 :
    let count := 9223372036854775807
    let low := 4611686018427387904
    let high := count - 1
    count ≤ maximum 63 ∧ low < high ∧ high < count ∧
      midpointMachine 63 low high = -2305843009213693953 := by decide +kernel

/-- An all-unit array at the signed length limit reaches a negative second midpoint. -/
theorem unchecked_search_64 :
    let count := 9223372036854775807
    machinePick 63 (fun index => index + 1) (count - 1) 3 0 (count - 1) = none := by decide +kernel

end MicroCFTA.SourceQuickCheckFrequency
