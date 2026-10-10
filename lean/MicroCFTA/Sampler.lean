import MicroCFTA.SizeMass
import MicroCFTA.SizedRank

/-!
# Concrete finite sampling

This module models the exact arithmetic and finite algorithms in
`Ranked.Internal.Sampler`. Natural weights and ranks follow the source's
positivity and range checks. Rational normalization has no rounding.
The sampling backend's randomness and retry behavior require explicit laws.
The finite grouping and cumulative array are represented by ordered lists.
Theorems derive the bounds required by signed machine conversion. They do not
verify GHC conversion instructions. Recursive sampler knot productivity and
backend random-number generation remain separate obligations.
-/

namespace MicroCFTA.Sampler

open Probability

local instance : Std.Associative (α := Rat) (· * ·) := ⟨Rat.mul_assoc⟩
local instance : Std.Commutative (α := Rat) (· * ·) := ⟨Rat.mul_comm⟩

/-- The least common multiple of a finite list, starting at one. -/
def lcmList : List Nat → Nat
  | [] => 1
  | value :: values => Nat.lcm value (lcmList values)

/-- The greatest common divisor of a finite list, starting at zero. -/
def gcdList : List Nat → Nat
  | [] => 0
  | value :: values => Nat.gcd value (gcdList values)

/-- The denominator fold equals the source's left fold. -/
theorem lcmList_foldl (values : List Nat) (initial : Nat) :
    values.foldl Nat.lcm initial = Nat.lcm initial (lcmList values) := by
  induction values generalizing initial with
  | nil => simp [lcmList]
  | cons value values ih => simp [lcmList, ih, Nat.lcm_assoc]

/-- The common-factor fold equals the source's left fold. -/
theorem gcdList_foldl (values : List Nat) (initial : Nat) :
    values.foldl Nat.gcd initial = Nat.gcd initial (gcdList values) := by
  induction values generalizing initial with
  | nil => simp [gcdList]
  | cons value values ih => simp [gcdList, ih, Nat.gcd_assoc]

/-- Every positive denominator list has a positive common multiple. -/
theorem lcmList_positive (values : List Nat) (positive : ∀ value ∈ values, 0 < value) :
    0 < lcmList values := by
  induction values with
  | nil => decide
  | cons value values ih =>
      exact Nat.lcm_pos (positive value (by simp)) (ih (fun other member => positive other (by simp [member])))

/-- Every listed denominator divides the computed common denominator. -/
theorem dvd_lcmList (values : List Nat) (value : Nat) (member : value ∈ values) : value ∣ lcmList values := by
  induction values with
  | nil => simp at member
  | cons first values ih =>
      rcases List.mem_cons.mp member with same | member
      · subst value; exact Nat.dvd_lcm_left _ _
      · exact Nat.dvd_trans (ih member) (Nat.dvd_lcm_right _ _)

/-- The common factor divides every listed integer mass. -/
theorem gcdList_dvd (values : List Nat) (value : Nat) (member : value ∈ values) : gcdList values ∣ value := by
  induction values with
  | nil => simp at member
  | cons first values ih =>
      rcases List.mem_cons.mp member with same | member
      · subst value; exact Nat.gcd_dvd_left _ _
      · exact Nat.dvd_trans (Nat.gcd_dvd_right _ _) (ih member)

/-- A positive member makes the computed common factor positive. -/
theorem gcdList_positive (values : List Nat) (value : Nat) (member : value ∈ values) (positive : 0 < value) :
    0 < gcdList values := by
  induction values with
  | nil => simp at member
  | cons first values ih =>
      rcases List.mem_cons.mp member with same | member
      · subst value; exact Nat.gcd_pos_of_pos_left _ positive
      · exact Nat.gcd_pos_of_pos_right _ (ih member)

/-- Convert an exact natural quotient to the same rational quotient. -/
theorem natCast_div (numerator denominator : Nat) (divides : denominator ∣ numerator)
    (positive : 0 < denominator) :
    ((numerator / denominator : Nat) : Rat) = (numerator : Rat) / (denominator : Rat) := by
  have exactProduct : ((numerator / denominator : Nat) : Rat) * (denominator : Rat) = numerator := by
    rw [← Rat.natCast_mul, Nat.div_mul_cancel divides]
  have nonzero : (denominator : Rat) ≠ 0 := Rat.ne_of_gt (Rat.natCast_pos.mpr positive)
  calc
    _ = (((numerator / denominator : Nat) : Rat) * (denominator : Rat)) / denominator :=
      (Rat.mul_div_cancel nonzero).symm
    _ = _ := congrArg (fun value : Rat => value / denominator) exactProduct

/-- The computed common denominator of the input rational masses. -/
def commonDenominator (outcomes : Distribution α) : Nat :=
  lcmList (outcomes.map (fun entry => entry.1.den))

/-- Scale a positive rational mass to the common integer denominator. -/
def unscaled (denominator : Nat) (mass : Rat) : Nat :=
  mass.num.toNat * (denominator / mass.den)

/-- Compute the source's intermediate integer masses. -/
def unscaledMasses (outcomes : Distribution α) : List Nat :=
  outcomes.map (fun entry => unscaled (commonDenominator outcomes) entry.1)

/-- Divide every intermediate mass by their common factor. Values retain their order. -/
def integerMasses (outcomes : Distribution α) : List (Nat × α) :=
  outcomes.map (fun entry =>
    (unscaled (commonDenominator outcomes) entry.1 / gcdList (unscaledMasses outcomes), entry.2))

/-- Rational denominators make the computed common denominator positive. -/
theorem commonDenominator_positive (outcomes : Distribution α) : 0 < commonDenominator outcomes := by
  apply lcmList_positive
  intro denominator member
  obtain ⟨entry, _, same⟩ := List.mem_map.mp member
  exact same ▸ entry.1.den_pos

/-- Every input denominator divides the computed common denominator. -/
theorem denominator_dvd_common (outcomes : Distribution α) (entry : Rat × α) (member : entry ∈ outcomes) :
    entry.1.den ∣ commonDenominator outcomes :=
  dvd_lcmList _ _ (List.mem_map.mpr ⟨entry, member, rfl⟩)

/-- Converting the positive numerator to a natural number preserves its exact rational value. -/
theorem unscaled_exact (denominator : Nat) (mass : Rat) (nonnegative : 0 ≤ mass)
    (divides : mass.den ∣ denominator) : (unscaled denominator mass : Rat) = (denominator : Rat) * mass := by
  have numeratorNonnegative : 0 ≤ mass.num := Rat.num_nonneg.mpr nonnegative
  have numerator : (mass.num.toNat : Rat) = (mass.num : Rat) := by
    rw [← Rat.intCast_natCast, Int.toNat_of_nonneg numeratorNonnegative]
  have fraction : (mass.num : Rat) / (mass.den : Rat) = mass := by
    simpa only [Rat.divInt_eq_div, Rat.intCast_natCast] using Rat.num_divInt_den mass
  rw [unscaled, Rat.natCast_mul, numerator, natCast_div denominator mass.den divides mass.den_pos]
  calc
    _ = (denominator : Rat) * ((mass.num : Rat) / (mass.den : Rat)) := by
      simp only [Rat.div_def]
      ac_rfl
    _ = _ := congrArg ((denominator : Rat) * ·) fraction

/-- Every positive input mass becomes a positive intermediate integer mass. -/
theorem unscaled_positive (outcomes : Distribution α) (entry : Rat × α)
    (member : entry ∈ outcomes) (positive : 0 < entry.1) :
    0 < unscaled (commonDenominator outcomes) entry.1 := by
  apply Rat.natCast_pos.mp
  rw [unscaled_exact _ _ (Rat.le_of_lt positive) (denominator_dvd_common outcomes entry member)]
  exact Rat.mul_pos (Rat.natCast_pos.mpr (commonDenominator_positive outcomes)) positive

/-- A nonempty positive mass list has a positive common factor. -/
theorem commonFactor_positive (outcomes : Distribution α) (nonempty : outcomes ≠ [])
    (positive : ∀ entry ∈ outcomes, 0 < entry.1) : 0 < gcdList (unscaledMasses outcomes) := by
  cases outcomes with
  | nil => contradiction
  | cons entry entries =>
      apply gcdList_positive _ (unscaled (commonDenominator (entry :: entries)) entry.1)
      · exact List.mem_map.mpr ⟨entry, by simp, rfl⟩
      · exact unscaled_positive _ entry (by simp) (positive entry (by simp))

/-- Every common divisor of the listed values divides their computed gcd. -/
theorem dvd_gcdList (values : List Nat) (factor : Nat) (divides : ∀ value ∈ values, factor ∣ value) :
    factor ∣ gcdList values := by
  induction values with
  | nil => exact Nat.dvd_zero _
  | cons value values ih =>
      exact Nat.dvd_gcd (divides value (by simp)) (ih (fun other member => divides other (by simp [member])))

/-- Exact common-factor division commutes with the finite gcd fold. -/
theorem gcdList_div (values : List Nat) (factor : Nat) (divides : ∀ value ∈ values, factor ∣ value) :
    gcdList (values.map (· / factor)) = gcdList values / factor := by
  induction values with
  | nil => simp [gcdList]
  | cons value values ih =>
      have tail : ∀ other ∈ values, factor ∣ other := fun other member => divides other (by simp [member])
      simp only [List.map_cons, gcdList, ih tail]
      exact Nat.gcd_div (divides value (by simp)) (dvd_gcdList values factor tail)

/-- Regard integer ticket weights as rational masses without changing their values. -/
def weightDistribution (weighted : List (Nat × α)) : Distribution α :=
  weighted.map (fun entry => ((entry.1 : Rat), entry.2))

/-- Integer conversion changes all rational masses by one common positive scale. -/
theorem integerMasses_scale (outcomes : Distribution α) (nonempty : outcomes ≠ [])
    (positive : ∀ entry ∈ outcomes, 0 < entry.1) :
    weightDistribution (integerMasses outcomes) =
      scale ((commonDenominator outcomes : Rat) / (gcdList (unscaledMasses outcomes) : Rat)) outcomes := by
  have factorPositive := commonFactor_positive outcomes nonempty positive
  simp only [weightDistribution, integerMasses, List.map_map, Function.comp_def, scale]
  apply List.map_congr_left
  intro entry member
  have divides := gcdList_dvd (unscaledMasses outcomes) (unscaled (commonDenominator outcomes) entry.1)
    (List.mem_map.mpr ⟨entry, member, rfl⟩)
  have exact := natCast_div _ _ divides factorPositive
  rw [exact, unscaled_exact _ _ (Rat.le_of_lt (positive entry member))
    (denominator_dvd_common outcomes entry member)]
  congr 1
  simp only [Rat.div_def]
  ac_rfl

/-- Every converted integer weight is positive. -/
theorem integerMasses_positive (outcomes : Distribution α) (nonempty : outcomes ≠ [])
    (positive : ∀ entry ∈ outcomes, 0 < entry.1) :
    ∀ entry ∈ integerMasses outcomes, 0 < entry.1 := by
  intro entry member
  obtain ⟨original, originalMember, same⟩ := List.mem_map.mp member
  subst entry
  have numeratorPositive := unscaled_positive outcomes original originalMember (positive original originalMember)
  have divides := gcdList_dvd (unscaledMasses outcomes) (unscaled (commonDenominator outcomes) original.1)
    (List.mem_map.mpr ⟨original, originalMember, rfl⟩)
  exact Nat.div_pos (Nat.le_of_dvd numeratorPositive divides) (commonFactor_positive outcomes nonempty positive)

/-- Removing the computed gcd leaves primitive integer weights. -/
theorem integerMasses_primitive (outcomes : Distribution α) (nonempty : outcomes ≠ [])
    (positive : ∀ entry ∈ outcomes, 0 < entry.1) :
    gcdList ((integerMasses outcomes).map Prod.fst) = 1 := by
  have factorPositive := commonFactor_positive outcomes nonempty positive
  have mapped : (integerMasses outcomes).map Prod.fst =
      (unscaledMasses outcomes).map (· / gcdList (unscaledMasses outcomes)) := by
    simp only [integerMasses, unscaledMasses, List.map_map, Function.comp_def]
  rw [mapped, gcdList_div _ _ (fun value member => gcdList_dvd _ value member)]
  exact Nat.div_self (by omega)

/-- Integer conversion preserves the entire normalized distribution, including duplicate values. -/
theorem integerMasses_normalize (outcomes : Distribution α) (nonempty : outcomes ≠ [])
    (positive : ∀ entry ∈ outcomes, 0 < entry.1) :
    normalize (weightDistribution (integerMasses outcomes)) = normalize outcomes := by
  rw [integerMasses_scale outcomes nonempty positive]
  apply normalize_scale
  have denominatorPositive := Rat.natCast_pos.mpr (commonDenominator_positive outcomes)
  have factorPositive := Rat.natCast_pos.mpr (commonFactor_positive outcomes nonempty positive)
  exact Rat.ne_of_gt (by
    rw [Rat.div_def]
    exact Rat.mul_pos denominatorPositive (Rat.inv_pos.mpr factorPositive))

/-- Ticket weights and their rational representation have the same total. -/
theorem weightDistribution_total (weighted : List (Nat × α)) :
    total (weightDistribution weighted) = (ticketCount weighted : Rat) := by
  induction weighted with
  | nil => rfl
  | cons entry weighted ih =>
      rcases entry with ⟨weight, value⟩
      change (weight : Rat) + total (weightDistribution weighted) = ((weight + ticketCount weighted : Nat) : Rat)
      rw [ih, Rat.natCast_add]

/-- Ticket weights and their rational representation assign the same mass to every event. -/
theorem weightDistribution_event (weighted : List (Nat × α)) (event : α → Bool) :
    eventMass event (weightDistribution weighted) = (eventWeight event weighted : Rat) := by
  induction weighted with
  | nil => rfl
  | cons entry weighted ih =>
      rcases entry with ⟨weight, value⟩
      simp only [weightDistribution, List.map_cons, eventMass, eventWeight, Rat.natCast_add]
      rw [show eventMass event (List.map (fun entry => ((entry.1 : Rat), entry.2)) weighted) =
        (eventWeight event weighted : Rat) from ih]
      cases event value <;> simp

/-- Uniform integer tickets implement the normalized rational masses after conversion. -/
theorem integerMasses_event_probability (outcomes : Distribution α) (nonempty : outcomes ≠ [])
    (positive : ∀ entry ∈ outcomes, 0 < entry.1) (event : α → Bool) :
    ticketProbability event (integerMasses outcomes) = eventMass event (normalize outcomes) := by
  rw [← integerMasses_normalize outcomes nonempty positive, normalize, eventMass_scale,
    weightDistribution_total, weightDistribution_event, ticketProbability_eq]
  simp only [Rat.div_def]
  ac_rfl

/-- Equal-weight payloads share one compiled ticket block. -/
structure Group (α : Type) where
  width : Nat
  values : List α
  deriving Repr

/-- The number of tickets in one equal-weight group. -/
def Group.cardinality (group : Group α) : Nat := group.width * group.values.length

/-- Insert one payload by ascending weight, prepending within an equal-weight group. -/
def insertGroup (weight : Nat) (value : α) : List (Group α) → List (Group α)
  | [] => [⟨weight, [value]⟩]
  | group :: groups =>
      if weight = group.width then {group with values := value :: group.values} :: groups
      else if weight < group.width then ⟨weight, [value]⟩ :: group :: groups
      else group :: insertGroup weight value groups

/-- Group tickets as in ascending map keys with singleton lists prepended on collisions. -/
def groupWeighted (weighted : List (Nat × α)) : List (Group α) :=
  weighted.foldl (fun groups entry => insertGroup entry.1 entry.2 groups) []

/-- Count every ticket in the compiled groups. -/
def groupTotal : List (Group α) → Nat
  | [] => 0
  | group :: groups => group.cardinality + groupTotal groups

/-- Count tickets whose payload satisfies an event. -/
def groupEvent (event : α → Bool) : List (Group α) → Nat
  | [] => 0
  | group :: groups => group.width * group.values.countP event + groupEvent event groups

/-- Every insertion adds exactly its declared ticket width. -/
theorem insertGroup_total (weight : Nat) (value : α) (groups : List (Group α)) :
    groupTotal (insertGroup weight value groups) = weight + groupTotal groups := by
  induction groups with
  | nil => simp [insertGroup, groupTotal, Group.cardinality]
  | cons group groups ih =>
      simp only [insertGroup]
      split
      next same => simp [groupTotal, Group.cardinality, List.length_cons, Nat.mul_add, same, Nat.add_assoc, Nat.add_comm]
      next different =>
        split
        · simp [groupTotal, Group.cardinality]
        · simp [groupTotal, ih, Nat.add_assoc, Nat.add_comm]

/-- Equal-weight grouping preserves every event's integer mass. -/
theorem insertGroup_event (event : α → Bool) (weight : Nat) (value : α) (groups : List (Group α)) :
    groupEvent event (insertGroup weight value groups) =
      (if event value then weight else 0) + groupEvent event groups := by
  induction groups with
  | nil => cases eventValue : event value <;> simp [insertGroup, groupEvent, eventValue]
  | cons group groups ih =>
      simp only [insertGroup]
      split
      next same =>
        cases eventValue : event value <;> simp [groupEvent, eventValue, Nat.mul_add, same, Nat.add_assoc, Nat.add_comm]
      next different =>
        split
        · cases eventValue : event value <;> simp [groupEvent, eventValue]
        · simp only [groupEvent, ih]
          omega

/-- The grouping fold preserves the total of its accumulator and all remaining weights. -/
theorem groupFold_total (weighted : List (Nat × α)) (groups : List (Group α)) :
    groupTotal (weighted.foldl (fun groups entry => insertGroup entry.1 entry.2 groups) groups) =
      ticketCount weighted + groupTotal groups := by
  induction weighted generalizing groups with
  | nil => simp [ticketCount]
  | cons entry weighted ih =>
      simp only [List.foldl_cons, ih, insertGroup_total, ticketCount]
      omega

/-- The grouping fold preserves each event's accumulated mass. -/
theorem groupFold_event (event : α → Bool) (weighted : List (Nat × α)) (groups : List (Group α)) :
    groupEvent event (weighted.foldl (fun groups entry => insertGroup entry.1 entry.2 groups) groups) =
      eventWeight event weighted + groupEvent event groups := by
  induction weighted generalizing groups with
  | nil => simp [eventWeight]
  | cons entry weighted ih =>
      simp only [List.foldl_cons, ih, insertGroup_event, eventWeight]
      omega

/-- Grouping preserves the total ticket count. -/
theorem groupWeighted_total (weighted : List (Nat × α)) : groupTotal (groupWeighted weighted) = ticketCount weighted := by
  simpa [groupWeighted, groupTotal] using groupFold_total weighted []

/-- Grouping preserves every event mass, including repeated equal payloads. -/
theorem groupWeighted_event (event : α → Bool) (weighted : List (Nat × α)) :
    groupEvent event (groupWeighted weighted) = eventWeight event weighted := by
  simpa [groupWeighted, groupEvent] using groupFold_event event weighted []

/-- Positive groups have positive widths and at least one payload. -/
def GroupsPositive (groups : List (Group α)) : Prop :=
  ∀ group ∈ groups, 0 < group.width ∧ group.values ≠ []

/-- Inserting a positive input weight preserves the group's required invariants. -/
theorem insertGroup_positive (weight : Nat) (value : α) (groups : List (Group α))
    (weightPositive : 0 < weight) (positive : GroupsPositive groups) :
    GroupsPositive (insertGroup weight value groups) := by
  induction groups with
  | nil =>
      intro group member
      have same : group = ⟨weight, [value]⟩ := by simpa [insertGroup] using member
      subst group
      exact ⟨weightPositive, by simp⟩
  | cons first groups ih =>
      have tailPositive : GroupsPositive groups := fun group member => positive group (by simp [member])
      simp only [insertGroup]
      split
      next same =>
        intro group member
        rcases List.mem_cons.mp member with equal | member
        · subst group; exact ⟨(positive first (by simp)).1, by simp⟩
        · exact tailPositive group member
      next different =>
        split
        · intro group member
          rcases List.mem_cons.mp member with equal | member
          · subst group; exact ⟨weightPositive, by simp⟩
          · exact positive group member
        · intro group member
          rcases List.mem_cons.mp member with equal | member
          · subst group; exact positive first (by simp)
          · exact ih tailPositive group member

/-- Positive input weights produce only valid equal-weight groups. -/
theorem groupWeighted_positive (weighted : List (Nat × α))
    (positive : ∀ entry ∈ weighted, 0 < entry.1) : GroupsPositive (groupWeighted weighted) := by
  have foldPositive (entries : List (Nat × α)) (groups : List (Group α))
      (positiveEntries : ∀ entry ∈ entries, 0 < entry.1) (positiveGroups : GroupsPositive groups) :
      GroupsPositive (entries.foldl (fun groups entry => insertGroup entry.1 entry.2 groups) groups) := by
    induction entries generalizing groups with
    | nil => exact positiveGroups
    | cons entry entries ih =>
        exact ih _ (fun other member => positiveEntries other (by simp [member]))
          (insertGroup_positive entry.1 entry.2 groups (positiveEntries entry (by simp)) positiveGroups)
  exact foldPositive weighted [] positive (by intro group member; simp at member)

/-- The start offset of a group is the total width of all preceding groups. -/
def lowerBound : List (Group α) → Nat → Nat
  | [], _ => 0
  | _ :: _, 0 => 0
  | group :: groups, index + 1 => group.cardinality + lowerBound groups index

/-- The first group starts at ticket zero. -/
theorem lowerBound_zero (groups : List (Group α)) : lowerBound groups 0 = 0 := by
  cases groups <;> rfl

/-- Group starts form a monotone cumulative-count sequence. -/
theorem lowerBound_mono (groups : List (Group α)) (left right : Nat) (order : left ≤ right) :
    lowerBound groups left ≤ lowerBound groups right := by
  induction groups generalizing left right with
  | nil => simp [lowerBound]
  | cons group groups ih =>
      cases left with
      | zero => simp [lowerBound]
      | succ left =>
          cases right with
          | zero => omega
          | succ right => exact Nat.add_le_add_left (ih left right (by omega)) _

/-- The offset after the last group equals the total ticket count. -/
theorem lowerBound_length (groups : List (Group α)) : lowerBound groups groups.length = groupTotal groups := by
  induction groups with
  | nil => rfl
  | cons group groups ih => simp [lowerBound, groupTotal, ih]

/-- Consecutive group starts differ by that group's derived ticket count. -/
theorem lowerBound_step (groups : List (Group α)) (index : Nat) (group : Group α)
    (found : groups[index]? = some group) :
    lowerBound groups (index + 1) = lowerBound groups index + group.cardinality := by
  induction groups generalizing index with
  | nil => simp at found
  | cons first groups ih =>
      cases index with
      | zero =>
          have same : first = group := by simpa using found
          subst first
          simp [lowerBound, lowerBound_zero]
      | succ index =>
          have tail : groups[index]? = some group := by simpa using found
          simp only [lowerBound, ih index tail, Nat.add_assoc]

/-- The source binary search uses the upper midpoint. -/
def upperMidpoint (low high : Nat) : Nat := low + (high - low + 1) / 2

/-- A nontrivial interval has an upper midpoint strictly above its lower end. -/
theorem upperMidpoint_bounds (low high : Nat) (strict : low < high) :
    low < upperMidpoint low high ∧ upperMidpoint low high ≤ high := by
  unfold upperMidpoint
  omega

/-- Find the last group start that does not exceed the ticket. -/
def ticketSearch (lower : Nat → Nat) (ticket low high : Nat) : Nat :=
  if high ≤ low then low
  else
    let middle := upperMidpoint low high
    if ticket < lower middle then ticketSearch lower ticket low (middle - 1)
    else ticketSearch lower ticket middle high
termination_by high - low
decreasing_by
  all_goals
    have _midpoint := upperMidpoint_bounds low high (by omega)
    omega

/-- Binary search returns the greatest start index below the ticket within the initial interval. -/
theorem ticketSearch_correct (lower : Nat → Nat) (ticket low high : Nat)
    (bounds : low ≤ high) (first : lower low ≤ ticket)
    (monotone : ∀ left right, left ≤ right → lower left ≤ lower right) :
    low ≤ ticketSearch lower ticket low high ∧ ticketSearch lower ticket low high ≤ high ∧
      lower (ticketSearch lower ticket low high) ≤ ticket ∧
      ∀ index, ticketSearch lower ticket low high < index → index ≤ high → ticket < lower index := by
  rw [ticketSearch]
  split
  next done => exact ⟨Nat.le_refl _, bounds, first, by intro index after within; omega⟩
  next more =>
    have midpoint := upperMidpoint_bounds low high (by omega)
    dsimp only
    split
    next before =>
      have ih := ticketSearch_correct lower ticket low (upperMidpoint low high - 1) (by omega) first monotone
      refine ⟨ih.1, by omega, ih.2.2.1, ?_⟩
      intro index after within
      by_cases earlier : index < upperMidpoint low high
      · exact ih.2.2.2 index after (by omega)
      · have bound := monotone (upperMidpoint low high) index (by omega)
        omega
    next after =>
      have ih := ticketSearch_correct lower ticket (upperMidpoint low high) high midpoint.2 (by omega) monotone
      exact ⟨by omega, ih.2.1, ih.2.2.1, ih.2.2.2⟩
termination_by high - low
decreasing_by
  all_goals
    have _midpoint := upperMidpoint_bounds low high (by omega)
    omega

/-- Expand one compiled group to its conceptual ticket sequence. -/
def blockTickets (group : Group α) : List α :=
  group.values.flatMap (fun value => List.replicate group.width value)

/-- Expand all compiled groups in their private ticket order. -/
def groupTickets (groups : List (Group α)) : List α := groups.flatMap blockTickets

/-- A compiled block has its declared number of tickets. -/
theorem blockTickets_length (group : Group α) : (blockTickets group).length = group.cardinality := by
  have length (values : List α) : (values.flatMap (fun value => List.replicate group.width value)).length =
      group.width * values.length := by
    induction values with
    | nil => simp
    | cons value values ih => simp [ih, Nat.mul_add, Nat.add_comm]
  exact length group.values

/-- The compiled group sequence has its derived total ticket count. -/
theorem groupTickets_length (groups : List (Group α)) : (groupTickets groups).length = groupTotal groups := by
  induction groups with
  | nil => rfl
  | cons group groups ih =>
      change (blockTickets group ++ groupTickets groups).length = group.cardinality + groupTotal groups
      rw [List.length_append, blockTickets_length, ih]

/-- A compiled block preserves each payload's declared ticket multiplicity. -/
theorem blockTickets_event (event : α → Bool) (group : Group α) :
    (blockTickets group).countP event = group.width * group.values.countP event := by
  have count (values : List α) : (values.flatMap (fun value => List.replicate group.width value)).countP event =
      group.width * values.countP event := by
    induction values with
    | nil => simp
    | cons value values ih =>
        simp only [List.flatMap_cons, List.countP_append, List.countP_cons, List.countP_replicate, ih]
        cases accepted : event value <;> simp [Nat.mul_add, Nat.add_comm]
  exact count group.values

/-- Grouped ticket expansion preserves the grouped event count. -/
theorem groupTickets_event (event : α → Bool) (groups : List (Group α)) :
    (groupTickets groups).countP event = groupEvent event groups := by
  induction groups with
  | nil => rfl
  | cons group groups ih =>
      change (blockTickets group ++ groupTickets groups).countP event =
        group.width * group.values.countP event + groupEvent event groups
      rw [List.countP_append, blockTickets_event, ih]

/-- Quotient decoding in an equal-width block agrees with conceptual ticket expansion. -/
theorem blockTickets_get (group : Group α) (ticket : Nat) (valid : ticket < group.cardinality) :
    (blockTickets group)[ticket]? = group.values[ticket / group.width]? := by
  have widthPositive : 0 < group.width := by
    unfold Group.cardinality at valid
    by_cases zero : group.width = 0
    · simp [zero] at valid
    · omega
  have expand : blockTickets group = Decoder.applyValues
      (group.values.map (fun value (_ : Unit) => value)) (List.replicate group.width ()) := by
    simp [blockTickets, Decoder.applyValues, List.flatMap_map]
  rw [expand, Decoder.get_applyValues]
  simp only [List.length_map, List.length_replicate]
  have fits : ticket < group.values.length * group.width := by
    simpa [Group.cardinality, Nat.mul_comm] using valid
  rw [ite_eq_left fits]
  simp only [List.getElem?_map, List.getElem?_replicate, ite_eq_left (Nat.mod_lt ticket widthPositive)]
  cases group.values[ticket / group.width]? <;> rfl

/-- A group's global interval replays through its local quotient decoder. -/
theorem groupTickets_get (groups : List (Group α)) (index : Nat) (group : Group α)
    (found : groups[index]? = some group) (ticket : Nat)
    (lower : lowerBound groups index ≤ ticket)
    (upper : ticket < lowerBound groups index + group.cardinality) :
    (groupTickets groups)[ticket]? = group.values[(ticket - lowerBound groups index) / group.width]? := by
  induction groups generalizing index ticket with
  | nil => simp at found
  | cons first groups ih =>
      cases index with
      | zero =>
          have same : first = group := by simpa using found
          subst first
          simp only [lowerBound, Nat.zero_add] at upper
          rw [groupTickets, List.flatMap_cons, List.getElem?_append_left (by simpa [blockTickets_length] using upper)]
          simpa [lowerBound] using blockTickets_get group ticket upper
      | succ index =>
          have tail : groups[index]? = some group := by simpa using found
          simp only [lowerBound] at lower upper ⊢
          have pastFirst : (blockTickets first).length ≤ ticket := by rw [blockTickets_length]; omega
          rw [groupTickets, List.flatMap_cons, List.getElem?_append_right pastFirst, blockTickets_length]
          have result := ih index tail (ticket - first.cardinality) (by omega) (by omega)
          simpa only [Nat.sub_sub, groupTickets] using result

/-- The searched group contains the ticket between its start and the next start. -/
theorem ticketSearch_interval (groups : List (Group α)) (ticket : Nat) (valid : ticket < groupTotal groups) :
    let index := ticketSearch (lowerBound groups) ticket 0 (groups.length - 1)
    index < groups.length ∧ lowerBound groups index ≤ ticket ∧ ticket < lowerBound groups (index + 1) := by
  have nonempty : 0 < groups.length := by
    cases groups with
    | nil => simp [groupTotal] at valid
    | cons group groups => simp
  have found := ticketSearch_correct (lowerBound groups) ticket 0 (groups.length - 1)
    (Nat.zero_le _) (by rw [lowerBound_zero]; omega) (lowerBound_mono groups)
  dsimp only
  refine ⟨by omega, found.2.2.1, ?_⟩
  by_cases last : ticketSearch (lowerBound groups) ticket 0 (groups.length - 1) = groups.length - 1
  · have next : ticketSearch (lowerBound groups) ticket 0 (groups.length - 1) + 1 = groups.length := by omega
    rw [next, lowerBound_length]
    exact valid
  · exact found.2.2.2 _ (by omega) (by omega)

/-- Decode a valid ticket with the source's binary group lookup and quotient payload lookup. -/
def binaryDecode (groups : List (Group α)) (ticket : Nat) : Option α :=
  if ticket < groupTotal groups then do
    let index := ticketSearch (lowerBound groups) ticket 0 (groups.length - 1)
    let group ← groups[index]?
    group.values[(ticket - lowerBound groups index) / group.width]?
  else none

/-- Binary compiled lookup is exactly the conceptual grouped-ticket decoder at every rank. -/
theorem binaryDecode_correct (groups : List (Group α)) (ticket : Nat) :
    binaryDecode groups ticket = (groupTickets groups)[ticket]? := by
  by_cases valid : ticket < groupTotal groups
  · have interval := ticketSearch_interval groups ticket valid
    dsimp only at interval
    let index := ticketSearch (lowerBound groups) ticket 0 (groups.length - 1)
    let group := groups[index]'interval.1
    have found : groups[index]? = some group := List.getElem?_eq_getElem interval.1
    have step := lowerBound_step groups index group found
    have replay := groupTickets_get groups index group found ticket interval.2.1 (by rw [← step]; exact interval.2.2)
    simp only [binaryDecode, ite_eq_left valid]
    change (groups[index]?).bind _ = _
    rw [found]
    exact replay.symm
  · rw [binaryDecode, ite_eq_right valid]
    exact (List.getElem?_eq_none_iff.mpr (by rw [groupTickets_length]; omega)).symm

/-- Uniform sampling of the compiled groups has the original declared event probability. -/
theorem grouped_ticket_probability (weighted : List (Nat × α)) (event : α → Bool) :
    eventMass event (normalize (counting (groupTickets (groupWeighted weighted)))) = ticketProbability event weighted := by
  rw [uniform_event_probability, groupTickets_length, groupTickets_event,
    groupWeighted_total, groupWeighted_event, ticketProbability_eq]

/-- Enumerating all valid list indexes recovers the list, with optional lookup results. -/
theorem map_range_get (values : List α) :
    (List.range values.length).map (fun rank => values[rank]?) = values.map some := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Function.comp_def, ih]

/-- Mapping values commutes with normalization. -/
theorem map_normalize (transform : α → β) (outcomes : Distribution α) :
    Probability.map transform (normalize outcomes) = normalize (Probability.map transform outcomes) := by
  rw [normalize, normalize, total_map]
  simp [Probability.map, scale, List.map_map, Function.comp_def]

/-- Mapping the unit-weight counting distribution maps its value list. -/
theorem map_counting (transform : α → β) (values : List α) :
    Probability.map transform (counting values) = counting (values.map transform) := by
  simp [Probability.map, counting, List.map_map, Function.comp_def]

/-- The default compiled sampler draws one uniform ticket and applies binary decoding. -/
def binarySampling (groups : List (Group α)) : Distribution (Option α) :=
  Probability.map (binaryDecode groups) (normalize (counting (List.range (groupTotal groups))))

/-- The binary implementation has exactly the distribution of the expanded ticket table. -/
theorem binarySampling_correct (groups : List (Group α)) :
    binarySampling groups = Probability.map some (normalize (counting (groupTickets groups))) := by
  rw [binarySampling, map_normalize, map_counting, map_normalize, map_counting]
  have lookups : (List.range (groupTotal groups)).map (binaryDecode groups) = (groupTickets groups).map some := by
    have decoder : binaryDecode groups = fun rank => (groupTickets groups)[rank]? := by
      funext rank
      exact binaryDecode_correct groups rank
    rw [decoder, ← groupTickets_length]
    exact map_range_get (groupTickets groups)
  rw [lookups]

/-- Default ticket sampling and the exact weighted backend agree on every value event. -/
theorem binarySampling_event (weighted : List (Nat × α)) (event : α → Bool) :
    eventMass (fun result => result.any event) (binarySampling (groupWeighted weighted)) =
      ticketProbability event weighted := by
  rw [binarySampling_correct, eventMass_map]
  exact grouped_ticket_probability weighted event

/-- Compiling converted rational masses preserves their exact event probabilities. -/
theorem compiled_rational_probability (outcomes : Distribution α) (nonempty : outcomes ≠ [])
    (positive : ∀ entry ∈ outcomes, 0 < entry.1) (event : α → Bool) :
    eventMass (fun result => result.any event) (binarySampling (groupWeighted (integerMasses outcomes))) =
      eventMass event (normalize outcomes) := by
  rw [binarySampling_event, integerMasses_event_probability outcomes nonempty positive event]

/-- A compiled finite table retains its checked bound and its grouped payloads. -/
structure Compiled (α : Type) where
  bound : Nat
  groups : List (Group α)
  deriving Repr

/-- Compile only a positive ticket count within the machine-bound precondition. -/
def compileWeighted (maximum : Nat) (weighted : List (Nat × α)) : Option (Compiled α) :=
  let total := ticketCount weighted
  if 0 < total ∧ total ≤ maximum then some ⟨total, groupWeighted weighted⟩ else none

/-- Compiled metadata is derived from the input weights and satisfies the source's guards. -/
theorem compileWeighted_correct (maximum : Nat) (weighted : List (Nat × α)) (compiled : Compiled α)
    (found : compileWeighted maximum weighted = some compiled) :
    compiled.bound = ticketCount weighted ∧ compiled.groups = groupWeighted weighted ∧
      0 < compiled.bound ∧ compiled.bound ≤ maximum ∧ groupTotal compiled.groups = compiled.bound := by
  unfold compileWeighted at found
  dsimp only at found
  split at found
  next within =>
    have same := Option.some.inj found
    subst compiled
    exact ⟨rfl, rfl, within.1, within.2, groupWeighted_total weighted⟩
  next invalid => cases found

/-- Any valid backend ticket is decoded successfully by the compiled table. -/
theorem compiledDecode_exists (maximum : Nat) (weighted : List (Nat × α)) (compiled : Compiled α)
    (found : compileWeighted maximum weighted = some compiled) (ticket : Nat) (valid : ticket < compiled.bound) :
    ∃ value, binaryDecode compiled.groups ticket = some value := by
  have correct := compileWeighted_correct maximum weighted compiled found
  have length : ticket < (groupTickets compiled.groups).length := by
    rw [groupTickets_length, correct.2.2.2.2]
    exact valid
  exact ⟨(groupTickets compiled.groups)[ticket], by rw [binaryDecode_correct, List.getElem?_eq_getElem length]⟩

/-- Positive groups have at least one ticket per group and per payload. -/
theorem positive_group_bounds (groups : List (Group α)) (positive : GroupsPositive groups) :
    groups.length ≤ groupTotal groups ∧
      ∀ group ∈ groups, 0 < group.cardinality ∧ group.values.length ≤ group.cardinality := by
  have memberBounds (group : Group α) (member : group ∈ groups) :
      0 < group.cardinality ∧ group.values.length ≤ group.cardinality := by
    have widthPositive := (positive group member).1
    have lengthPositive := List.length_pos_iff.mpr (positive group member).2
    exact ⟨Nat.mul_pos widthPositive lengthPositive,
      by simpa [Group.cardinality] using Nat.mul_le_mul_right group.values.length widthPositive⟩
  refine ⟨?_, memberBounds⟩
  induction groups with
  | nil => exact Nat.le_refl _
  | cons group groups ih =>
      have first := (memberBounds group (by simp)).1
      have rest := ih (fun other member => positive other (by simp [member]))
        (fun other member => memberBounds other (by simp [member]))
      change groups.length + 1 ≤ group.cardinality + groupTotal groups
      omega

/-- Every cumulative group start is at most the complete ticket count. -/
theorem lowerBound_le_total (groups : List (Group α)) (index : Nat) : lowerBound groups index ≤ groupTotal groups := by
  induction groups generalizing index with
  | nil => exact Nat.le_refl _
  | cons group groups ih =>
      cases index with
      | zero => exact Nat.zero_le _
      | succ index => exact Nat.add_le_add_left (ih index) _

/-- All compiled interval arithmetic stays inside the checked machine bound. -/
theorem compiled_interval_bounds (maximum : Nat) (weighted : List (Nat × α)) (compiled : Compiled α)
    (found : compileWeighted maximum weighted = some compiled)
    (positive : ∀ entry ∈ weighted, 0 < entry.1) (index : Nat) (group : Group α)
    (groupFound : compiled.groups[index]? = some group) :
    0 < group.width ∧ group.values.length ≤ maximum ∧
      lowerBound compiled.groups index + group.width * group.values.length ≤ maximum ∧
      compiled.groups.length ≤ maximum := by
  have correct := compileWeighted_correct maximum weighted compiled found
  have groupsPositive : GroupsPositive compiled.groups := by
    rw [correct.2.1]
    exact groupWeighted_positive weighted positive
  have member := List.mem_of_getElem? groupFound
  have bounds := positive_group_bounds compiled.groups groupsPositive
  have step := lowerBound_step compiled.groups index group groupFound
  have next := lowerBound_le_total compiled.groups (index + 1)
  refine ⟨(groupsPositive group member).1, ?_, ?_, ?_⟩
  · have payload := (bounds.2 group member).2
    unfold Group.cardinality at payload step
    omega
  · unfold Group.cardinality at step
    omega
  · omega

/-- Narrowing a checked nonnegative rank into a signed machine range preserves it. -/
theorem checked_machine_rank (maximum bound rank : Nat) (fits : bound ≤ maximum) (valid : rank < bound) :
    rank % (2 * (maximum + 1)) = rank ∧ (rank : Int) < (maximum + 1 : Nat) := by
  exact ⟨Nat.mod_eq_of_lt (by omega), by omega⟩

/-- The exact interpretations of the value-only and ranked sampler fields. -/
structure ExactSampler (α : Type) where
  values : Distribution α
  ranked : Distribution (Nat × α)

/-- Discarding sampled ranks gives the same value distribution as the value-only field. -/
def Coherent (sampler : ExactSampler α) : Prop :=
  Probability.map Prod.snd sampler.ranked = sampler.values

/-- Uniform exact rank selection over the backend's half-open interval. -/
def uniformRanks (bound : Nat) : Distribution Nat := normalize (counting (List.range bound))

/-- The uniform constructor uses the same rank selector for both sampler fields. -/
def uniformSampler (bound : Nat) (valueAt : Nat → α) : ExactSampler α :=
  ⟨Probability.map valueAt (uniformRanks bound),
    Probability.map (fun rank => (rank, valueAt rank)) (uniformRanks bound)⟩

/-- Mapping a sampler preserves every sampled structural rank. -/
def mapSampler (transform : α → β) (sampler : ExactSampler α) : ExactSampler β :=
  ⟨Probability.map transform sampler.values,
    Probability.map (fun entry => (entry.1, transform entry.2)) sampler.ranked⟩

/-- Applicative sampling combines independent values and their mixed-radix ranks. -/
def productSampler (rightCount : Nat) (functions : ExactSampler (α → β)) (arguments : ExactSampler α) :
    ExactSampler β :=
  ⟨Probability.map (fun entry => entry.1 entry.2) (product functions.values arguments.values),
    Probability.map (fun entry =>
      (pairRank rightCount entry.1.1 entry.2.1, entry.1.2 entry.2.2))
      (product functions.ranked arguments.ranked)⟩

/-- Mapping exact distributions composes its value functions. -/
theorem map_map (first : α → β) (second : β → γ) (outcomes : Distribution α) :
    Probability.map second (Probability.map first outcomes) = Probability.map (second ∘ first) outcomes := by
  simp [Probability.map, List.map_map, Function.comp_def]

/-- Mapping both components commutes with independent sampling. -/
theorem map_product (leftMap : α → β) (rightMap : γ → δ)
    (left : Distribution α) (right : Distribution γ) :
    Probability.map (fun entry => (leftMap entry.1, rightMap entry.2)) (product left right) =
      product (Probability.map leftMap left) (Probability.map rightMap right) := by
  simp [Probability.map, product, List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def]

/-- The uniform constructor's ranked and unranked fields agree. -/
theorem uniformSampler_coherent (bound : Nat) (valueAt : Nat → α) : Coherent (uniformSampler bound valueAt) := by
  simp [Coherent, uniformSampler, map_map, Function.comp_def]

/-- Mapping preserves agreement between the sampler's two fields. -/
theorem mapSampler_coherent (transform : α → β) (sampler : ExactSampler α) (coherent : Coherent sampler) :
    Coherent (mapSampler transform sampler) := by
  unfold Coherent mapSampler
  rw [map_map]
  have same := congrArg (Probability.map transform) coherent
  rw [map_map] at same
  exact same

/-- Product construction preserves agreement between the sampler's two fields. -/
theorem productSampler_coherent (rightCount : Nat) (functions : ExactSampler (α → β))
    (arguments : ExactSampler α) (functionsCoherent : Coherent functions) (argumentsCoherent : Coherent arguments) :
    Coherent (productSampler rightCount functions arguments) := by
  unfold Coherent productSampler
  rw [map_map]
  have regroup :
      Probability.map (fun entry : (Nat × (α → β)) × (Nat × α) => entry.1.2 entry.2.2)
        (product functions.ranked arguments.ranked) =
      Probability.map (fun entry : (α → β) × α => entry.1 entry.2)
        (Probability.map (fun entry : (Nat × (α → β)) × (Nat × α) => (entry.1.2, entry.2.2))
          (product functions.ranked arguments.ranked)) := by rw [map_map]; rfl
  change Probability.map (fun entry : (Nat × (α → β)) × (Nat × α) => entry.1.2 entry.2.2) _ = _
  rw [regroup, map_product Prod.snd Prod.snd, functionsCoherent, argumentsCoherent]

/-- Mapping a probability distribution preserves nonnegativity and total mass. -/
theorem map_probability (transform : α → β) (outcomes : Distribution α) (probability : IsProbability outcomes) :
    IsProbability (Probability.map transform outcomes) := by
  refine ⟨?_, by rw [total_map]; exact probability.2⟩
  intro entry member
  change entry ∈ outcomes.map (fun original => (original.1, transform original.2)) at member
  obtain ⟨original, belongs, same⟩ := List.mem_map.mp member
  subst entry
  exact probability.1 original belongs

/-- A positive uniform cardinality produces normalized distributions in both sampler fields. -/
theorem uniformSampler_probability (bound : Nat) (valueAt : Nat → α) (positive : 0 < bound) :
    IsProbability (uniformSampler bound valueAt).values ∧ IsProbability (uniformSampler bound valueAt).ranked := by
  have probability : IsProbability (uniformRanks bound) := uniform_probability _ (by simpa using positive)
  exact ⟨map_probability valueAt (uniformRanks bound) probability,
    map_probability (fun rank => (rank, valueAt rank)) (uniformRanks bound) probability⟩

/-- Product constructors multiply independent probabilities and remain normalized. -/
theorem productSampler_probability (rightCount : Nat) (functions : ExactSampler (α → β))
    (arguments : ExactSampler α)
    (left : IsProbability functions.values ∧ IsProbability functions.ranked)
    (right : IsProbability arguments.values ∧ IsProbability arguments.ranked) :
    IsProbability (productSampler rightCount functions arguments).values ∧
      IsProbability (productSampler rightCount functions arguments).ranked :=
  ⟨map_probability (fun entry : (α → β) × α => entry.1 entry.2) _
      (product_probability _ _ left.1 right.1),
    map_probability (fun entry : (Nat × (α → β)) × (Nat × α) =>
      (pairRank rightCount entry.1.1 entry.2.1, entry.1.2 entry.2.2)) _
      (product_probability _ _ left.2 right.2)⟩

/-- The cardinality-one shortcut is exactly deterministic sampling at rank zero. -/
theorem uniformSampler_one (valueAt : Nat → α) :
    (uniformSampler 1 valueAt).values = [(1, valueAt 0)] ∧
      (uniformSampler 1 valueAt).ranked = [(1, (0, valueAt 0))] := by
  have oneInverse : (1 : Rat)⁻¹ = 1 := by
    simpa only [Rat.mul_one] using (Rat.inv_mul_cancel (1 : Rat) (by decide))
  simp [uniformSampler, uniformRanks, normalize, counting, total, scale, Probability.map, Rat.add_zero, oneInverse]

/-- Exact rejection sampling returns no outcomes when the accepted mass is not positive. -/
def exactFilter (predicate : α → Bool) (outcomes : Distribution α) : Distribution α :=
  if 0 < eventMass predicate outcomes then condition predicate outcomes else []

/-- Positive-mass rejection sampling has the conditional event probability. -/
theorem exactFilter_event (predicate event : α → Bool) (outcomes : Distribution α)
    (positive : 0 < eventMass predicate outcomes) :
    eventMass event (exactFilter predicate outcomes) =
      eventMass (fun value => predicate value && event value) outcomes / eventMass predicate outcomes := by
  rw [exactFilter, ite_eq_left positive, eventMass_condition]

/-- Conditioning nonnegative input on positive accepted mass returns a probability. -/
theorem exactFilter_probability (predicate : α → Bool) (outcomes : Distribution α)
    (nonnegative : Nonnegative outcomes) (positive : 0 < eventMass predicate outcomes) :
    IsProbability (exactFilter predicate outcomes) := by
  rw [exactFilter, ite_eq_left positive]
  exact condition_probability predicate outcomes nonnegative positive

/-- A rejected exact distribution is empty, as in the source's nonpositive-mass branch. -/
theorem exactFilter_empty (predicate : α → Bool) (outcomes : Distribution α)
    (empty : eventMass predicate outcomes ≤ 0) : exactFilter predicate outcomes = [] := by
  simp [exactFilter, Rat.not_lt.mpr empty]

/-- A backend interpretation must agree on events; the typeclass signatures alone do not imply these laws. -/
structure BackendLaws
    (selectInteger selectInt : Nat → Distribution Nat)
    (filterGen : (α → Bool) → Distribution α → Distribution α) : Prop where
  integer_uniform : ∀ bound, 0 < bound → selectInteger bound = uniformRanks bound
  int_uniform : ∀ bound, 0 < bound → selectInt bound = uniformRanks bound
  filter_exact : ∀ predicate outcomes, filterGen predicate outcomes = exactFilter predicate outcomes

/-- Lawful machine-rank and arbitrary-precision selectors agree after the same bound check. -/
theorem machine_big_agree (selectInteger selectInt : Nat → Distribution Nat)
    (filterGen : (α → Bool) → Distribution α → Distribution α)
    (lawful : BackendLaws selectInteger selectInt filterGen) (bound : Nat) (positive : 0 < bound) :
    selectInt bound = selectInteger bound := by
  rw [lawful.int_uniform bound positive, lawful.integer_uniform bound positive]

/-- Value mapping commutes with multiplication of all outcome masses. -/
theorem map_scale (transform : α → β) (factor : Rat) (outcomes : Distribution α) :
    Probability.map transform (scale factor outcomes) = scale factor (Probability.map transform outcomes) := by
  simp [Probability.map, scale, List.map_map, Function.comp_def]

/-- Mapping all branches commutes with their unnormalized mixture. -/
theorem map_mix (transform : α → β) (branches : List (Rat × Distribution α)) :
    Probability.map transform (mix branches) =
      mix (branches.map (fun entry => (entry.1, Probability.map transform entry.2))) := by
  induction branches with
  | nil => rfl
  | cons entry branches ih =>
      rcases entry with ⟨weight, outcomes⟩
      change Probability.map transform (scale weight outcomes ++ mix branches) =
        scale weight (Probability.map transform outcomes) ++ _
      rw [show Probability.map transform (scale weight outcomes ++ mix branches) =
        Probability.map transform (scale weight outcomes) ++ Probability.map transform (mix branches) by
          simp [Probability.map]]
      rw [map_scale, ih]

/-- Mapping callback values leaves the branch-weight total unchanged. -/
theorem branchWeight_map (transform : α → β) (branches : List (Rat × Distribution α)) :
    branchWeight (branches.map (fun entry => (entry.1, Probability.map transform entry.2))) = branchWeight branches := by
  induction branches with
  | nil => rfl
  | cons entry branches ih => simp [branchWeight, ih]

/-- Value mapping commutes with exact weighted backend choice. -/
theorem map_frequency (transform : α → β) (branches : List (Rat × Distribution α)) :
    Probability.map transform (frequency branches) =
      frequency (branches.map (fun entry => (entry.1, Probability.map transform entry.2))) := by
  rw [frequency, map_scale, map_mix, frequency, branchWeight_map]

/-- Scaling outer branch weights scales the unnormalized mixture once. -/
theorem mix_scale_outer (factor : Rat) (branches : List (Rat × Distribution α)) :
    mix (scale factor branches) = scale factor (mix branches) := by
  induction branches with
  | nil => rfl
  | cons entry branches ih =>
      rcases entry with ⟨weight, outcomes⟩
      change scale (factor * weight) outcomes ++ mix (scale factor branches) =
        scale factor (scale weight outcomes ++ mix branches)
      rw [SizeMass.scale_append, scale_scale, ih]

/-- Frequency is the mixture of normalized branch weights. -/
theorem frequency_eq_mix_normalize (branches : List (Rat × Distribution α)) :
    frequency branches = mix (normalize branches) := by
  have weights : total branches = branchWeight branches := by
    induction branches with
    | nil => rfl
    | cons entry branches ih => simp [total, branchWeight, ih]
  rw [normalize, mix_scale_outer, weights]
  rfl

/-- Integer mass compilation preserves complete weighted callback distributions. -/
theorem integerMasses_frequency (branches : List (Rat × Distribution α)) (nonempty : branches ≠ [])
    (positive : ∀ entry ∈ branches, 0 < entry.1) :
    frequency (weightDistribution (integerMasses branches)) = frequency branches := by
  rw [frequency_eq_mix_normalize, integerMasses_normalize branches nonempty positive,
    ← frequency_eq_mix_normalize]

/-- A single positive-weight alternative needs no backend draw. -/
theorem frequency_singleton (weight : Rat) (outcomes : Distribution α) (positive : 0 < weight) :
    frequency [(weight, outcomes)] = outcomes := by
  simp only [frequency, branchWeight, mix, List.append_nil, Rat.add_zero]
  rw [scale_scale, Rat.inv_mul_cancel _ (Rat.ne_of_gt positive), scale_one]

/-- One choice alternative keeps its structural count separate from its sampling mass. -/
structure Alternative (α : Type) where
  count : Nat
  mass : Rat
  sampling : ExactSampler α

/-- A live alternative carries its structural rank offset. -/
structure ChoicePart (α : Type) where
  mass : Rat
  offset : Nat
  sampling : ExactSampler α

/-- The complete structural count includes alternatives skipped by sampling. -/
def alternativeCount : List (Alternative α) → Nat
  | [] => 0
  | alternative :: rest => alternative.count + alternativeCount rest

/-- Keep positive-mass alternatives, advancing offsets even for omitted alternatives. -/
def choiceParts (offset : Nat) : List (Alternative α) → List (ChoicePart α)
  | [] => []
  | alternative :: rest =>
      let later := choiceParts (offset + alternative.count) rest
      if 0 < alternative.count ∧ 0 < alternative.mass then
        ⟨alternative.mass, offset, alternative.sampling⟩ :: later
      else later

/-- Each live part comes from an input alternative and occupies its original structural interval. -/
theorem choiceParts_origin (alternatives : List (Alternative α)) (offset : Nat) (part : ChoicePart α)
    (member : part ∈ choiceParts offset alternatives) :
    ∃ alternative, alternative ∈ alternatives ∧ part.mass = alternative.mass ∧
      part.sampling = alternative.sampling ∧ 0 < alternative.count ∧ 0 < part.mass ∧
      offset ≤ part.offset ∧ part.offset + alternative.count ≤ offset + alternativeCount alternatives := by
  induction alternatives generalizing offset with
  | nil => simp [choiceParts] at member
  | cons alternative alternatives ih =>
      simp only [choiceParts] at member
      split at member
      next live =>
        rcases List.mem_cons.mp member with same | member
        · subst part
          exact ⟨alternative, by simp, rfl, rfl, live.1, live.2, Nat.le_refl _, by simp [alternativeCount]⟩
        · obtain ⟨original, belongs, mass, sampling, countPositive, massPositive, lower, upper⟩ :=
            ih (offset + alternative.count) member
          exact ⟨original, by simp [belongs], mass, sampling, countPositive, massPositive,
            by omega, by simp only [alternativeCount]; omega⟩
      next skipped =>
        obtain ⟨original, belongs, mass, sampling, countPositive, massPositive, lower, upper⟩ :=
          ih (offset + alternative.count) member
        exact ⟨original, by simp [belongs], mass, sampling, countPositive, massPositive,
          by omega, by simp only [alternativeCount]; omega⟩

/-- Run a weighted choice, offsetting only the ranked sampler field. -/
def chooseSampler (parts : List (ChoicePart α)) : ExactSampler α :=
  ⟨frequency (parts.map (fun part => (part.mass, part.sampling.values))),
    frequency (parts.map (fun part => (part.mass,
      Probability.map (fun entry => (part.offset + entry.1, entry.2)) part.sampling.ranked)))⟩

/-- Weighted choice preserves agreement between the sampler's value and rank fields. -/
theorem chooseSampler_coherent (parts : List (ChoicePart α))
    (coherent : ∀ part ∈ parts, Coherent part.sampling) : Coherent (chooseSampler parts) := by
  unfold Coherent chooseSampler
  rw [map_frequency]
  apply congrArg frequency
  simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro part member
  have agreed := coherent part member
  rw [map_map]
  exact congrArg (fun outcomes => (part.mass, outcomes)) agreed

/-- The source choice worker preserves value/rank coherence while retaining skipped structural offsets. -/
theorem choiceParts_coherent (alternatives : List (Alternative α))
    (coherent : ∀ alternative ∈ alternatives, Coherent alternative.sampling) :
    Coherent (chooseSampler (choiceParts 0 alternatives)) := by
  apply chooseSampler_coherent
  intro part member
  obtain ⟨alternative, belongs, _, same, _⟩ := choiceParts_origin alternatives 0 part member
  rw [same]
  exact coherent alternative belongs

/-- Positive nonempty branch weights have a positive total. -/
theorem positive_branchWeight (branches : List (Rat × Distribution α)) (nonempty : branches ≠ [])
    (positive : ∀ branch ∈ branches, 0 < branch.1) : 0 < branchWeight branches := by
  have same : branchWeight branches = total branches := by
    clear nonempty positive
    induction branches with
    | nil => rfl
    | cons branch branches ih => simp [branchWeight, total, ih]
  rw [same]
  exact Sized.total_positive branches nonempty positive

/-- Derived live parts and probability callbacks give normalized exact weighted choices. -/
theorem chooseSampler_probability (parts : List (ChoicePart α)) (nonempty : parts ≠ [])
    (positive : ∀ part ∈ parts, 0 < part.mass)
    (probability : ∀ part ∈ parts, IsProbability part.sampling.values ∧ IsProbability part.sampling.ranked) :
    IsProbability (chooseSampler parts).values ∧ IsProbability (chooseSampler parts).ranked := by
  constructor
  · apply frequency_probability
    · intro branch member
      obtain ⟨part, belongs, same⟩ := List.mem_map.mp member
      subst branch
      exact ⟨Rat.le_of_lt (positive part belongs), (probability part belongs).1⟩
    · apply positive_branchWeight
      · simpa using nonempty
      · intro branch member
        obtain ⟨part, belongs, same⟩ := List.mem_map.mp member
        subst branch
        exact positive part belongs
  · apply frequency_probability
    · intro branch member
      obtain ⟨part, belongs, same⟩ := List.mem_map.mp member
      subst branch
      exact ⟨Rat.le_of_lt (positive part belongs), map_probability (fun entry : Nat × α => (part.offset + entry.1, entry.2)) _ (probability part belongs).2⟩
    · apply positive_branchWeight
      · simpa using nonempty
      · intro branch member
        obtain ⟨part, belongs, same⟩ := List.mem_map.mp member
        subst branch
        exact positive part belongs

/-- The exact backend lists one weighted outcome per payload, without expanding tickets. -/
def exactSelectWeighted (weighted : List (Nat × α)) : Distribution α :=
  weighted.map (fun entry => ((entry.1 : Rat) / (ticketCount weighted : Rat), entry.2))

/-- Exact weighted selection is normalization of the declared integer masses. -/
theorem exactSelectWeighted_correct (weighted : List (Nat × α)) :
    exactSelectWeighted weighted = normalize (weightDistribution weighted) := by
  rw [normalize, weightDistribution_total]
  simp only [exactSelectWeighted, weightDistribution, scale, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro entry _
  congr 1
  simp only [Rat.div_def]
  ac_rfl

/-- Exact and default compiled backends agree on all observable value events. -/
theorem compiled_exact_backend_agree (weighted : List (Nat × α)) (event : α → Bool) :
    eventMass (fun result => result.any event) (binarySampling (groupWeighted weighted)) =
      eventMass event (exactSelectWeighted weighted) := by
  rw [binarySampling_event, exactSelectWeighted_correct, normalize, eventMass_scale,
    weightDistribution_total, weightDistribution_event, ticketProbability_eq]
  simp only [Rat.div_def]
  ac_rfl

/-- The weighted backend shortcut rejects an empty alternative list explicitly. -/
def chooseWeighted : List (Rat × Distribution α) → Option (Distribution α)
  | [] => none
  | [(_, outcomes)] => some outcomes
  | alternatives => some (frequency alternatives)

/-- The singleton shortcut and ordinary backend frequency have identical positive-weight semantics. -/
theorem chooseWeighted_correct (branches : List (Rat × Distribution α)) (nonempty : branches ≠ [])
    (positive : ∀ entry ∈ branches, 0 < entry.1) :
    chooseWeighted branches = some (frequency branches) := by
  cases branches with
  | nil => contradiction
  | cons branch branches =>
      cases branches with
      | nil =>
          rw [chooseWeighted, frequency_singleton branch.1 branch.2 (positive branch (by simp))]
      | cons other rest => rfl

/-- Remove nonpositive rational alternatives before exact integer compilation. -/
def liveMasses (branches : List (Rat × Distribution α)) : List (Rat × Distribution α) :=
  branches.filter (fun entry => decide (0 < entry.1))

/-- Compile rational branch masses and use the same singleton-aware backend chooser. -/
def chooseMassWeighted (branches : List (Rat × Distribution α)) : Option (Distribution α) :=
  chooseWeighted (weightDistribution (integerMasses (liveMasses branches)))

/-- The concrete mass chooser preserves the exact mixture of all positive alternatives. -/
theorem chooseMassWeighted_correct (branches : List (Rat × Distribution α))
    (nonempty : liveMasses branches ≠ []) :
    chooseMassWeighted branches = some (frequency (liveMasses branches)) := by
  have positive : ∀ entry ∈ liveMasses branches, 0 < entry.1 := by
    intro entry member
    exact of_decide_eq_true (List.mem_filter.mp member).2
  have compiledPositive := integerMasses_positive (liveMasses branches) nonempty positive
  have nonemptyCompiled : weightDistribution (integerMasses (liveMasses branches)) ≠ [] := by
    simpa [weightDistribution, integerMasses] using nonempty
  have positiveCompiled : ∀ entry ∈ weightDistribution (integerMasses (liveMasses branches)), 0 < entry.1 := by
    intro entry member
    obtain ⟨original, belongs, same⟩ := List.mem_map.mp member
    subst entry
    exact Rat.natCast_pos.mpr (compiledPositive original belongs)
  rw [chooseMassWeighted, chooseWeighted_correct _ nonemptyCompiled positiveCompiled,
    integerMasses_frequency (liveMasses branches) nonempty positive]

/-- A mass chooser with no positive alternatives reaches the source's explicit error case. -/
theorem chooseMassWeighted_empty (branches : List (Rat × Distribution α))
    (empty : liveMasses branches = []) : chooseMassWeighted branches = none := by
  simp [chooseMassWeighted, empty, integerMasses, weightDistribution, chooseWeighted]

/-- One live product-size split stores its count, rank offset, sizes, and right radix. -/
structure ProductPart where
  block : Nat
  offset : Nat
  functionSize : Nat
  argumentSize : Nat
  argumentCount : Nat
  deriving Repr

/-- Compute product parts, omitting zero blocks and retaining cumulative structural offsets. -/
def productSampleParts (argumentCounts : Nat → Nat) (size offset : Nat) :
    List (Nat × Nat) → List ProductPart
  | [] => []
  | (functionSize, functionCount) :: rest =>
      let argumentSize := size - functionSize
      let argumentCount := argumentCounts argumentSize
      let block := functionCount * argumentCount
      if block = 0 then productSampleParts argumentCounts size offset rest
      else ⟨block, offset, functionSize, argumentSize, argumentCount⟩ ::
        productSampleParts argumentCounts size (offset + block) rest

/-- Count all product tickets from the supplied finite split prefix. -/
def splitTotal (argumentCounts : Nat → Nat) (size : Nat) (functions : List (Nat × Nat)) : Nat :=
  (functions.map (fun entry => entry.2 * argumentCounts (size - entry.1))).sum

/-- Every product part has a positive derived block and its original interval within the class. -/
theorem productSampleParts_correct (argumentCounts : Nat → Nat) (size offset : Nat)
    (functions : List (Nat × Nat)) (part : ProductPart)
    (member : part ∈ productSampleParts argumentCounts size offset functions) :
    ∃ functionCount, (part.functionSize, functionCount) ∈ functions ∧
      part.argumentSize = size - part.functionSize ∧ part.argumentCount = argumentCounts part.argumentSize ∧
      part.block = functionCount * part.argumentCount ∧ 0 < part.block ∧
      offset ≤ part.offset ∧ part.offset + part.block ≤ offset + splitTotal argumentCounts size functions := by
  induction functions generalizing offset with
  | nil => simp [productSampleParts] at member
  | cons entry functions ih =>
      rcases entry with ⟨functionSize, functionCount⟩
      simp only [productSampleParts] at member
      split at member
      next empty =>
        obtain ⟨count, belongs, argumentSize, argumentCount, block, positive, lower, upper⟩ := ih offset member
        refine ⟨count, by simp [belongs], argumentSize, argumentCount, block, positive, lower, ?_⟩
        simpa [splitTotal, empty] using upper
      next live =>
        rcases List.mem_cons.mp member with same | member
        · subst part
          refine ⟨functionCount, by simp, rfl, rfl, rfl, by dsimp only; omega, Nat.le_refl _, ?_⟩
          simp [splitTotal]
        · obtain ⟨count, belongs, argumentSize, argumentCount, block, positive, lower, upper⟩ :=
            ih (offset + functionCount * argumentCounts (size - functionSize)) member
          refine ⟨count, by simp [belongs], argumentSize, argumentCount, block, positive, by omega, ?_⟩
          simp only [splitTotal, List.map_cons, List.sum_cons] at upper ⊢
          omega

/-- A recursive size sampler is observed one exact size at a time. -/
abbrev SampleIndex (α : Type) := Nat → ExactSampler α

/-- The product index chooses among derived size splits and delegates to the two side samplers. -/
def productSampleIndexBy (weightOf : ProductPart → Rat) (functionCounts : List (Nat × Nat))
    (argumentCounts : Nat → Nat) (functions : SampleIndex (α → β)) (arguments : SampleIndex α)
    (size : Nat) : ExactSampler β :=
  chooseSampler ((productSampleParts argumentCounts size 0 functionCounts).map (fun part =>
    ⟨weightOf part, part.offset, productSampler part.argumentCount
      (functions part.functionSize) (arguments part.argumentSize)⟩))

/-- Count-weighted products use each derived block's structural cardinality. -/
def productSampleIndex (functionCounts : List (Nat × Nat)) (argumentCounts : Nat → Nat)
    (functions : SampleIndex (α → β)) (arguments : SampleIndex α) (size : Nat) : ExactSampler β :=
  productSampleIndexBy (fun part => part.block) functionCounts argumentCounts functions arguments size

/-- Mass-weighted products choose a split by the product of its retained side masses. -/
def productMassSampleIndex (functionCounts : List (Nat × Nat)) (argumentCounts : Nat → Nat)
    (functionMass argumentMass : Nat → Rat) (functions : SampleIndex (α → β)) (arguments : SampleIndex α)
    (size : Nat) : ExactSampler β :=
  productSampleIndexBy (fun part => functionMass part.functionSize * argumentMass part.argumentSize)
    functionCounts argumentCounts functions arguments size

/-- Product size sampling preserves the value/rank agreement of its child samplers. -/
theorem productSampleIndexBy_coherent (weightOf : ProductPart → Rat) (functionCounts : List (Nat × Nat))
    (argumentCounts : Nat → Nat) (functions : SampleIndex (α → β)) (arguments : SampleIndex α) (size : Nat)
    (functionCoherent : ∀ size, Coherent (functions size)) (argumentCoherent : ∀ size, Coherent (arguments size)) :
    Coherent (productSampleIndexBy weightOf functionCounts argumentCounts functions arguments size) := by
  apply chooseSampler_coherent
  intro choice member
  obtain ⟨part, _, same⟩ := List.mem_map.mp member
  subst choice
  exact productSampler_coherent _ _ _ (functionCoherent _) (argumentCoherent _)

/-- Count weighting derives positive branch masses from every retained product split. -/
theorem productSampleIndex_probability (functionCounts : List (Nat × Nat)) (argumentCounts : Nat → Nat)
    (functions : SampleIndex (α → β)) (arguments : SampleIndex α) (size : Nat)
    (nonempty : productSampleParts argumentCounts size 0 functionCounts ≠ [])
    (functionProbability : ∀ part ∈ productSampleParts argumentCounts size 0 functionCounts,
      IsProbability (functions part.functionSize).values ∧ IsProbability (functions part.functionSize).ranked)
    (argumentProbability : ∀ part ∈ productSampleParts argumentCounts size 0 functionCounts,
      IsProbability (arguments part.argumentSize).values ∧ IsProbability (arguments part.argumentSize).ranked) :
    IsProbability (productSampleIndex functionCounts argumentCounts functions arguments size).values ∧
      IsProbability (productSampleIndex functionCounts argumentCounts functions arguments size).ranked := by
  apply chooseSampler_probability
  · simpa using nonempty
  · intro choice member
    obtain ⟨part, belongs, same⟩ := List.mem_map.mp member
    subst choice
    obtain ⟨_, _, _, _, _, positive, _⟩ := productSampleParts_correct argumentCounts size 0 functionCounts part belongs
    exact Rat.natCast_pos.mpr positive
  · intro choice member
    obtain ⟨part, belongs, same⟩ := List.mem_map.mp member
    subst choice
    exact productSampler_probability _ _ _ (functionProbability part belongs) (argumentProbability part belongs)

/-- Map an index without changing the rank positions in any class. -/
def mapSampleIndex (transform : α → β) (sampling : SampleIndex α) : SampleIndex β :=
  fun size => mapSampler transform (sampling size)

/-- The atomic constructor is defined only at size one; other sizes represent the source's error case. -/
def atomicSampleIndex (sampling : ExactSampler α) (size : Nat) : Option (ExactSampler α) :=
  if size = 1 then some sampling else none

/-- An empty recursive language has no sampler at any size. -/
def emptySampleIndex (_size : Nat) : Option (ExactSampler α) := none

/-- Bounded sampling uses structural counts as masses and keeps all preceding class offsets. -/
def boundedSampler (classes : List (Nat × Nat)) (sampling : SampleIndex α) : ExactSampler α :=
  chooseSampler (choiceParts 0 (classes.map (fun entry =>
    ⟨entry.2, (entry.2 : Rat), sampling entry.1⟩)))

/-- Bounded sampling preserves the rank/value agreement of each exact-size sampler. -/
theorem boundedSampler_coherent (classes : List (Nat × Nat)) (sampling : SampleIndex α)
    (coherent : ∀ size, Coherent (sampling size)) : Coherent (boundedSampler classes sampling) := by
  apply choiceParts_coherent
  intro alternative member
  obtain ⟨entry, _, same⟩ := List.mem_map.mp member
  subst alternative
  exact coherent _

/-- Every compiled ticket width fits the same checked machine bound. -/
theorem compiled_width_bound (maximum : Nat) (weighted : List (Nat × α)) (compiled : Compiled α)
    (found : compileWeighted maximum weighted = some compiled)
    (positive : ∀ entry ∈ weighted, 0 < entry.1) (index : Nat) (group : Group α)
    (groupFound : compiled.groups[index]? = some group) : group.width ≤ maximum := by
  have correct := compileWeighted_correct maximum weighted compiled found
  have bounds := compiled_interval_bounds maximum weighted compiled found positive index group groupFound
  have groupsPositive : GroupsPositive compiled.groups := by
    rw [correct.2.1]
    exact groupWeighted_positive weighted positive
  have valuesPositive := List.length_pos_iff.mpr (groupsPositive group (List.mem_of_getElem? groupFound)).2
  have widthLe : group.width ≤ group.width * group.values.length := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left group.width valuesPositive
  omega

/-- The upper-midpoint search arithmetic also stays within the checked machine range. -/
theorem compiled_search_bounds (maximum : Nat) (weighted : List (Nat × α)) (compiled : Compiled α)
    (found : compileWeighted maximum weighted = some compiled)
    (positive : ∀ entry ∈ weighted, 0 < entry.1) (low high : Nat)
    (interval : low < high ∧ high < compiled.groups.length) :
    high - low + 1 ≤ maximum ∧ upperMidpoint low high ≤ maximum := by
  have correct := compileWeighted_correct maximum weighted compiled found
  have groupsPositive : GroupsPositive compiled.groups := by
    rw [correct.2.1]
    exact groupWeighted_positive weighted positive
  have lengthBound := (positive_group_bounds compiled.groups groupsPositive).1
  have midpoint := upperMidpoint_bounds low high interval.1
  omega

end MicroCFTA.Sampler









