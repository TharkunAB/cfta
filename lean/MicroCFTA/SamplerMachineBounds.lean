import MicroCFTA.DecoderMachineBounds

/-!
# Machine arithmetic of the compiled weighted sampler

The checked ticket total supplies all local bounds. The source casts each
width before multiplication and computes its midpoint with signed Int
arithmetic. Every operation below stays in the nonnegative signed range.
-/
namespace MicroCFTA.SamplerMachineBounds
open Sampler DecoderMachineBounds

/-- The source compiled group adds its converted width times its array length. -/
def upperWord (bits start width size : Nat) : Nat :=
  add bits (cast bits start) (multiply bits (cast bits width) (cast bits size))

/-- Successful positive-ticket compilation preserves all group arithmetic exactly. -/
theorem group_machine (bits : Nat) (weighted : List (Nat × Value)) (compiled : Compiled Value)
    (found : compileWeighted (maximum bits) weighted = some compiled)
    (positive : ∀ entry ∈ weighted, 0 < entry.1) (index : Nat) (group : Group Value)
    (groupFound : compiled.groups[index]? = some group) :
    narrow bits group.width = (group.width : Int) ∧
      narrow bits group.values.length = (group.values.length : Int) ∧
      signed bits (upperWord bits (lowerBound compiled.groups index) group.width group.values.length) =
        ((lowerBound compiled.groups index + group.width * group.values.length : Nat) : Int) := by
  have bounds := compiled_interval_bounds (maximum bits) weighted compiled found positive index group groupFound
  have width := compiled_width_bound (maximum bits) weighted compiled found positive index group groupFound
  refine ⟨narrow_exact bits _ width, narrow_exact bits _ bounds.2.1, ?_⟩
  rw [upperWord, multiply_cast, add_cast]
  exact narrow_exact bits _ bounds.2.2.1

/-- The source subtracts the lower index, adds one, divides by two, and adds the lower index. -/
def midpointWord (bits low high : Nat) : Nat :=
  add bits (cast bits low)
    (cast bits ((add bits (subtract bits (cast bits high) (cast bits low)) (cast bits 1)) / 2))

/-- The actual midpoint word is the mathematical upper midpoint after the total-ticket check. -/
theorem midpoint_machine (bits : Nat) (weighted : List (Nat × Value)) (compiled : Compiled Value)
    (found : compileWeighted (maximum bits) weighted = some compiled)
    (positive : ∀ entry ∈ weighted, 0 < entry.1) (low high : Nat)
    (interval : low < high ∧ high < compiled.groups.length) :
    signed bits (midpointWord bits low high) = (upperMidpoint low high : Int) := by
  have bounds := compiled_search_bounds (maximum bits) weighted compiled found positive low high interval
  have correct := compileWeighted_correct (maximum bits) weighted compiled found
  have groupPositive : GroupsPositive compiled.groups := by
    rw [correct.2.1]
    exact groupWeighted_positive weighted positive
  have groupsBound := (positive_group_bounds compiled.groups groupPositive).1
  have total := groupWeighted_total weighted
  rw [← correct.2.1] at total
  have highBound : high ≤ maximum bits := by omega
  unfold midpointWord
  rw [subtract_cast bits high low highBound (by omega), add_cast bits (high - low) 1,
    cast_exact bits (high - low + 1) bounds.1, add_cast]
  exact narrow_exact bits _ bounds.2

/-- The payload index uses converted words for its ticket, group start, and width. -/
def payloadWord (bits ticket start width : Nat) : Nat :=
  cast bits ((subtract bits (cast bits ticket) (cast bits start)) / cast bits width)

/-- A selected group has an exact machine quotient and a safe payload-array index. -/
theorem payload_machine (bits : Nat) (weighted : List (Nat × Value)) (compiled : Compiled Value)
    (found : compileWeighted (maximum bits) weighted = some compiled)
    (positive : ∀ entry ∈ weighted, 0 < entry.1) (index : Nat) (group : Group Value)
    (groupFound : compiled.groups[index]? = some group) (ticket : Nat)
    (inside : lowerBound compiled.groups index ≤ ticket ∧
      ticket < lowerBound compiled.groups index + group.width * group.values.length) :
    let position := (ticket - lowerBound compiled.groups index) / group.width
    position < group.values.length ∧
      signed bits (payloadWord bits ticket (lowerBound compiled.groups index) group.width) = (position : Int) := by
  have bounds := compiled_interval_bounds (maximum bits) weighted compiled found positive index group groupFound
  have width := compiled_width_bound (maximum bits) weighted compiled found positive index group groupFound
  have ticketBound : ticket ≤ maximum bits := by omega
  have localBound : ticket - lowerBound compiled.groups index ≤ maximum bits := by omega
  have within : (ticket - lowerBound compiled.groups index) / group.width < group.values.length := by
    apply (Nat.div_lt_iff_lt_mul bounds.1).mpr
    rw [Nat.mul_comm]
    omega
  refine ⟨within, ?_⟩
  rw [payloadWord, subtract_cast bits ticket _ ticketBound inside.1,
    cast_exact bits _ localBound, cast_exact bits _ width]
  exact narrow_exact bits _ (Nat.le_trans (Nat.div_le_self _ _) localBound)

/-- The actual binary-search result supplies both safe table lookup and the selected payload interval. -/
theorem lookup_machine (bits : Nat) (weighted : List (Nat × Value)) (compiled : Compiled Value)
    (found : compileWeighted (maximum bits) weighted = some compiled)
    (positive : ∀ entry ∈ weighted, 0 < entry.1) (ticket : Nat) (valid : ticket < compiled.bound) :
    let index := ticketSearch (lowerBound compiled.groups) ticket 0 (compiled.groups.length - 1)
    ∃ group, compiled.groups[index]? = some group ∧
      (ticket - lowerBound compiled.groups index) / group.width < group.values.length ∧
      signed bits (payloadWord bits ticket (lowerBound compiled.groups index) group.width) =
        (((ticket - lowerBound compiled.groups index) / group.width : Nat) : Int) := by
  have correct := compileWeighted_correct (maximum bits) weighted compiled found
  have total := groupWeighted_total weighted
  rw [← correct.2.1, ← correct.1] at total
  have interval := ticketSearch_interval compiled.groups ticket (by omega)
  let index := ticketSearch (lowerBound compiled.groups) ticket 0 (compiled.groups.length - 1)
  let group := compiled.groups[index]'interval.1
  have groupFound : compiled.groups[index]? = some group := List.getElem?_eq_getElem interval.1
  have step := lowerBound_step compiled.groups index group groupFound
  have inside : lowerBound compiled.groups index ≤ ticket ∧
      ticket < lowerBound compiled.groups index + group.width * group.values.length := by
    refine ⟨interval.2.1, ?_⟩
    have upper : ticket < lowerBound compiled.groups (index + 1) := interval.2.2
    rw [step] at upper
    exact upper
  exact ⟨group, groupFound, payload_machine bits weighted compiled found positive index group groupFound ticket inside⟩

end MicroCFTA.SamplerMachineBounds
