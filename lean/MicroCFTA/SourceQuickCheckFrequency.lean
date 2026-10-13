import MicroCFTA.Probability

/-!
# The QuickCheck cumulative upper-bound search

Weights are nonnegative Integers represented by Nat. The backend contract
requires positive weights. The proofs also permit zero-width alternatives.
The source array is an ordered list. Machine index bounds are separate.
-/
namespace MicroCFTA.SourceQuickCheckFrequency
open Probability

/-- The source mapAccumL adds each weight before storing its upper bound. -/
def accumulate (start : Nat) : List (Nat × α) → Nat × List (Nat × α)
  | [] => (start, [])
  | (weight, value) :: rest =>
    let tail := accumulate (start + weight) rest
    (tail.1, (start + weight, value) :: tail.2)

/-- Each array position retains its input value and cumulative upper bound. -/
def cumulative (weighted : List (Nat × α)) : List (Nat × α) := (accumulate 0 weighted).2

/-- The start of an alternative is the total weight of its predecessors. -/
def weightBefore : List (Nat × α) → Nat → Nat
  | [], _ => 0
  | _ :: _, 0 => 0
  | (weight, _) :: rest, index + 1 => weight + weightBefore rest index

/-- mapAccumL obtains the exact unbounded Integer total. -/
theorem accumulate_total (weighted : List (Nat × α)) (start : Nat) :
    (accumulate start weighted).1 = start + ticketCount weighted := by
  induction weighted generalizing start with
  | nil => simp [accumulate, ticketCount]
  | cons entry rest ih => simp [accumulate, ticketCount, ih, Nat.add_assoc]

/-- Array construction does not sort or deduplicate alternatives. -/
theorem accumulate_length (weighted : List (Nat × α)) (start : Nat) :
    (accumulate start weighted).2.length = weighted.length := by
  induction weighted generalizing start with
  | nil => rfl
  | cons entry rest ih => simp [accumulate, ih]

theorem weightBefore_zero (weighted : List (Nat × α)) : weightBefore weighted 0 = 0 := by
  cases weighted <;> rfl

/-- Cumulative bounds are monotone even when some weights are zero. -/
theorem weightBefore_mono (weighted : List (Nat × α)) (left right : Nat) (ordered : left ≤ right) :
    weightBefore weighted left ≤ weightBefore weighted right := by
  induction weighted generalizing left right with
  | nil => simp [weightBefore]
  | cons entry rest ih =>
    cases left with
    | zero => simp [weightBefore]
    | succ left =>
      cases right with
      | zero => omega
      | succ right => exact Nat.add_le_add_left (ih left right (by omega)) _

/-- The last upper bound is the total draw bound. -/
theorem weightBefore_length (weighted : List (Nat × α)) : weightBefore weighted weighted.length = ticketCount weighted := by
  induction weighted with
  | nil => rfl
  | cons entry rest ih => simp [weightBefore, ticketCount, ih]

/-- Adjacent bounds differ by the weight at that array position. -/
theorem weightBefore_step (weighted : List (Nat × α)) (index : Nat) (entry : Nat × α)
    (found : weighted[index]? = some entry) :
    weightBefore weighted (index + 1) = weightBefore weighted index + entry.1 := by
  induction weighted generalizing index with
  | nil => simp at found
  | cons first rest ih =>
    cases index with
    | zero =>
      have same : first = entry := by simpa using found
      subst first
      simp [weightBefore, weightBefore_zero]
    | succ index =>
      have tail : rest[index]? = some entry := by simpa using found
      simp only [weightBefore, ih index tail, Nat.add_assoc]

/-- Every cumulative array read is derived from the corresponding input occurrence. -/
theorem accumulate_get (weighted : List (Nat × α)) (start index : Nat) (entry : Nat × α)
    (found : weighted[index]? = some entry) :
    (accumulate start weighted).2[index]? = some (start + weightBefore weighted (index + 1), entry.2) := by
  induction weighted generalizing start index with
  | nil => simp at found
  | cons first rest ih =>
    cases index with
    | zero =>
      have same : first = entry := by simpa using found
      subst first
      simp [accumulate, weightBefore, weightBefore_zero]
    | succ index =>
      have tail : rest[index]? = some entry := by simpa using found
      simpa [accumulate, weightBefore, Nat.add_assoc] using ih (start + first.1) index tail

/-- The source lower midpoint lies in the left half of every nontrivial interval. -/
theorem midpoint_bounds (low high : Nat) (strict : low < high) :
    low ≤ (low + high) / 2 ∧ (low + high) / 2 < high := by omega

/-- The source binary search stops only when its valid bounds agree. -/
def pick (upper : Nat → Nat) (selected low high : Nat) (ordered : low ≤ high) : Nat :=
  if same : low = high then low
  else
    let middle := (low + high) / 2
    if selected < upper middle then pick upper selected low middle (by have := midpoint_bounds low high (by omega); omega)
    else pick upper selected (middle + 1) high (by have := midpoint_bounds low high (by omega); omega)
termination_by high - low
decreasing_by all_goals have := midpoint_bounds low high (by omega); omega

/-- Every finite source search returns the first upper bound above its ticket. -/
theorem pick_correct (upper : Nat → Nat) (selected low high : Nat) (ordered : low ≤ high)
    (last : selected < upper high)
    (before : ∀ index, index < low → upper index ≤ selected)
    (monotone : ∀ left right, left ≤ right → right ≤ high → upper left ≤ upper right) :
    low ≤ pick upper selected low high ordered ∧ pick upper selected low high ordered ≤ high ∧
      selected < upper (pick upper selected low high ordered) ∧
      ∀ index, index < pick upper selected low high ordered → upper index ≤ selected := by
  rw [pick]
  split
  next same => subst high; exact ⟨Nat.le_refl _, Nat.le_refl _, last, before⟩
  next different =>
    have middle := midpoint_bounds low high (by omega)
    dsimp only
    split
    next earlier =>
      have ih := pick_correct upper selected low ((low + high) / 2) middle.1 earlier before
        (fun left right le bound => monotone left right le (by omega))
      exact ⟨ih.1, by omega, ih.2.2⟩
    next later =>
      have ih := pick_correct upper selected ((low + high) / 2 + 1) high (by omega) last
        (by intro index bound; have := monotone index ((low + high) / 2) (by omega) (by omega); omega) monotone
      exact ⟨by omega, ih.2⟩
termination_by high - low
decreasing_by all_goals have := midpoint_bounds low high (by omega); omega

/-- Search only reads upper bounds inside its original valid array interval. -/
theorem pick_congr (upper other : Nat → Nat) (selected low high : Nat) (ordered : low ≤ high)
    (same : ∀ index, low ≤ index → index ≤ high → upper index = other index) :
    pick upper selected low high ordered = pick other selected low high ordered := by
  rw [pick, pick]
  split
  · rfl
  · have middle := midpoint_bounds low high (by omega)
    dsimp only
    rw [same _ middle.1 (by omega)]
    split
    · apply pick_congr
      intro index lower upperBound
      exact same index lower (by omega)
    · apply pick_congr
      intro index lower upperBound
      exact same index (by omega) upperBound
termination_by high - low
decreasing_by all_goals have := midpoint_bounds low high (by omega); omega

/-- Read the actual cumulative array upper bound. Unused invalid reads return zero. -/
def upperAt (weighted : List (Nat × α)) (index : Nat) : Nat :=
  ((cumulative weighted)[index]?.map Prod.fst).getD 0

/-- All search reads expose the derived weightBefore sum. -/
theorem upperAt_eq (weighted : List (Nat × α)) (index : Nat) (valid : index < weighted.length) :
    upperAt weighted index = weightBefore weighted (index + 1) := by
  have found := accumulate_get weighted 0 index weighted[index] (List.getElem?_eq_getElem valid)
  simp only [upperAt, cumulative, found, Option.map_some, Option.getD_some, Nat.zero_add]

/-- The source returns the generator at the selected array position. -/
def select (weighted : List (Nat × α)) (ticket : Nat) : Option α :=
  if nonempty : 0 < weighted.length then
    ((cumulative weighted)[pick (upperAt weighted) ticket 0 (weighted.length - 1) (by omega)]?).map Prod.snd
  else none

/-- A valid source draw selects an original occurrence inside its exact ticket interval. -/
theorem select_interval (weighted : List (Nat × α)) (ticket : Nat) (valid : ticket < ticketCount weighted) :
    ∃ index entry, weighted[index]? = some entry ∧
      weightBefore weighted index ≤ ticket ∧ ticket < weightBefore weighted index + entry.1 ∧
      select weighted ticket = some entry.2 := by
  have nonempty : 0 < weighted.length := by cases weighted <;> simp_all [ticketCount]
  let index := pick (fun index => weightBefore weighted (index + 1)) ticket 0 (weighted.length - 1) (by omega)
  have final : weightBefore weighted (weighted.length - 1 + 1) = ticketCount weighted := by
    rw [Nat.sub_add_cancel (by omega), weightBefore_length]
  have selected := pick_correct (fun index => weightBefore weighted (index + 1)) ticket 0 (weighted.length - 1)
    (by omega) (by simpa only [final] using valid) (by intro index earlier; omega)
    (fun left right ordered _ => weightBefore_mono weighted _ _ (by omega))
  have inRange : index < weighted.length := by dsimp only [index]; omega
  let entry := weighted[index]
  have found : weighted[index]? = some entry := List.getElem?_eq_getElem inRange
  have lower : weightBefore weighted index ≤ ticket := by
    by_cases zero : index = 0
    · simp [zero, weightBefore_zero]
    · have before := selected.2.2.2 (index - 1) (by omega)
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ index)] using before
  have upper : ticket < weightBefore weighted index + entry.1 := by
    rw [←weightBefore_step weighted index entry found]
    exact selected.2.2.1
  have actual : pick (upperAt weighted) ticket 0 (weighted.length - 1) (by omega) = index := by
    apply pick_congr
    intro position _ before
    exact upperAt_eq weighted position (by omega)
  refine ⟨index, entry, found, lower, upper, ?_⟩
  rw [select, dite_eq_left nonempty, actual]
  simp only [cumulative, accumulate_get weighted 0 index entry found, Option.map_some]

/-- Any original occurrence owns its complete consecutive ticket interval. -/
theorem tickets_at (weighted : List (Nat × α)) (index : Nat) (entry : Nat × α)
    (found : weighted[index]? = some entry) (ticket : Nat)
    (lower : weightBefore weighted index ≤ ticket) (upper : ticket < weightBefore weighted index + entry.1) :
    (tickets weighted)[ticket]? = some entry.2 := by
  induction weighted generalizing index ticket with
  | nil => simp at found
  | cons first rest ih =>
    cases index with
    | zero =>
      have same : first = entry := by simpa using found
      subst first
      simp only [weightBefore] at upper
      have fits : ticket < entry.1 := by omega
      simp [tickets, List.getElem?_append, fits]
    | succ index =>
      have tail : rest[index]? = some entry := by simpa using found
      simp only [weightBefore] at lower upper
      rw [tickets, List.flatMap_cons, List.getElem?_append_right (by simpa using (show first.1 ≤ ticket by omega))]
      simpa only [List.length_replicate, tickets] using ih index tail (ticket - first.1) (by omega) (by omega)

/-- The actual binary array search agrees with ordered linear ticket selection. -/
theorem select_correct (weighted : List (Nat × α)) (ticket : Nat) (valid : ticket < ticketCount weighted) :
    select weighted ticket = (tickets weighted)[ticket]? := by
  obtain ⟨index, entry, found, lower, upper, selected⟩ := select_interval weighted ticket valid
  rw [selected, tickets_at weighted index entry found ticket lower upper]

end MicroCFTA.SourceQuickCheckFrequency
