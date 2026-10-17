import MicroCFTA.IntersectTotal

/-!
# Numeric rank for the full closed-root termination tuple

The bounded radix retains root size, unseen pairs, local weight, and swap.
Reset can restore the lower fields because it strictly decreases root size.
The rank uses initial uniform input bounds and the literal pair inventory.
-/
namespace MicroCFTA.IntersectNumericRank
open Language IntersectSchedule
variable {Symbol : Type} {view : View Symbol} {inputs : FiniteInput view}

/-- Append one bounded digit to a natural number. -/
def combine (width high low : Nat) : Nat := high * (width + 1) + low

/-- Lexicographic decrease gives numeric decrease when the child digit fits. -/
theorem combine_lt {width firstHigh lastHigh firstLow lastLow : Nat}
    (bounded : firstLow ≤ width)
    (less : firstHigh < lastHigh ∨ firstHigh = lastHigh ∧ firstLow < lastLow) :
    combine width firstHigh firstLow < combine width lastHigh lastLow := by
  rcases less with high | ⟨rfl, low⟩
  · have step := Nat.mul_le_mul_right (width + 1) (show firstHigh + 1 ≤ lastHigh by omega)
    rw [Nat.add_mul, Nat.one_mul] at step
    unfold combine
    omega
  · exact Nat.add_lt_add_left low _

/-- A fitting digit retains the capacity of its bounded high field. -/
theorem combine_bound {width high low capacity : Nat} (highBound : high < capacity) (lowBound : low ≤ width) :
    combine width high low < capacity * (width + 1) := by
  have step := Nat.mul_le_mul_right (width + 1) (show high + 1 ≤ capacity by omega)
  rw [Nat.add_mul, Nat.one_mul] at step
  unfold combine
  omega

/-- The outer termination field is the sum of both closed-root sizes. -/
def rootSize (bounds : InputBounds view inputs) (roots : ClosedRoots view inputs) : Nat :=
  bounds.size roots.left + bounds.size roots.right

/-- Encode the exact termination tuple with a uniform source payload bound. -/
def rank (bounds : InputBounds view inputs) (bound : Nat) (roots : ClosedRoots view inputs) (call : Call Symbol) : Nat :=
  let parts := measure bounds.pairs bounds.localWeight.value call
  combine 1 (combine (2 * bound + 1) (combine bounds.pairs.length (rootSize bounds roots) parts.1) parts.2.1) parts.2.2

/-- Initial pair count and payload mass bound every encoded termination tuple. -/
def ceiling (pairs bound : Nat) : Nat := ((2 * bound + 1) * (pairs + 1) * (2 * bound + 2)) * 2

/-- All lower fields fit their initial radices, including arbitrary edge child lists. -/
theorem parts_bound (bounds : InputBounds view inputs) (bound : Nat)
    (uniform : ∀ input, bounds.localWeight.value input ≤ bound) (call : Call Symbol) :
    (measure bounds.pairs bounds.localWeight.value call).1 ≤ bounds.pairs.length ∧
      (measure bounds.pairs bounds.localWeight.value call).2.1 ≤ 2 * bound + 1 ∧
      (measure bounds.pairs bounds.localWeight.value call).2.2 ≤ 1 := by
  cases call with
  | node domain left right =>
      refine ⟨List.length_filter_le _ _, ?_, ?_⟩
      · have first := uniform left
        have second := uniform right
        change bounds.localWeight.value left + bounds.localWeight.value right ≤ _
        omega
      · change (if greater left right then 1 else 0) ≤ 1
        split <;> omega
  | edge domain left right =>
      refine ⟨List.length_filter_le _ _, ?_, Nat.zero_le _⟩
      have bounded := largest_le ((left.children.zip right.children).map fun pair =>
        bounds.localWeight.value pair.1 + bounds.localWeight.value pair.2) (2 * bound) (by
          intro value member
          obtain ⟨pair, _present, rfl⟩ := List.mem_map.mp member
          have first := uniform pair.1
          have second := uniform pair.2
          omega)
      change edgeWeight bounds.localWeight.value left right ≤ _
      unfold edgeWeight
      omega

/-- Every ready or stopping call has an initial numeric rank ceiling. -/
theorem rank_bound (bounds : InputBounds view inputs) (bound : Nat)
    (sizes : ∀ input, bounds.size input ≤ bound)
    (weights : ∀ input, bounds.localWeight.value input ≤ bound)
    (roots : ClosedRoots view inputs) (call : Call Symbol) :
    rank bounds bound roots call < ceiling bounds.pairs.length bound := by
  have parts := parts_bound bounds bound weights call
  have rootsBound : rootSize bounds roots < 2 * bound + 1 := by
    have first := sizes roots.left
    have second := sizes roots.right
    unfold rootSize
    omega
  have first := combine_bound rootsBound parts.1
  have second := combine_bound first parts.2.1
  exact combine_bound second parts.2.2

/-- Strict root-size decrease permits every bounded restoration of lower fields. -/
theorem root_decrease (bounds : InputBounds view inputs) (bound : Nat)
    (weights : ∀ input, bounds.localWeight.value input ≤ bound)
    (roots nextRoots : ClosedRoots view inputs) (parent child : Call Symbol)
    (less : rootSize bounds nextRoots < rootSize bounds roots) :
    rank bounds bound nextRoots child < rank bounds bound roots parent := by
  have parts := parts_bound bounds bound weights child
  have first := combine_lt parts.1 (Or.inl less)
  have second := combine_lt parts.2.1 (Or.inl first)
  exact combine_lt parts.2.2 (Or.inl second)

/-- Every actual local semantic transition retains the exact encoded lexicographic decrease. -/
theorem local_decrease (bounds : InputBounds view inputs) (bound : Nat)
    (weights : ∀ input, bounds.localWeight.value input ≤ bound)
    (roots nextRoots : ClosedRoots view inputs) (parent child : Call Symbol)
    (same : rootSize bounds nextRoots = rootSize bounds roots)
    (actual : LocalStep view bounds.pairs child parent) :
    rank bounds bound nextRoots child < rank bounds bound roots parent := by
  have parts := parts_bound bounds bound weights child
  have descent := local_decreases view bounds.pairs bounds.localWeight child parent actual
  unfold rank
  rw [same]
  rcases Prod.lex_def.mp descent with unseenLess | ⟨unseenSame, localLess⟩
  · have first := Nat.add_lt_add_left unseenLess (rootSize bounds roots * (bounds.pairs.length + 1))
    have second := combine_lt parts.2.1 (Or.inl first)
    exact combine_lt parts.2.2 (Or.inl second)
  · rw [unseenSame]
    rcases Prod.lex_def.mp localLess with weightLess | ⟨weightSame, swapLess⟩
    · have second := Nat.add_lt_add_left weightLess
        (combine bounds.pairs.length (rootSize bounds roots)
          (measure bounds.pairs bounds.localWeight.value parent).1 * (2 * bound + 1 + 1))
      exact combine_lt parts.2.2 (Or.inl second)
    · rw [weightSame]
      exact Nat.add_lt_add_left swapLess _

end MicroCFTA.IntersectNumericRank
