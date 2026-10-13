import MicroCFTA.SourceInternedIntersectionDispatchCompletion

/-!
# Source recursion equations for completed ordinary dispatch

The completed computation calls the completed dispatcher on every child.
It needs no fuel argument from its caller. The source swap step re-enters
the dispatcher on the reversed pair. This equation concerns constructor
Work; the outer and reversed memo entries remain distinct source requests.
-/
namespace MicroCFTA.SourceInternedIntersectionDispatch
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedProvenance InternedEdgeResidency SourceInternedIntersectionRows

/-- Complete the dispatched ordinary construction with its derived bound. -/
noncomputable def completed [DecidableEq Symbol] (pair : Value Symbol Unit × Value Symbol Unit) : Work Symbol Unit (Value Symbol Unit) :=
  dispatch (bound pair) pair

/-- A sufficient caller bound executes exactly each child's own completed computation. -/
theorem resolved_calls [DecidableEq Symbol] (fuel : Nat) (pair : Value Symbol Unit × Value Symbol Unit)
    (left : sizeOf pair.1 ≤ fuel + 1) (right : sizeOf pair.2 ≤ fuel + 1) :
    dispatch (fuel + 1) pair =
      if hasEmpty pair then .pure .empty else if closedSelf pair then .pure pair.1
      else node completed (nodeEdges (ordered pair).1) (nodeEdges (ordered pair).2) := by
  simp only [dispatch]
  split
  · rfl
  · split
    · rfl
    · apply node_congr
      intro edgePair member request inside
      have original := (pairs_member _ _ edgePair).mp member
      have children := List.of_mem_zip inside
      have sizes := ordered_sizes (fuel + 1) pair left right
      have leftLess := child_smaller (ordered pair).1 edgePair.1 original.1 request.1 children.1
      have rightLess := child_smaller (ordered pair).2 edgePair.2 original.2.1 request.2 children.2
      have childBound : bound request ≤ fuel := Nat.max_le.mpr ⟨by omega, by omega⟩
      have stable := dispatch_stable (bound request) request (Nat.le_max_left _ _) (Nat.le_max_right _ _) (fuel - bound request)
      rw [Nat.add_sub_of_le childBound] at stable
      exact stable

/-- The finite completed worker satisfies the unbounded ordinary source recursion equation. -/
theorem completed_equation [DecidableEq Symbol] (pair : Value Symbol Unit × Value Symbol Unit) :
    completed pair =
      if hasEmpty pair then .pure .empty else if closedSelf pair then .pure pair.1
      else node completed (nodeEdges (ordered pair).1) (nodeEdges (ordered pair).2) := by
  have left : sizeOf pair.1 ≤ bound pair := Nat.le_max_left _ _
  have right : sizeOf pair.2 ≤ bound pair := Nat.le_max_right _ _
  cases found : bound pair with
  | zero => have positive := record_positive pair.1; omega
  | succ fuel =>
      unfold completed
      rw [found]
      exact resolved_calls fuel pair (by omega) (by omega)

/-- Reversing a closed unequal pair cannot introduce a self-intersection shortcut. -/
theorem closedSelf_swap_false (pair : Value Symbol Unit × Value Symbol Unit)
    (different : closedSelf pair = false) (leftClosed : pair.1.free = []) (rightClosed : pair.2.free = []) :
    closedSelf (pair.2, pair.1) = false := by
  simp only [closedSelf, leftClosed, List.isEmpty_nil, Bool.and_true] at different
  simp only [closedSelf, rightClosed, List.isEmpty_nil, Bool.and_true]
  simpa only [beq_eq_false_iff_ne, ne_comm] using different

/-- Source sorting re-enters the exact completed constructor computation on the reversed pair. -/
theorem completed_swap [DecidableEq Symbol] (pair : Value Symbol Unit × Value Symbol Unit)
    (nonempty : hasEmpty pair = false) (different : closedSelf pair = false) (swap : greater pair.1 pair.2 = true)
    (leftClosed : pair.1.free = []) (rightClosed : pair.2.free = []) :
    completed pair = completed (pair.2, pair.1) := by
  have emptySwap : hasEmpty (pair.2, pair.1) = false := by simpa only [hasEmpty, Bool.or_comm] using nonempty
  rw [completed_equation pair, completed_equation (pair.2, pair.1)]
  simp [nonempty, different, emptySwap, closedSelf_swap_false pair different leftClosed rightClosed,
    ordered, swap, greater_swap pair.1 pair.2 swap]

/-- The actual public guard decision selects the corresponding completed source branch. -/
theorem public_equation [DecidableEq Symbol] (pair : Value Symbol Unit × Value Symbol Unit)
    (leftPlain : Plain pair.1) (rightPlain : Plain pair.2)
    (state : State Symbol Unit) (facts : Facts state) (inputs : Inputs state pair) :
    completed pair = match decision emptyDomain pair with
      | .empty => .pure .empty
      | .self => .pure pair.1
      | .swap => completed (pair.2, pair.1)
      | .ordinary => node completed (nodeEdges pair.1) (nodeEdges pair.2)
      | .reset | .repeated => .pure .empty := by
  rw [public_decision pair leftPlain rightPlain state facts inputs]
  by_cases empty : hasEmpty pair = true
  · rw [completed_equation]
    simp [empty]
  · by_cases same : closedSelf pair = true
    · rw [completed_equation]
      simp [empty, same]
    · by_cases swap : greater pair.1 pair.2 = true
      · simp only [empty, same, swap, ↓reduceIte]
        exact completed_swap pair (Bool.eq_false_iff.mpr empty) (Bool.eq_false_iff.mpr same) swap
          (plain_closed pair.1 leftPlain state facts inputs.1) (plain_closed pair.2 rightPlain state facts inputs.2)
      · rw [completed_equation]
        simp [empty, same, ordered, swap]

end MicroCFTA.SourceInternedIntersectionDispatch
