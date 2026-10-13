import MicroCFTA.SourceSizedDispatch

/-!
# A removed dead edge changes canonical class order

`sizedReference` orders the original graph. `fromFTA` first trims it.
The removed edge accepts no term, but it changes the order of two child
states. A plain unambiguous input can therefore have different class ranks.
The source now reads original rows directly for both query paths.
-/
namespace MicroCFTA.SourceSizedDispatchCounterexample
open Language RecursiveSize CanonicalClasses
open Std
attribute [local instance] lexOrd

/-- State 1 has an unproductive edge before its productive edge. -/
def original : Graph (Fin 5) (Nat × Nat) where
  nodes := List.finRange 5
  complete := by intro node; simp
  distinct := List.nodup_finRange 5
  rows node :=
    if node = 0 then [((1, 4), [1]), ((1, 4), [2])]
    else if node = 1 then [((1, 1), [4]), ((1, 3), [3])]
    else if node = 2 then [((1, 2), [3])]
    else if node = 3 then [((0, 0), [])]
    else []

/-- Remove the dead edge. An unused empty state does not affect the example. -/
def reduced : Graph (Fin 5) (Nat × Nat) :=
  { original with rows := fun node =>
      if node = 1 then [((1, 3), [3])] else original.rows node }

/-- Read the proved finite canonical loop's result. -/
def classes (graph : Graph Node (Nat × Nat)) : Node → Nat :=
  (canonical graph).getD (fun _ => 0)

/-- Order the actual edge rows by their arity, symbol, and child classes. -/
def ordered (graph : Graph Node (Nat × Nat)) : Automaton Node Nat :=
  fun node =>
    ((graph.rows node).mergeSort fun left right =>
      (compare (edgeKey (classes graph) left) (edgeKey (classes graph) right)).isLE).map
      fun edge => ⟨edge.1.2, edge.2, fun _ => true⟩

/-- Removing the unproductive edge reverses the two productive child classes. -/
theorem canonical_order_changes :
    classes original 1 < classes original 2 ∧ classes reduced 2 < classes reduced 1 := by
  cbv

/-- Both count-table classes have two terms, in opposite order. -/
theorem size_three_order_changes :
    RecursiveSize.enumerate (ordered original) 3 0 =
      [.node 4 [.node 3 [.node 0 []]], .node 4 [.node 2 [.node 0 []]]] ∧
    RecursiveSize.enumerate (ordered reduced) 3 0 =
      [.node 4 [.node 2 [.node 0 []]], .node 4 [.node 3 [.node 0 []]]] := by
  cbv

/-- Equal class counts do not establish equal class sequences. -/
theorem same_count_different_first :
    countAt (ordered original) 3 0 = countAt (ordered reduced) 3 0 ∧
    (RecursiveSize.enumerate (ordered original) 3 0)[0]? ≠
      (RecursiveSize.enumerate (ordered reduced) 3 0)[0]? := by
  constructor
  · rw [countAt_correct, countAt_correct, size_three_order_changes.1,
      size_three_order_changes.2]
    rfl
  · rw [size_three_order_changes.1, size_three_order_changes.2]
    decide

/-- All states are productive, but state 1 has a repeated leaf transition. -/
def duplicated : Graph (Fin 5) (Nat × Nat) where
  nodes := List.finRange 5
  complete := by intro node; simp
  distinct := List.nodup_finRange 5
  rows node :=
    if node = 0 then [((2, 4), [1, 3]), ((2, 4), [2, 4])]
    else if node = 1 then [((0, 0), []), ((0, 0), []), ((0, 3), [])]
    else if node = 2 then [((0, 0), []), ((0, 2), [])]
    else if node = 3 then [((0, 5), [])]
    else [((0, 6), [])]

/-- Interning removes only the repeated leaf edge in this finite graph. -/
def deduplicated : Graph (Fin 5) (Nat × Nat) :=
  { duplicated with rows := fun node =>
      if node = 1 then [((0, 0), []), ((0, 3), [])] else duplicated.rows node }

/-- Canonical refinement observes row multiplicity before interning removes it. -/
theorem duplicate_canonical_order_changes :
    classes duplicated 1 < classes duplicated 2 ∧
      classes deduplicated 2 < classes deduplicated 1 := by
  cbv

/-- First-occurrence term removal does not undo the canonical row-order change. -/
theorem duplicate_reference_order_changes :
    SourceSizedReference.classes (ordered duplicated) 3 0 =
      [.node 4 [.node 0 [], .node 5 []], .node 4 [.node 3 [], .node 5 []],
        .node 4 [.node 0 [], .node 6 []], .node 4 [.node 2 [], .node 6 []]] ∧
    SourceSizedReference.classes (ordered deduplicated) 3 0 =
      [.node 4 [.node 0 [], .node 6 []], .node 4 [.node 2 [], .node 6 []],
        .node 4 [.node 0 [], .node 5 []], .node 4 [.node 3 [], .node 5 []]] := by
  cbv

end MicroCFTA.SourceSizedDispatchCounterexample
