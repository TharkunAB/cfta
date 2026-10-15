import MicroCFTA.SourceMergedComparisonStability
import MicroCFTA.SourceMergedCompletion
import MicroCFTA.MergedColdMergeStability

/-!
# Exact stability of general repaired merge execution

Increasing either proof bound preserves every completed value and full
actual cache. General repaired comparison supplies the filter stability.
No semantic premise is required to retain completed execution traces.
-/
namespace MicroCFTA.SourceMergedStability
open InternedConstructorTemplates
open MergedSourceComparison (Result)
open MergedComparisonStability (Refines bind_refines)
open SourceMergedComparisonStability (check_refines)
open MergedColdMerge (Action pure bind work retainedColumn small)
open MergedColdMergeStability (map_refines retained_refines small_refines)
open SourceMergedWorker (column large group root worker)
open MergedPhysicalGroupColumns MergedOrdinaryHeight

/-- Extra comparison fuel preserves every completed ordered recursive-cover search. -/
theorem anyAccepts_refines [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (fuel extra : Nat) (narrow : Value Symbol Guard) (wides : List (Value Symbol Guard)) :
    Refines (SourceMergedSelection.anyAccepts clear fuel narrow wides)
      (SourceMergedSelection.anyAccepts clear (fuel + extra) narrow wides) := by
  induction wides with
  | nil => exact .refl _
  | cons wide rest ih =>
      simp only [SourceMergedSelection.anyAccepts]
      split
      · exact bind_refines _ _ _ _ (check_refines clear fuel extra [] wide narrow)
          (fun accepted => by cases accepted with
            | false => exact ih
            | true => exact .refl _)
      · exact .refl _

/-- Extra comparison fuel preserves the exact ordered retained list and its effects. -/
theorem retain_refines [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (fuel extra : Nat) (recursive inputs : List (Value Symbol Guard)) :
    Refines (SourceMergedSelection.retain clear fuel recursive inputs)
      (SourceMergedSelection.retain clear (fuel + extra) recursive inputs) := by
  induction inputs with
  | nil => exact .refl _
  | cons child rest ih =>
      simp only [SourceMergedSelection.retain]
      split
      · exact bind_refines _ _ _ _ ih (fun _ => .refl _)
      · exact bind_refines _ _ _ _ (anyAccepts_refines clear fuel extra child recursive)
          (fun _ => bind_refines _ _ _ _ ih (fun _ => .refl _))

/-- Ordered identity removal retains every completed selection result at extra fuel. -/
theorem select_refines [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (fuel extra : Nat) (inputs : List (Value Symbol Guard)) :
    Refines (SourceMergedSelection.select clear fuel inputs) (SourceMergedSelection.select clear (fuel + extra) inputs) :=
  bind_refines _ _ _ _ (retain_refines clear fuel extra (inputs.filter closedMu) inputs) (fun _ => .refl _)

/-- Actual stateful selection and retained-column construction preserve both completed bounds. -/
theorem column_refines [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (first second : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (same : ∀ value, Refines (first value) (second value)) (clear : Guard → Bool)
    (fuel extra : Nat) (inputs : List (Value Symbol Guard)) :
    Refines (column first clear fuel inputs) (column second clear (fuel + extra) inputs) :=
  bind_refines _ _ _ _ (select_refines clear fuel extra inputs) (retained_refines first second same)

/-- Large-edge construction preserves all completed column traces in their source order. -/
theorem large_refines [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (first second : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (same : ∀ value, Refines (first value) (second value)) (clear : Guard → Bool)
    (fuel extra : Nat) (top : Guard) (edge : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard)) :
    Refines (large first clear fuel top edge rest) (large second clear (fuel + extra) top edge rest) :=
  bind_refines _ _ _ _ (map_refines _ _ (column_refines first second same clear fuel extra) _) (fun _ => .refl _)

/-- The exact source threshold preserves both completed recursive and comparison bounds. -/
theorem group_refines [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (first second : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (same : ∀ value, Refines (first value) (second value)) (clear : Guard → Bool)
    (fuel extra : Nat) (top : Guard) (edges : List (EdgeValue Symbol Guard)) :
    Refines (group first clear fuel top edges) (group second clear (fuel + extra) top edges) := by
  unfold group
  split
  · exact map_refines _ _ (small_refines first second same) edges
  · cases edges with
    | nil => exact .refl _
    | cons edge rest => exact bind_refines _ _ _ _ (large_refines first second same clear fuel extra top edge rest) (fun _ => .refl _)

/-- Final parent interning preserves the completed trace of every structural group. -/
theorem root_refines [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (first second : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (same : ∀ value, Refines (first value) (second value)) (clear : Guard → Bool)
    (fuel extra : Nat) (top : Guard) (groups : List (List (EdgeValue Symbol Guard))) :
    Refines (root first clear fuel top groups) (root second clear (fuel + extra) top groups) :=
  bind_refines _ _ _ _ (map_refines _ _ (group_refines first second same clear fuel extra top) groups) (fun _ => .refl _)

/-- Increasing either bound preserves every completed cold worker result and exact final cache. -/
theorem worker_refines [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (clear : Guard → Bool) (top : Guard) (ordinary later : Nat) (more : ordinary ≤ later)
    (comparison extra : Nat) (value : Value Symbol Guard) :
    Refines (worker grouping clear top ordinary comparison value) (worker grouping clear top later (comparison + extra) value) := by
  induction ordinary generalizing later value with
  | zero =>
      cases later with
      | zero =>
          cases value with
          | empty | reference | union | mu => exact .refl _
          | node entry edges depth free =>
              by_cases closed : free = []
              · intro state value after impossible; simp [worker, closed] at impossible
              · simp only [worker, closed, ↓reduceIte]; exact .refl _
      | succ later =>
          cases value with
          | empty | reference | union | mu => exact .refl _
          | node entry edges depth free =>
              by_cases closed : free = []
              · intro state value after impossible; simp [worker, closed] at impossible
              · simp only [worker, closed, ↓reduceIte]; exact .refl _
  | succ ordinary ih =>
      cases later with
      | zero => omega
      | succ later =>
          cases value with
          | empty | reference | union | mu => exact .refl _
          | node entry edges depth free =>
              by_cases closed : free = []
              · simp only [worker, closed, ↓reduceIte]
                exact root_refines _ _ (fun value => ih later (by omega) value) clear comparison extra top (grouping edges)
              · simp only [worker, closed, ↓reduceIte]; exact .refl _

/-- Any two completed choices of both fuel bounds return the same record and exact cache. -/
theorem successful_results_eq [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (clear : Guard → Bool) (top : Guard) (firstOrdinary secondOrdinary firstComparison secondComparison : Nat)
    (value : Value Symbol Guard) (state : State Symbol Guard) (first second : Value Symbol Guard) (after final : State Symbol Guard)
    (firstDone : worker grouping clear top firstOrdinary firstComparison value state = .done first after)
    (secondDone : worker grouping clear top secondOrdinary secondComparison value state = .done second final) :
    (first, after) = (second, final) := by
  have firstReplay := worker_refines grouping clear top firstOrdinary (max firstOrdinary secondOrdinary) (Nat.le_max_left _ _)
    firstComparison secondComparison value state first after firstDone
  have secondReplay := worker_refines grouping clear top secondOrdinary (max firstOrdinary secondOrdinary) (Nat.le_max_right _ _)
    secondComparison firstComparison value state second final secondDone
  rw [Nat.add_comm secondComparison firstComparison] at secondReplay
  have same := Result.done.inj (firstReplay.symm.trans secondReplay)
  exact Prod.ext same.1 same.2

end MicroCFTA.SourceMergedStability
