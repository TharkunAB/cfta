import MicroCFTA.MergedColdMergeCompletion
import MicroCFTA.MergedComparisonStability

/-!
# Exact fuel stability of the cold merge worker

Increasing either proof bound preserves every completed record and its
exact final cache. The proof follows the actual ordered comparison filter
and constructor effects. It requires no source semantic premises.
-/
namespace MicroCFTA.MergedColdMergeStability
open InternedConstructorTemplates MergedSourceComparison MergedComparisonStability
open MergedColdMerge MergedPhysicalGroupColumns MergedOrdinaryHeight

/-- Extra comparison fuel preserves every completed ordered recursive-cover search. -/
theorem anyAccepts_refines [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (fuel extra : Nat) (narrow : Value Symbol Guard) (wides : List (Value Symbol Guard)) :
    Refines (MergedSourceSelection.anyAccepts clear fuel narrow wides)
      (MergedSourceSelection.anyAccepts clear (fuel + extra) narrow wides) := by
  induction wides with
  | nil => exact .refl _
  | cons wide rest ih =>
      simp only [MergedSourceSelection.anyAccepts]
      split
      · exact bind_refines _ _ _ _ (check_refines clear fuel extra [] wide narrow)
          (fun accepted => by cases accepted with
            | false => exact ih
            | true => exact .refl _)
      · exact .refl _

/-- Extra comparison fuel preserves the exact ordered retained list and its effects. -/
theorem retain_refines [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (fuel extra : Nat) (recursive inputs : List (Value Symbol Guard)) :
    Refines (MergedSourceSelection.retain clear fuel recursive inputs)
      (MergedSourceSelection.retain clear (fuel + extra) recursive inputs) := by
  induction inputs with
  | nil => exact .refl _
  | cons child rest ih =>
      simp only [MergedSourceSelection.retain]
      split
      · exact bind_refines _ _ _ _ ih (fun _ => .refl _)
      · exact bind_refines _ _ _ _ (anyAccepts_refines clear fuel extra child recursive)
          (fun _ => bind_refines _ _ _ _ ih (fun _ => .refl _))

/-- Ordered identity removal retains every completed selection result at extra fuel. -/
theorem select_refines [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (fuel extra : Nat) (inputs : List (Value Symbol Guard)) :
    Refines (MergedSourceSelection.select clear fuel inputs) (MergedSourceSelection.select clear (fuel + extra) inputs) :=
  bind_refines _ _ _ _ (retain_refines clear fuel extra (inputs.filter closedMu) inputs) (fun _ => .refl _)

/-- Ordered cold-action traversal preserves each completed callback result. -/
theorem map_refines (first second : Request → Action Symbol Guard Output)
    (same : ∀ request, Refines (first request) (second request)) (requests : List Request) :
    Refines (MergedColdMerge.map first requests) (MergedColdMerge.map second requests) := by
  induction requests with
  | nil => exact .refl _
  | cons first rest ih =>
      exact bind_refines _ _ _ _ (same first) (fun _ => bind_refines _ _ _ _ ih (fun _ => .refl _))

/-- Retained-column constructor branches preserve completed recursive results. -/
theorem retained_refines [DecidableEq (EdgeKey Symbol Guard)]
    (first second : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (same : ∀ value, Refines (first value) (second value)) (retained : List (Value Symbol Guard)) :
    Refines (retainedColumn first retained) (retainedColumn second retained) := by
  have branches (values : List (Value Symbol Guard)) :
      Refines (if values.any recursiveBoundary then work (makeUnion values) else MergedColdMerge.bind (work (MergedOrdinaryHeight.ordinaryUnion values)) first)
        (if values.any recursiveBoundary then work (makeUnion values) else MergedColdMerge.bind (work (MergedOrdinaryHeight.ordinaryUnion values)) second) := by
    split
    · exact .refl _
    · exact bind_refines _ _ _ _ (.refl _) same
  cases retained with
  | nil => exact branches []
  | cons value rest =>
      cases rest with
      | nil => exact .refl _
      | cons other tail => exact branches (value :: other :: tail)

/-- Actual stateful selection and retained-column construction preserve both completed bounds. -/
theorem column_refines [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (first second : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (same : ∀ value, Refines (first value) (second value)) (clear : Guard → Bool)
    (fuel extra : Nat) (inputs : List (Value Symbol Guard)) :
    Refines (column first clear fuel inputs) (column second clear (fuel + extra) inputs) :=
  bind_refines _ _ _ _ (select_refines clear fuel extra inputs) (retained_refines first second same)

/-- Small-edge construction preserves every completed ordered child trace. -/
theorem small_refines [DecidableEq (EdgeKey Symbol Guard)]
    (first second : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (same : ∀ value, Refines (first value) (second value)) (edge : EdgeValue Symbol Guard) :
    Refines (small first edge) (small second edge) :=
  bind_refines _ _ _ _ (map_refines first second same edge.children) (fun _ => .refl _)

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

/-- One derived comparison bound stabilizes every ordinary bound above the original input height. -/
theorem worker_saturated [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (groupsCorrect : ∀ edges, MergedPhysicalGroupRoot.Grouping edges (grouping edges))
    (clear : Guard → Bool) (top : Guard) (value : Value Symbol Guard) (state : State Symbol Guard)
    (facts : InternedNestedFacts.Facts state) (prepared : MergedPhysicalWarmup.Prepared state)
    (available : InternedProbeProvenance.Available state value) :
    ∃ bound result after, Extension state after ∧ InternedProbeProvenance.Available after result ∧
      ∀ ordinary comparison, height value ≤ ordinary → bound ≤ comparison →
        worker grouping clear top ordinary comparison value state = .done result after := by
  obtain ⟨bound, result, after, done, extension, valid⟩ :=
    execute_complete grouping groupsCorrect clear top value state facts prepared available
  refine ⟨bound, result, after, extension, valid, ?_⟩
  intro ordinary comparison ordinaryEnough comparisonEnough
  have replay := worker_refines grouping clear top (height value) ordinary ordinaryEnough
    bound (comparison - bound) value state result after (done bound (Nat.le_refl _))
  simpa only [Nat.add_sub_of_le comparisonEnough] using replay

/-- Every successful fuel choice has the full derived completion certificate. -/
theorem successful_verified [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (groupsCorrect : ∀ edges, MergedPhysicalGroupRoot.Grouping edges (grouping edges))
    (clear : Guard → Bool) (top : Guard) (value : Value Symbol Guard) (state : State Symbol Guard)
    (facts : InternedNestedFacts.Facts state) (prepared : MergedPhysicalWarmup.Prepared state)
    (available : InternedProbeProvenance.Available state value)
    (ordinary comparison : Nat) (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : worker grouping clear top ordinary comparison value state = .done result after) :
    Extension state after ∧ InternedProbeProvenance.Available after result := by
  obtain ⟨bound, output, final, completed, extension, valid⟩ :=
    execute_complete grouping groupsCorrect clear top value state facts prepared available
  have same := successful_results_eq grouping clear top ordinary (height value) comparison bound value state
    result output after final done (completed bound (Nat.le_refl _))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  exact ⟨extension, valid⟩

end MicroCFTA.MergedColdMergeStability
