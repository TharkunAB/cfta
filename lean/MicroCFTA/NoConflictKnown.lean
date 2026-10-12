import MicroCFTA.SourceGuardPlan

/-!
# Conflict-free actual names have known identities

Every source ambiguity witness creates two distinct representative/name values.
Both appear in the executable count-based conflict test. Thus no conflicts
implies an empty ambiguity set, without inspecting complete subtrees.
-/
namespace MicroCFTA.NoConflictKnown
open SourceGuards SourceObservations

/-- A positive sparse comparison requires two known leaves. -/
theorem compare_true_leaves [DecidableEq Formula] (left right : Observed Formula)
    (same : compareObserved left right = some true) : left.leafness = .leaf ∧ right.leafness = .leaf := by
  unfold compareObserved at same
  split at same
  · contradiction
  · cases hl : left.leafness <;> cases hr : right.leafness <;> simp_all

/-- Substitution cannot make an inner or mixed root into a leaf. -/
theorem sameShape_true_leaves [DecidableEq Formula] (formulas : Formulas Formula)
    (observed : Observations Formula) (scopes : List (List (Resolved Formula))) (left right : Path)
    (same : sameShape formulas observed scopes left right = some true) :
    (observed left).map Observed.leafness = some .leaf ∧
      (observed right).map Observed.leafness = some .leaf := by
  cases a : observed left with
  | none => simp [sameShape, a] at same
  | some first =>
      cases b : observed right with
      | none => simp [sameShape, a, b] at same
      | some second =>
          have comparison : compareObserved (renameObserved formulas scopes first)
              (renameObserved formulas scopes second) = some true := by simpa [sameShape, a, b] using same
          have leaves := compare_true_leaves _ _ comparison
          simpa [renameObserved] using leaves

/-- A non-leaf actual always retains its own position as sparse representative. -/
theorem nonleaf_representative [DecidableEq Formula] (formulas : Formulas Formula)
    (observed : Observations Formula) (entries : List (Actual Formula)) (actual : Actual Formula)
    (nonleaf : (observed actual.target).map Observed.leafness ≠ some .leaf) :
    representative observed (sameShape formulas observed []) entries actual = actual.target := by
  unfold representative
  split
  · rename_i canonical selected
    have accepted := List.find?_some selected
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at accepted
    rcases accepted.2 with comparison | leaves
    · exact False.elim (nonleaf (sameShape_true_leaves formulas observed [] _ _ comparison).1)
    · exact False.elim (nonleaf leaves.1)
  · rfl

/-- A known leaf can have only a known leaf as sparse representative. -/
theorem leaf_representative [DecidableEq Formula] (formulas : Formulas Formula)
    (observed : Observations Formula) (entries : List (Actual Formula)) (actual : Actual Formula)
    (leaf : (observed actual.target).map Observed.leafness = some .leaf) :
    (observed (representative observed (sameShape formulas observed []) entries actual)).map Observed.leafness = some .leaf := by
  unfold representative
  split
  · rename_i canonical selected
    have accepted := List.find?_some selected
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at accepted
    rcases accepted.2 with comparison | leaves
    · exact (sameShape_true_leaves formulas observed [] _ _ comparison).2
    · exact leaves.2
  · exact leaf

/-- An ambiguous pair cannot share one sparse representative path. -/
theorem ambiguous_representatives_apart [DecidableEq Formula] (formulas : Formulas Formula)
    (observed : Observations Formula) (entries : List (Actual Formula)) (first second : Actual Formula)
    (different : first.target ≠ second.target)
    (shape : (observed first.target).map Observed.leafness ≠ some .leaf ∨
      (observed second.target).map Observed.leafness ≠ some .leaf) :
    representative observed (sameShape formulas observed []) entries first ≠
      representative observed (sameShape formulas observed []) entries second := by
  intro same
  by_cases firstLeaf : (observed first.target).map Observed.leafness = some .leaf
  · have secondInner : (observed second.target).map Observed.leafness ≠ some .leaf := shape.resolve_left (fun h => h firstLeaf)
    have leaf := leaf_representative formulas observed entries first firstLeaf
    rw [same, nonleaf_representative formulas observed entries second secondInner] at leaf
    exact secondInner leaf
  · rw [nonleaf_representative formulas observed entries first firstLeaf] at same
    by_cases secondLeaf : (observed second.target).map Observed.leafness = some .leaf
    · have leaf := leaf_representative formulas observed entries second secondLeaf
      rw [← same] at leaf
      exact firstLeaf leaf
    · rw [nonleaf_representative formulas observed entries second secondLeaf] at same
      exact different same

/-- Two distinct members satisfying one predicate contribute at least two to the source count. -/
theorem countP_two [DecidableEq α] (items : List α) (first second : α) (predicate : α → Bool)
    (firstMember : first ∈ items) (secondMember : second ∈ items) (different : first ≠ second)
    (firstTrue : predicate first = true) (secondTrue : predicate second = true) :
    2 ≤ items.countP predicate := by
  have pairUnique : [first, second].Nodup := by simp [different]
  have subset : ∀ value ∈ [first, second], value ∈ items.filter predicate := by
    intro value member
    rcases List.mem_cons.mp member with rfl | tail
    · exact List.mem_filter.mpr ⟨firstMember, firstTrue⟩
    · have equal : value = second := by simpa using tail
      subst value
      exact List.mem_filter.mpr ⟨secondMember, secondTrue⟩
  have bound := List.Nodup.length_le_of_subset pairUnique subset
  simpa [List.countP_eq_length_filter] using bound

/-- Absence of count-based conflicts proves absence of every source ambiguity witness. -/
theorem no_conflicts_known [DecidableEq Formula] (formulas : Formulas Formula)
    (observed : Observations Formula) (guard : Guard Formula)
    (none : conflicts observed (sameShape formulas observed []) guard = []) :
    ambiguous observed (sameShape formulas observed []) guard = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro target member
  obtain ⟨first, firstMember, _, second, secondMember, different, sameName, _, _, shape⟩ :=
    (SourceActuals.ambiguous_iff _ _ _ target).mp member
  let entries := actuals observed guard
  let firstValue := (representative observed (sameShape formulas observed []) entries first, first.name)
  let secondValue := (representative observed (sameShape formulas observed []) entries second, second.name)
  have firstPresent : firstValue ∈ values observed (sameShape formulas observed []) guard := by
    simp only [values, List.mem_eraseDups]
    exact List.mem_map.mpr ⟨first, firstMember, rfl⟩
  have secondPresent : secondValue ∈ values observed (sameShape formulas observed []) guard := by
    simp only [values, List.mem_eraseDups]
    exact List.mem_map.mpr ⟨second, secondMember, rfl⟩
  have apart : firstValue ≠ secondValue := fun same =>
    ambiguous_representatives_apart formulas observed entries first second different shape (congrArg Prod.fst same)
  have count := countP_two (values observed (sameShape formulas observed []) guard) firstValue secondValue
    (fun value => decide (value.2 = firstValue.2)) firstPresent secondPresent apart (by simp)
    (by simpa [firstValue, secondValue] using sameName.symm)
  have conflicted : firstValue ∈ conflicts observed (sameShape formulas observed []) guard :=
    List.mem_filter.mpr ⟨firstPresent, by simp only [decide_eq_true_eq]; omega⟩
  simp [none] at conflicted

/-- A decided conflict-free trie result equals complete public guard evaluation. -/
theorem no_conflict_decided_exact [DecidableEq Formula] (formulas : Formulas Formula)
    (solver : Entailment Formula) (guard : Guard Formula) (term : Language.Term (Label Formula))
    (noConflict : conflicts (observe term) (sameShape formulas (observe term) []) guard = [])
    (decided : evaluateGuardWithShape formulas solver (SourceGuardPlan.observations guard term) guard ≠ .unknown) :
    evaluateGuardWithShape formulas solver (SourceGuardPlan.observations guard term) guard =
      evaluateGuard formulas solver guard term :=
  SourceGuardPlan.planned_decided_exact formulas solver guard term
    (no_conflicts_known formulas (observe term) guard noConflict) decided

end MicroCFTA.NoConflictKnown
