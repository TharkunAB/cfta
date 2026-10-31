import MicroCFTA.SourceSizedMinimumConvergence

/-!
# Structural size bounds from the actual minimum pass

The pass derives a known row cost from the existing child lookups.
Suffix updates can only reduce those known costs.
The final table bounds every finite run of the guard-erased row grammar.
This does not assert attainment in the constrained accepted language.
-/
namespace MicroCFTA.SourceSizedMinimumStructuralBound
open SourceSizedMinimumPass SourceSizedMinimumConvergence SourceSizedDecided
open Language RecursiveSize
variable {Q Symbol Guard : Type}

private theorem fold_bounds (values : List Int) (first : Int) :
    values.foldl min first ≤ first ∧ ∀ cost ∈ values, values.foldl min first ≤ cost := by
  induction values generalizing first with
  | nil => exact ⟨Int.le_refl _, by intro cost impossible; cases impossible⟩
  | cons next rest ih =>
      change rest.foldl min (min first next) ≤ first ∧
        ∀ cost ∈ next :: rest, rest.foldl min (min first next) ≤ cost
      have tail := ih (min first next)
      refine ⟨by have bounded := tail.1; omega, ?_⟩
      intro cost member
      rcases List.mem_cons.mp member with atHead | inRest
      · subst cost
        have bounded := tail.1
        omega
      · exact tail.2 cost inRest

private theorem least_bound (values : List Int) (cost : Int) (member : cost ∈ values) :
    ∃ value, least values = some value ∧ value ≤ cost := by
  cases values with
  | nil => cases member
  | cons first rest =>
      refine ⟨rest.foldl min first, rfl, ?_⟩
      have bounds := fold_bounds rest first
      rcases List.mem_cons.mp member with atHead | inRest
      · subst cost
        exact bounds.1
      · exact bounds.2 cost inRest

private theorem add_known [DecidableEq Q] (key : Q) (rows : List (Row Q Symbol Guard))
    (known : Table Q) (current : Q) (old : Int) (before : known current = some old) :
    ∃ value, addMinimum key rows known current = some value ∧ value ≤ old := by
  cases selected : least (rows.filterMap (transitionMinimum known)) with
  | none => exact ⟨old, by simpa only [addMinimum, selected] using before, Int.le_refl _⟩
  | some candidate =>
      by_cases same : current = key
      · subst current
        refine ⟨min candidate old, ?_, by omega⟩
        simp only [addMinimum, selected, insertMinimum, ite_eq_left, before]
      · exact ⟨old, by simpa only [addMinimum, selected, insertMinimum, ite_eq_right same] using before,
          Int.le_refl _⟩

private theorem add_row_bound [DecidableEq Q] (key : Q) (rows : List (Row Q Symbol Guard))
    (known : Table Q) (row : Row Q Symbol Guard) (member : row ∈ rows)
    (cost : Int) (observed : transitionMinimum known row = some cost) :
    ∃ value, addMinimum key rows known key = some value ∧ value ≤ cost := by
  have listed : cost ∈ rows.filterMap (transitionMinimum known) :=
    List.mem_filterMap.mpr ⟨row, member, observed⟩
  obtain ⟨candidate, selected, bounded⟩ := least_bound _ cost listed
  cases oldLookup : known key with
  | none =>
      refine ⟨candidate, ?_, bounded⟩
      simp only [addMinimum, selected, insertMinimum, ite_eq_left, oldLookup]
  | some old =>
      refine ⟨min candidate old, ?_, by omega⟩
      simp only [addMinimum, selected, insertMinimum, ite_eq_left, oldLookup]

private theorem scan_known [DecidableEq Q] (source : Q → List (Row Q Symbol Guard))
    (keys : List Q) (known : Table Q) (current : Q) (old : Int) (before : known current = some old) :
    ∃ value, scan source keys known current = some value ∧ value ≤ old := by
  induction keys with
  | nil => exact ⟨old, before, Int.le_refl _⟩
  | cons key rest ih =>
      obtain ⟨middle, actual, bounded⟩ := ih
      obtain ⟨value, after, nextBound⟩ := add_known key (source key) (scan source rest known) current middle actual
      exact ⟨value, after, Int.le_trans nextBound bounded⟩

private theorem scan_children [DecidableEq Q] (source : Q → List (Row Q Symbol Guard))
    (keys : List Q) (known : Table Q) (children : List Q) (sizes : List Int)
    (observed : children.mapM known = some sizes) :
    ∃ nextSizes, children.mapM (scan source keys known) = some nextSizes ∧ nextSizes.sum ≤ sizes.sum := by
  induction children generalizing sizes with
  | nil =>
      change some [] = some sizes at observed
      have same := Option.some.inj observed
      subst sizes
      exact ⟨[], rfl, Int.le_refl _⟩
  | cons child rest ih =>
      cases head : known child with
      | none => simp [List.mapM_cons, head] at observed
      | some old =>
          cases tail : rest.mapM known with
          | none => simp [List.mapM_cons, head, tail] at observed
          | some olds =>
              have same : old :: olds = sizes := by simpa [List.mapM_cons, head, tail] using observed
              subst sizes
              obtain ⟨value, actual, bounded⟩ := scan_known source keys known child old head
              obtain ⟨values, actualTail, boundedTail⟩ := ih olds tail
              refine ⟨value :: values, ?_, ?_⟩
              · simp only [List.mapM_cons, actual, actualTail]
                rfl
              · simp only [List.sum_cons]
                omega

private theorem scan_row_bound [DecidableEq Q] (source : Q → List (Row Q Symbol Guard))
    (keys : List Q) (known : Table Q) :
    ∀ current row, current ∈ keys → row ∈ source current → ∀ sizes,
      row.children.mapM known = some sizes →
        ∃ value, scan source keys known current = some value ∧ value ≤ 1 + sizes.sum := by
  induction keys with
  | nil => intro current row impossible; cases impossible
  | cons key rest ih =>
      intro current row member rowMember sizes observed
      rcases List.mem_cons.mp member with atHead | inRest
      · subst current
        obtain ⟨nextSizes, children, bounded⟩ := scan_children source rest known row.children sizes observed
        have actualCost : transitionMinimum (scan source rest known) row = some (1 + nextSizes.sum) := by
          simp only [transitionMinimum, children, Option.map_some]
        obtain ⟨value, after, nextBound⟩ :=
          add_row_bound key (source key) (scan source rest known) row rowMember _ actualCost
        exact ⟨value, after, by omega⟩
      · obtain ⟨middle, actual, bounded⟩ := ih current row inRest rowMember sizes observed
        obtain ⟨value, after, nextBound⟩ := add_known key (source key) (scan source rest known) current middle actual
        exact ⟨value, after, Int.le_trans nextBound bounded⟩

/-- A row and its actual child lookups derive an upper bound for the actual completed pass. -/
theorem pass_row_bound [DecidableEq Q] (input : SourceSizedPreprocessing.Input Q Symbol Guard)
    (known : Table Q) (current : Q) (row : Row Q Symbol Guard) (member : row ∈ input.rows current)
    (sizes : List Int) (observed : row.children.mapM known = some sizes) :
    ∃ value, pass input known current = some value ∧ value ≤ 1 + sizes.sum :=
  scan_row_bound input.rows input.states known current row (input.complete current) member sizes observed

/-- The actual final table bounds every finite derivation when all row guards are erased. -/
theorem erased_lower_bound [DecidableEq Q] (input : SourceSizedPreprocessing.Input Q Symbol Guard)
    (current : Q) (term : Term Symbol)
    (accepted : Accepts (automaton input.rows (fun _ _ => true)) current term) :
    ∃ value, minimumSizes input current = some value ∧ value ≤ (nodeSize term : Int) := by
  induction accepted using Accepts.rec
    (motive_2 := fun states terms _ => ∃ sizes,
      states.mapM (minimumSizes input) = some sizes ∧ sizes.sum ≤ (forestSize terms : Int)) with
  | @node state edge terms edgeMember _childRuns _guardHolds ih =>
      obtain ⟨row, rowMember, sameEdge⟩ := List.mem_map.mp edgeMember
      subst edge
      obtain ⟨sizes, children, bounded⟩ := ih
      obtain ⟨value, actual, nextBound⟩ := pass_row_bound input (minimumSizes input) state row rowMember sizes children
      have fixed := (minimum_spec input).1
      rw [fixed] at actual
      refine ⟨value, actual, ?_⟩
      simp only [nodeSize]
      change value ≤ ((forestSize terms + 1 : Nat) : Int)
      omega
  | nil => exact ⟨[], rfl, by simp [forestSize]⟩
  | @cons state term states terms _childRun _childRuns ihHead ihTail =>
      obtain ⟨value, actual, bounded⟩ := ihHead
      obtain ⟨values, actualTail, boundedTail⟩ := ihTail
      refine ⟨value :: values, ?_, ?_⟩
      · simp only [List.mapM_cons, actual, actualTail]
        rfl
      · change value + values.sum ≤ ((nodeSize term + forestSize terms : Nat) : Int)
        omega

end MicroCFTA.SourceSizedMinimumStructuralBound
