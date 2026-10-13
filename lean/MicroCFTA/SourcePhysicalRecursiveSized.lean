import MicroCFTA.SourcePhysicalRecursiveConstruction
import MicroCFTA.SourceSizedReferenceAPI

/-!
# Exact size classes from an actually constructed recursive knot

Source construction, actual unfolding, and finite shared readback supply the
graph. Its independent chain language has one term at every positive node
count. Exact reference classes retain that term once. Every class has a
finite evaluation, and the shared four-query sequence has both inverse laws.
-/
namespace MicroCFTA.SourcePhysicalRecursiveSized
open Language RecursiveSize SourcePhysicalRecursiveRows SourcePhysicalRecursiveConstruction
open InternedConstructorTemplates InternedNestedConstruction InternedEdgeResidency

variable {Symbol Carrier Item : Type}

/-- The finite chain with the specified number of unary steps. -/
def term (base step : Symbol) : Nat → Term Symbol
  | 0 => .node base []
  | size + 1 => .node step [term base step size]

/-- A chain has one base node and one node per unary step. -/
theorem term_size (base step : Symbol) (size : Nat) : nodeSize (term base step size) = size + 1 := by
  induction size with
  | zero => simp [term, nodeSize]
  | succ size ih => simp [term, nodeSize, ih, Nat.add_assoc]

/-- Every independently specified chain is determined by its number of nodes. -/
theorem chain_unique (base step : Symbol) (value : Term Symbol) (accepted : Chain base step value) :
    value = term base step (nodeSize value - 1) := by
  induction accepted with
  | base => simp [term, nodeSize]
  | @step child accepted ih =>
      have size := nodeSize_pos child
      simp only [nodeSize, List.foldr_cons, List.foldr_nil, Nat.add_zero, Nat.add_sub_cancel]
      have next : nodeSize child = (nodeSize child - 1) + 1 := by omega
      conv => rhs; rw [next, term, ← ih]

/-- Every finite chain term belongs to the independent recursive language. -/
theorem term_chain (base step : Symbol) (size : Nat) : Chain base step (term base step size) := by
  induction size with
  | zero => exact .base
  | succ size ih => exact .step ih

/-- A duplicate-free list with exactly one possible member is that singleton. -/
theorem singleton_of_members (values : List Item) (value : Item) (distinct : values.Nodup)
    (members : ∀ other, other ∈ values ↔ other = value) : values = [value] := by
  cases values with
  | nil => have present := (members value).mpr rfl; cases present
  | cons first rest =>
      have head : first = value := (members first).mp List.mem_cons_self
      subst first
      have empty : rest = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro other member
        have same := (members other).mp (List.mem_cons_of_mem _ member)
        subst other
        exact (List.nodup_cons.mp distinct).1 member
      rw [empty]

/-- Exact shared-row language determines every positive reference class as one chain term. -/
theorem classes_exact [DecidableEq Symbol] (A : Automaton Carrier Symbol) (root : Carrier)
    (base step : Symbol) (exact : ∀ value, Accepts A root value ↔ Chain base step value) (size : Nat) :
    SourceSizedReference.classes A (size + 1) root = [term base step size] := by
  apply singleton_of_members _ _ (SourceSizedReference.classes_nodup A (size + 1) root)
  intro value
  rw [SourceSizedReference.mem_classes_iff, exact]
  constructor
  · rintro ⟨accepted, sized⟩
    rw [chain_unique base step value accepted, sized, Nat.add_sub_cancel]
  · intro same
    subst value
    exact ⟨term_chain base step size, term_size base step size⟩

/-- Actual construction and row exposure yield finite exact classes and both distinct-term inverses. -/
theorem source_sized [DecidableEq Symbol] (base step : Symbol) :
    ∃ result after fuel raw,
      InternedFreshOrdinaryConstruction.build (expression base step) [] empty =
        .done (record base step) (final base step) ∧
      InternedFreshOrdinaryStoredSubstitution.unfold (record base step) (final base step) = .done result after ∧
      (∀ larger, fuel ≤ larger → SourceInternedRows.toRows (heap 2 ((nodeEdges result).map exposure))
        larger (some 2) = some raw) ∧
      (∀ size, SourceSizedReference.classes (SourceRowsMinimumAdapter.automaton raw) (size + 1) (.interned 2) =
        [term base step size]) ∧
      (∀ size, SourceSizedReference.ClassEvaluation (SourceRowsMinimumAdapter.automaton raw) (size + 1) size (.interned 2)
        (SourceSizedReference.classes (SourceRowsMinimumAdapter.automaton raw) size (.interned 2))) ∧
      (∀ bound, (SourceSizedQueries.through
        (fun size => SourceSizedReference.classes (SourceRowsMinimumAdapter.automaton raw) size (.interned 2)) bound).Nodup ∧
        (SourceSizedQueries.through
        (fun size => SourceSizedReference.classes (SourceRowsMinimumAdapter.automaton raw) size (.interned 2)) bound).Pairwise
          (fun first second => nodeSize first ≤ nodeSize second)) ∧
      (∀ value position,
        SourceSizedQueries.rank (fun size => SourceSizedReference.classes (SourceRowsMinimumAdapter.automaton raw) size (.interned 2))
          nodeSize value = some position ↔
        SourceSizedQueries.unrank (fun size => SourceSizedReference.classes (SourceRowsMinimumAdapter.automaton raw) size (.interned 2))
          position = some value) := by
  obtain ⟨result, after, fuel, raw, built, unfolded, _, _, rows, language⟩ := source_rows base step
  refine ⟨result, after, fuel, raw, built, unfolded, rows, ?_, ?_, ?_, ?_⟩
  · exact classes_exact (SourceRowsMinimumAdapter.automaton raw) (.interned 2) base step language
  · exact fun size => SourceSizedReference.classes_evaluation_bound _ size _
  · exact fun bound => ⟨SourceSizedReferenceAPI.through_nodup _ _ bound,
      SourceSizedReferenceAPI.through_ordered _ _ bound⟩
  · intro value position
    exact ⟨SourceSizedReferenceAPI.unrank_rank _ _ value position,
      SourceSizedReferenceAPI.rank_unrank _ _ value position⟩

end MicroCFTA.SourcePhysicalRecursiveSized
