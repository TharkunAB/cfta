import MicroCFTA.EqualityLeafProjectionSchedule

/-!
# Bounded source identity iteration for projected leaf endpoints

The source tests canonical node identities. The proof can retain more
occurrences than the source. A changing source pass still changes this
occurrence representation, so its strictly decreasing weight bounds the
actual source loop.
-/
namespace MicroCFTA.EqualityLeafProjectionSchedule
open EqualityLeafProjectionSyntax

/-- Execution uses the actual lowered source equality test. -/
noncomputable def sourceRun (source : Source Tag Leaf Node) (meet : Leaf → Leaf → Leaf) (empty : Leaf)
    (read : Path → List Node → Leaf) (skip contradiction : Bool) (classes : List (List Path)) :
    Nat → List Node → Option (List Node)
  | 0, _ => none
  | fuel + 1, before => by
      classical
      exact let after := sourcePass source meet empty read skip contradiction classes before
        if after = before then some before else sourceRun source meet empty read skip contradiction classes fuel after

/-- A changing source pass strictly decreases the finite original-occurrence weight. -/
theorem source_changed_strict (source : Source Tag Leaf Node) (rank : Leaf → Nat)
    (meet : Leaf → Leaf → Leaf) (empty : Leaf) (laws : ConstructorLaws source meet)
    (leafProgress : ∀ target before, Progress rank (meet target before) before)
    (read : Path → List Node → Leaf) (skip contradiction : Bool) (classes : List (List Path))
    (before : List (Tree Tag Leaf)) (valid : Endpoints classes.flatten before)
    (changed : sourcePass source meet empty read skip contradiction classes (lowerForest source before) ≠ lowerForest source before) :
    forestWeight rank (pass source meet empty read skip contradiction classes before) < forestWeight rank before := by
  apply progress_strict _ _ _ (pass_progress source rank meet empty leafProgress read skip contradiction classes before)
  intro same
  apply changed
  rw [← pass_lower source meet empty laws read skip contradiction classes before valid, same]

/-- Fixed projected-leaf schedules terminate under local source constructor laws.
No projection synchronization, ancestor injectivity, or whole-pass contract is needed. -/
theorem source_terminates (source : Source Tag Leaf Node) (rank : Leaf → Nat)
    (meet : Leaf → Leaf → Leaf) (empty : Leaf) (laws : ConstructorLaws source meet)
    (leafProgress : ∀ target before, Progress rank (meet target before) before)
    (read : Path → List Node → Leaf) (skip contradiction : Bool) (classes : List (List Path))
    (before : List (Tree Tag Leaf)) (valid : Endpoints classes.flatten before) :
    ∃ fuel result, sourceRun source meet empty read skip contradiction classes fuel (lowerForest source before) = some result ∧
      sourcePass source meet empty read skip contradiction classes result = result ∧ fuel ≤ forestWeight rank before + 1 := by
  classical
  let after := pass source meet empty read skip contradiction classes before
  have lowered := pass_lower source meet empty laws read skip contradiction classes before valid
  by_cases fixed : sourcePass source meet empty read skip contradiction classes (lowerForest source before) = lowerForest source before
  · exact ⟨1, lowerForest source before, by simp [sourceRun, fixed], fixed, by omega⟩
  · have afterValid : Endpoints classes.flatten after := pass_endpoints source meet empty read skip contradiction classes before valid
    obtain ⟨fuel, result, finished, final, bounded⟩ :=
      source_terminates source rank meet empty laws leafProgress read skip contradiction classes after afterValid
    have smaller := source_changed_strict source rank meet empty laws leafProgress read skip contradiction classes before valid fixed
    refine ⟨fuel + 1, result, ?_, final, ?_⟩
    · simp only [sourceRun, fixed, ↓reduceIte]
      rw [← lowered]
      exact finished
    · change forestWeight rank after < forestWeight rank before at smaller
      omega
termination_by forestWeight rank before
decreasing_by exact source_changed_strict source rank meet empty laws leafProgress read skip contradiction classes before valid fixed

/-- The actual source residual algebra supplies finite leaf progress, including multiple symbols. -/
theorem source_guard_terminates (initial : List (SourceGuards.Guard FullSyntax.Formula))
    (source : Source Tag (FiniteLeafSymbolsProgress.Node (SourceLeafRowProgress.Row initial) symbols) Node)
    (laws : ConstructorLaws source (FiniteLeafSymbolsProgress.intersect (SourceLeafRowProgress.algebra initial)))
    (read : Path → List Node → FiniteLeafSymbolsProgress.Node (SourceLeafRowProgress.Row initial) symbols)
    (skip contradiction : Bool) (classes : List (List Path))
    (before : List (Tree Tag (FiniteLeafSymbolsProgress.Node (SourceLeafRowProgress.Row initial) symbols)))
    (valid : Endpoints classes.flatten before) :
    ∃ fuel result, sourceRun source (FiniteLeafSymbolsProgress.intersect (SourceLeafRowProgress.algebra initial))
        FiniteLeafSymbolsProgress.empty read skip contradiction classes fuel (lowerForest source before) = some result ∧
      sourcePass source (FiniteLeafSymbolsProgress.intersect (SourceLeafRowProgress.algebra initial))
        FiniteLeafSymbolsProgress.empty read skip contradiction classes result = result ∧
      fuel ≤ forestWeight (leafRank (SourceLeafRowProgress.algebra initial) (SourceLeafRowProgress.inventory initial)) before + 1 :=
  source_terminates source (leafRank (SourceLeafRowProgress.algebra initial) (SourceLeafRowProgress.inventory initial))
    (FiniteLeafSymbolsProgress.intersect (SourceLeafRowProgress.algebra initial)) FiniteLeafSymbolsProgress.empty laws
    (source_leaf_progress (SourceLeafRowProgress.algebra initial) (SourceLeafRowProgress.inventory initial)
      (SourceLeafRowProgress.inventory_complete initial)) read skip contradiction classes before valid

end MicroCFTA.EqualityLeafProjectionSchedule
