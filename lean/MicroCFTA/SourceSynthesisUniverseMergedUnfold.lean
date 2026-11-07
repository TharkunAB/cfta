import MicroCFTA.SourceSynthesisUniverseUnfold
import MicroCFTA.SourceSynthesisUniversePrepared
import MicroCFTA.MergedPrefixCompletion
import MicroCFTA.SourceMemoGate

/-!
# Actual universe unfolding after complete original-input merging

Original construction derives the selected universe and heap preparation.
Complete merging retains that actual universe in its returned heap.
Its first unfolding has only the same universe atoms and at most two layers.
The result covers these two operations. It does not bound outer reduction.
-/
namespace MicroCFTA.SourceSynthesisUniverseMergedUnfold
open InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedBoundaryAtoms InternedShallowHeap SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisUniversePrefixSeed

variable [DecidableEq (EdgeKey String Guard)]

/-- Original requests derive complete merging and the actual retained universe's bounded unfolding. -/
theorem firstOrderRaw_merged_unfold_bound (lib : Library) (query : Query) (size : Int) :
    match SourceSynthesisFirstOrderConstruction.firstOrderRaw lib query size with
    | .error _ => True
    | .ok expression =>
        ∃ input before comparisonBound merged after,
          InternedFreshOrdinaryConstruction.build expression [] empty = .done input before ∧
          Facts before ∧ Available before input ∧
          (∀ comparison, comparisonBound ≤ comparison → MergedColdMerge.execute MergedSourceGrouping.groups
            SourceMemoGate.plain top comparison input before = .done merged after) ∧
          MergedColdMerge.Extension before after ∧ Available after merged ∧
          SourceSynthesisUniversePrefixHeight.height merged ≤ sizeOf expression + 1 ∧
          (atoms merged = [] ∨ ∃ own body probe ordinary,
            Available after (.mu own body probe ordinary) ∧
            (∀ atom ∈ atoms merged, atom = .mu own.identity) ∧
            ∃ entry rows depth free final,
              InternedFreshOrdinaryStoredSubstitution.unfold (.mu own body probe ordinary) after =
                .done (.node entry rows depth free) final ∧
              MergedColdMerge.Extension after final ∧ Available final (.node entry rows depth free) ∧
              (∀ atom ∈ atoms (.node entry rows depth free), atom = .mu own.identity) ∧
              SourceSynthesisUniversePrefixHeight.height (.node entry rows depth free) ≤ 2) := by
  cases returned : SourceSynthesisFirstOrderConstruction.firstOrderRaw lib query size with
  | error => trivial
  | ok expression =>
      have original := SourceSynthesisUniversePrefixConstruction.firstOrderRaw_prefix_bound lib query size
      rw [returned] at original
      obtain ⟨input, before, pick, built, facts, available, ready, allowed, bounded⟩ := original
      have shallow : Shallow before := by
        have origin := SourceSynthesisUniverseOrigins.firstOrderRaw_overUniverse lib query size expression returned
        have retained := SourceSynthesisUniversePrepared.overUniverse_shallow _ expression origin empty empty_facts empty_shallow
        simpa only [built, Outcome.state] using retained
      have prepared := MergedPhysicalWarmup.prepared_of_shallow before facts shallow
      obtain ⟨comparisonBound, merged, after, complete, extension, resident, _unchanged, resultHeight, atomOrigin⟩ :=
        MergedPrefixCompletion.source_execute_prefix_complete SourceMemoGate.plain top input before
          facts prepared available
      refine ⟨input, before, comparisonBound, merged, after, built, facts, available, complete,
        extension, resident, Nat.le_trans resultHeight (Nat.add_le_add_right bounded 1), ?_⟩
      cases pick with
      | none =>
          left
          cases present : atoms merged with
          | nil => rfl
          | cons atom rest =>
              have member := atomOrigin atom (by simp only [present, List.mem_cons_self])
              exact False.elim (allowed atom member)
      | some seed =>
          have afterReady : Ready (some seed) after := grows_trans ready extension.growth
          obtain ⟨entry, rows, depth, free, final, unfolded, unfoldedExtension, unfoldedAvailable, unfoldedAtoms,
            unfoldedHeight⟩ := SourceSynthesisUniverseUnfold.unfold_bounded seed after extension.facts
              extension.prepared afterReady
          right
          exact ⟨seed.entry, seed.body, seed.depth, seed.ordinary, seed.available_after after extension.facts afterReady,
            fun atom member => allowed atom (atomOrigin atom member), entry, rows, depth, free, final,
            unfolded, unfoldedExtension, unfoldedAvailable, unfoldedAtoms, unfoldedHeight⟩

end MicroCFTA.SourceSynthesisUniverseMergedUnfold
