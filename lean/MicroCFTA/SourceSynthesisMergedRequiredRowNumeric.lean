import MicroCFTA.SourceSynthesisRequiredRowNumeric
import MicroCFTA.SourceSynthesisUniversePrepared
import MicroCFTA.SourceSynthesisUniversePrefixConstruction
import MicroCFTA.MergedPrefixCompletion
import MicroCFTA.MergedSemanticReady
import MicroCFTA.SourceMemoGate

/-!
# Numeric Required bounds on actual merged synthesis rows

Original construction supplies the initial heap and its semantic invariants.
Complete merging returns the heap used by each following Required call.
Each actual merged row has a stable complete forest run at the trie bound.
The row calls start independently from that same returned merge heap.
This result does not bound complete recursive reduction or total sibling work.
-/
namespace MicroCFTA.SourceSynthesisMergedRequiredRowNumeric
open InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedNestedProvenance (Values)
open InternedEdgeResidency (nodeEdges)
open InternedShallowHeap
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceSynthesisTypeSyntax SourceSynthesisGeneralizeSyntax

variable [DecidableEq (EdgeKey String Guard)]

omit [DecidableEq (EdgeKey String Guard)] in
private theorem row_children_closed (input : Value String Guard) (before : State String Guard)
    (facts : Facts before) (available : Available before input) (closed : input.free = []) :
    ClosedEdges (nodeEdges input) := by
  cases input with
  | node entry rows depth free =>
      exact MergedColdReaderClosed.node_children_closed before facts entry rows depth free available closed
  | empty | reference | union | mu =>
      intro edge member
      cases member

/-- Original signed requests derive stable Required runs on the actual complete merge's row forests. -/
theorem firstOrderRaw_merged_required_rows_numeric (lib : Library) (query : Query) (size : Int) :
    match SourceSynthesisFirstOrderConstruction.firstOrderRaw lib query size with
    | .error _ => True
    | .ok expression =>
        ∃ input before comparisonBound merged after,
          InternedFreshOrdinaryConstruction.build expression [] empty = .done input before ∧
          Facts before ∧ Available before input ∧
          (∀ comparison, comparisonBound ≤ comparison →
            MergedColdMerge.execute MergedSourceGrouping.groups SourceMemoGate.plain top comparison input before =
              .done merged after) ∧
          MergedColdMerge.Extension before after ∧
          SourceEqualityRequiredSemanticCache.SemanticReady after ∧
          InternedFreshOrdinaryCostHeap.Heap after ∧ Available after merged ∧ merged.free = [] ∧
          NoNewMu before after ∧
          SourceSynthesisUniversePrefixHeight.height merged ≤ sizeOf expression + 1 ∧
          ∀ edge ∈ nodeEdges merged, ∀ paths : List (List Int),
            ∃ results final readerBound,
              (∀ worker reader, 2 * sizeOf (SourceEqualityNeeded.build paths) + 1 ≤ worker →
                readerBound ≤ reader →
                SourceEqualityRequiredExecution.requireAll worker reader paths edge.children after =
                  .done results final) ∧
              SourceEqualityRequiredCache.Keeps after final ∧ Values final results ∧ ClosedValues results := by
  cases accepted : SourceSynthesisFirstOrderConstruction.firstOrderRaw lib query size with
  | error => trivial
  | ok expression =>
      have original := SourceSynthesisUniversePrefixConstruction.firstOrderRaw_prefix_bound lib query size
      rw [accepted] at original
      obtain ⟨input, before, _pick, built, facts, available, _ready, _allowed, inputHeight⟩ := original
      have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty expression input before built
      have semantic := SourceEqualityRequiredSemanticCache.constructed expression input before built
      have costs : InternedFreshOrdinaryCostHeap.Heap before := by
        simpa only [built, Outcome.state] using InternedFreshOrdinaryCosts.closed_heap expression
      have shallow : Shallow before := by
        have origin := SourceSynthesisUniverseOrigins.firstOrderRaw_overUniverse lib query size expression accepted
        have retained := SourceSynthesisUniversePrepared.overUniverse_shallow _ expression origin empty
          empty_facts empty_shallow
        simpa only [built, Outcome.state] using retained
      have prepared := MergedPhysicalWarmup.prepared_of_shallow before facts shallow
      obtain ⟨comparisonBound, merged, after, complete, extension, mergedAvailable,
        unchanged, outputHeight, _atomOrigin⟩ :=
        MergedPrefixCompletion.source_execute_prefix_complete SourceMemoGate.plain top input before
          facts prepared available
      have effect := MergedSemanticReady.source_execute_ready SourceMemoGate.plain top comparisonBound
        input before merged after semantic costs prepared available
        (complete comparisonBound (Nat.le_refl _))
      have mergedClosed := effect.2.2.2 closed
      have closedRows := row_children_closed merged after extension.facts mergedAvailable mergedClosed
      refine ⟨input, before, comparisonBound, merged, after, built, facts, available, complete, extension,
        effect.1, effect.2.1, mergedAvailable, mergedClosed, unchanged,
        Nat.le_trans outputHeight (Nat.add_le_add_right inputHeight 1), ?_⟩
      intro edge member paths
      have resident := InternedEdgeResidency.resident_edges after extension.facts.linked merged
        mergedAvailable.resident edge member
      have children : Values after edge.children := extension.facts.cached.edges edge.entry.key edge resident
      obtain ⟨results, final, keeps, resultAvailable, resultClosed, oldWorker, oldReader, replay⟩ :=
        SourceEqualityRequiredExecution.requireAll_complete paths edge.children after effect.1.ready
          children (closedRows edge member)
      obtain ⟨readerBound, stable⟩ := SourceCurrentRequiredWorkerNumeric.requireAll oldWorker oldReader paths
        edge.children results after final (replay oldWorker oldReader (Nat.le_refl _) (Nat.le_refl _))
        effect.1 effect.2.1 children
      exact ⟨results, final, readerBound, stable, keeps, resultAvailable, resultClosed⟩

end MicroCFTA.SourceSynthesisMergedRequiredRowNumeric
