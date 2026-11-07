import MicroCFTA.SourceSynthesisRequiredNumericInput

/-!
# Required-path worker depth for actual original row forests

Closed construction supplies each stored row's available closed children.
The original path trie fixes the worker bound for the complete child list.
The reader bound and the stable returned cache are derived internally.
This result covers one Required stage. It does not bound all sibling work
or complete recursive partial reduction.
-/
namespace MicroCFTA.SourceSynthesisRequiredRowNumeric
open InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedNestedProvenance (Values)
open InternedEdgeResidency (nodeEdges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityNeeded

variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

omit [DecidableEq (EdgeKey Symbol Guard)] in
private theorem row_children_closed (input : Value Symbol Guard) (before : State Symbol Guard)
    (facts : Facts before) (available : Available before input) (closed : input.free = []) :
    ClosedEdges (nodeEdges input) := by
  cases input with
  | node entry rows depth free =>
      exact MergedColdReaderClosed.node_children_closed before facts entry rows depth free available closed
  | empty | reference | union | mu =>
      intro edge member
      cases member

/-- Each actual constructed row derives a stable complete forest run at the original trie bound. -/
theorem constructed_rows (expression : Syntax Symbol Guard) :
    ∃ input before,
      InternedFreshOrdinaryConstruction.build expression [] empty = .done input before ∧
      Facts before ∧ Available before input ∧
      ∀ edge ∈ nodeEdges input, ∀ paths : List (List Int),
        ∃ results after readerBound,
          (∀ worker reader, 2 * sizeOf (SourceEqualityNeeded.build paths) + 1 ≤ worker → readerBound ≤ reader →
            SourceEqualityRequiredExecution.requireAll worker reader paths edge.children before = .done results after) ∧
          SourceEqualityRequiredCache.Keeps before after ∧ Values after results ∧ ClosedValues results := by
  obtain ⟨input, before, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  have checked := InternedFreshOrdinaryFacts.closed_verified expression
  have facts : Facts before := by simpa only [built, Outcome.state] using checked.facts
  have available := checked.result input before built
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty expression input before built
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression input before built
  have costs : InternedFreshOrdinaryCostHeap.Heap before := by
    simpa only [built, Outcome.state] using InternedFreshOrdinaryCosts.closed_heap expression
  have closedRows := row_children_closed input before facts available closed
  refine ⟨input, before, built, facts, available, ?_⟩
  intro edge member paths
  have resident := InternedEdgeResidency.resident_edges before facts.linked input available.resident edge member
  have children : Values before edge.children := facts.cached.edges edge.entry.key edge resident
  obtain ⟨results, after, keeps, resultAvailable, resultClosed, oldWorker, oldReader, replay⟩ :=
    SourceEqualityRequiredExecution.requireAll_complete paths edge.children before semantic.ready children
      (closedRows edge member)
  obtain ⟨readerBound, stable⟩ := SourceCurrentRequiredWorkerNumeric.requireAll oldWorker oldReader paths
    edge.children results before after (replay oldWorker oldReader (Nat.le_refl _) (Nat.le_refl _))
    semantic costs children
  exact ⟨results, after, readerBound, stable, keeps, resultAvailable, resultClosed⟩

end MicroCFTA.SourceSynthesisRequiredRowNumeric

namespace MicroCFTA.SourceSynthesisRequiredRowNumeric
open SourceSynthesisTypeSyntax SourceSynthesisGeneralizeSyntax
open InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedEdgeResidency (nodeEdges)
open MergedColdReaderClosedInputs (ClosedValues)

variable [DecidableEq (EdgeKey String Guard)]

/-- Original signed requests derive every row's Required stage without a supplied run or heap certificate. -/
theorem firstOrderRaw_required_rows_numeric (lib : Library) (query : Query) (size : Int) :
    match SourceSynthesisFirstOrderConstruction.firstOrderRaw lib query size with
    | .error _ => True
    | .ok expression =>
        ∃ input before,
          InternedFreshOrdinaryConstruction.build expression [] empty = .done input before ∧
          Facts before ∧ Available before input ∧
          ∀ edge ∈ nodeEdges input, ∀ paths : List (List Int),
            ∃ results after readerBound,
              (∀ worker reader, 2 * sizeOf (SourceEqualityNeeded.build paths) + 1 ≤ worker → readerBound ≤ reader →
                SourceEqualityRequiredExecution.requireAll worker reader paths edge.children before = .done results after) ∧
              SourceEqualityRequiredCache.Keeps before after ∧ Values after results ∧ ClosedValues results := by
  cases returned : SourceSynthesisFirstOrderConstruction.firstOrderRaw lib query size with
  | error => trivial
  | ok expression => exact constructed_rows expression

end MicroCFTA.SourceSynthesisRequiredRowNumeric
