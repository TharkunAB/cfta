import MicroCFTA.SourceCurrentRequiredWorkerNumeric
import MicroCFTA.InternedFreshOrdinaryCosts
import MicroCFTA.SourceSynthesisFirstOrderConstruction

/-!
# Required-path worker depth from original construction

The original requirement fixes worker depth at twice its trie size plus one.
Empty-cache construction derives every semantic and stored-cost premise.
Reader completion supplies an internal bound and one stable returned heap.
This result does not count all sibling work or bound recursive reduction.
-/
namespace MicroCFTA.SourceSynthesisRequiredNumericInput
open InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open SourceEqualityNeeded

variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- Original syntax and a finite requirement derive stable execution at a fixed worker bound. -/
theorem constructed_node (expression : Syntax Symbol Guard) (needed : Needed) :
    ∃ input before result after readerBound,
      InternedFreshOrdinaryConstruction.build expression [] empty = .done input before ∧
      Facts before ∧ Available before input ∧
      (∀ worker reader, 2 * sizeOf needed + 1 ≤ worker → readerBound ≤ reader →
        SourceEqualityRequiredWorker.require worker reader needed input before = .done result after) ∧
      SourceEqualityRequiredCache.Keeps before after ∧ Available after result ∧ result.free = [] := by
  obtain ⟨input, before, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  have checked := InternedFreshOrdinaryFacts.closed_verified expression
  have facts : Facts before := by simpa only [built, Outcome.state] using checked.facts
  have available := checked.result input before built
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty expression input before built
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression input before built
  have costs : InternedFreshOrdinaryCostHeap.Heap before := by
    simpa only [built, Outcome.state] using InternedFreshOrdinaryCosts.closed_heap expression
  obtain ⟨result, after, graph, keeps, resident, resultClosed⟩ :=
    SourceEqualityRequiredComplete.complete needed input before semantic.ready available closed
  obtain ⟨readerBound, stable⟩ :=
    SourceCurrentRequiredWorkerNumeric.node needed graph semantic costs available
  exact ⟨input, before, result, after, readerBound, built, facts, available, stable, keeps, resident, resultClosed⟩

end MicroCFTA.SourceSynthesisRequiredNumericInput

namespace MicroCFTA.SourceSynthesisRequiredNumericInput
open SourceSynthesisTypeSyntax SourceSynthesisGeneralizeSyntax
open InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance

variable [DecidableEq (EdgeKey String Guard)]

/-- Original signed synthesis and path requests need no supplied completed graph or heap resource premise. -/
theorem firstOrderRaw_required_numeric (lib : Library) (query : Query) (size : Int)
    (paths : List (List Int)) :
    match SourceSynthesisFirstOrderConstruction.firstOrderRaw lib query size with
    | .error _ => True
    | .ok expression =>
        ∃ input before result after readerBound,
          InternedFreshOrdinaryConstruction.build expression [] empty = .done input before ∧
          Facts before ∧ Available before input ∧
          (∀ worker reader, 2 * sizeOf (SourceEqualityNeeded.build paths) + 1 ≤ worker → readerBound ≤ reader →
            SourceEqualityRequiredWorker.require worker reader (SourceEqualityNeeded.build paths) input before =
              .done result after) ∧
          SourceEqualityRequiredCache.Keeps before after ∧ Available after result ∧ result.free = [] := by
  cases returned : SourceSynthesisFirstOrderConstruction.firstOrderRaw lib query size with
  | error => trivial
  | ok expression => exact constructed_node expression (SourceEqualityNeeded.build paths)

end MicroCFTA.SourceSynthesisRequiredNumericInput
