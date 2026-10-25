import MicroCFTA.SourceEqualityRequiredSemanticCache

/-!
# A finite future cache with exact language readback for a closed forest

The cold-table traversal is an existential proof witness. The required-path
worker does not run it. Every initial forest value has exact physical-graph
readback in one common future cache, including all requested exposed children.
-/
namespace MicroCFTA.SourceEqualityRequiredFuture
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open SourceColdSharedRows (Inputs ResidentRows)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache

/-- A finite closed source forest has one finite future cache with exact independent language readback. -/
theorem exact [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (inputs : Inputs before values) :
    ∃ after, SemanticReady after ∧ Grows before after ∧ Extends before.nodes.issued after.nodes.issued ∧
      ∀ value ∈ values, ∀ holds ambient term,
        EpsilonUnion.Accepts (MergedFreshOrdinaryGraph.graph after holds) value term ↔
          InternedGuardedLanguage.meaning holds ambient value term := by
  obtain ⟨rows, after, trace, depth, _⟩ := SourceFreshOrdinaryColdSharedTermination.complete
    (maximumDepth (nodeInventory before) + 1) before semantic.ready.semantic semantic.ready.covered semantic.ready.depth
    (InternedMuDepthInventory.initial_bounded before semantic.ready.semantic.1.normal.facts) (fun _ => none) values inputs
  have noRows : ResidentRows before (fun _ => none) := by intro identity edges absent; cases absent
  obtain ⟨afterSemantic, afterCovered, growth, history, _, resident⟩ :=
    trace.correct semantic.ready.semantic semantic.ready.covered inputs noRows
  have replayed := trace.replayed semantic.ready.semantic semantic.ready.covered inputs (by intro identity edges absent; cases absent)
  have closedRows := trace.closed (by intro identity edges absent; cases absent)
  have guarded := trace.guarded_heap semantic.ready.semantic semantic.ready.covered semantic.guarded inputs
  have budget := trace.budget_heap semantic.ready.semantic semantic.ready.covered semantic.budget inputs
  refine ⟨after, ⟨⟨afterSemantic, afterCovered, depth⟩, guarded, budget⟩, growth, history, ?_⟩
  intro value member holds ambient term
  exact SourceFreshOrdinaryColdGuardedExact.graph_exact after afterSemantic afterCovered guarded budget rows replayed resident closedRows
    value ((inputs value member).1.grows before after growth history) (inputs value member).2
    (trace.pending_done value member) holds ambient term

end MicroCFTA.SourceEqualityRequiredFuture
