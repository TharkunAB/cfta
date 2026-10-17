import MicroCFTA.SourceCurrentAllocatedRowReadNumeric
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000

namespace MicroCFTA.ReaderNumericIntegration
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open SourceCurrentAllocatedReaderConsumed (Run)
open SourceCurrentAllocatedReaderNumeric (collectFuel)
open SourceCurrentAllocatedRowReadNumeric (readFuel)
open MergedFreshOrdinaryExposure (collect nodeEdges)
local notation "Stored" => InternedValueMassHeap.Stored
local notation "initialBound" => InternedValueMassHeap.initialBound

private def nested : Syntax Nat Bool :=
  .binder false (.union [
    .node [.mk 0 true []],
    .binder false (.union [.node [.mk 1 false []], .node [.mk 2 true [.var 1]]])])

/-- Duplicate occurrences of a closed nested Mu use one initial computed collector bound. -/
theorem nested_duplicate_collect :
    ∃ input source count rows after,
      InternedFreshOrdinaryConstruction.build nested [] empty = .done input source ∧
      Run count ⟨source, [], [input, input]⟩ rows after ∧
      0 < count ∧ count ≤ collectFuel source.nodes.next source.edges.next (initialBound source) 2 ∧
      SourceCurrentAllocatedReaderControl.Good (initialBound source) after ∧
      SourceCurrentAllocatedReaderControl.Fits
        (collectFuel source.nodes.next source.edges.next (initialBound source) 2) after ∧
      after.pending = [] ∧
      collect (collectFuel source.nodes.next source.edges.next (initialBound source) 2)
        source [] [input, input] = .done rows after.heap ∧
      collect (count + 17) source [] [input, input] = .done rows after.heap ∧
      collect count after.heap [] [input, input] = .done rows after.heap := by
  obtain ⟨input, source, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete nested
  have semantic := SourceEqualityRequiredSemanticCache.constructed nested input source built
  have available := (InternedFreshOrdinaryFacts.closed_verified nested).result input source built
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty nested input source built
  have stored := InternedValueMassHeap.initial source semantic.ready.semantic.1.normal.facts
  have inputs : InternedNestedProvenance.Values source [input, input] := by
    intro value member
    simp only [List.mem_cons, List.mem_singleton] at member
    rcases member with rfl | rfl <;> exact available
  have closures : MergedColdReaderClosedInputs.ClosedValues [input, input] := by
    intro value member
    simp only [List.mem_cons, List.mem_singleton] at member
    rcases member with rfl | rfl <;> exact closed
  obtain ⟨count, rows, after, actual, enough, good, fits, empty, done, _stable⟩ :=
    SourceCurrentAllocatedReaderNumeric.collect_complete source [] [input, input] (initialBound source)
      semantic.ready.semantic semantic.ready.covered semantic.ready.depth inputs closures stored
  have positive : 0 < count := by
    cases count with
    | zero => have impossible := actual.exact; cases impossible
    | succ => omega
  have warm := MergedFreshOrdinaryColdReplay.collect_replay count source after.heap
    semantic.ready.semantic.1.normal.facts.coherent.valid [] [input, input] rows after.heap actual.exact (grows_refl _)
  exact ⟨input, source, count, rows, after, built, actual, positive, enough, good, fits,
    empty, done, actual.stable (count + 17) (by omega), warm⟩

private def productive : Syntax Nat Bool :=
  .binder false (.node [.mk 0 true [], .mk 1 false [.var 0]])

private theorem productive_shape : match InternedFreshOrdinaryConstruction.build productive [] empty with
    | .pending .. => False
    | .done input _ => ∃ entry body depth ordinary, input = .mu entry body depth ordinary ∧
        ∃ row ∈ InternedEdgeResidency.nodeEdges body, row.entry.key.symbol = 0 ∧ row.children = [] := by
  set_option cbv.maxSteps 100000000 in cbv
  exact ⟨_, _, _, _, rfl, _, .head _, rfl, rfl⟩

private theorem own_read (expression : Syntax Nat Bool) :
    ∃ input source rows after,
      InternedFreshOrdinaryConstruction.build expression [] empty = .done input source ∧
      nodeEdges (readFuel source.nodes.next source.edges.next (initialBound source)) input source = .done rows after ∧
      SourceEqualityProjectionRead.Read input source rows after ∧
      SourceEqualityRequiredCache.Keeps source after ∧ SourceEqualityRequiredSemanticCache.SemanticReady after ∧
      Stored (readFuel source.nodes.next source.edges.next (initialBound source)) after ∧
      after.nodes.next ≤ readFuel source.nodes.next source.edges.next (initialBound source) ∧
      after.edges.next ≤ readFuel source.nodes.next source.edges.next (initialBound source) ∧
      InternedNestedProvenance.Edges after rows ∧ MergedColdReaderClosedInputs.ClosedEdges rows ∧
      nodeEdges (readFuel source.nodes.next source.edges.next (initialBound source)) input after = .done rows after ∧
      nodeEdges (readFuel source.nodes.next source.edges.next (initialBound source) + 19) input source = .done rows after := by
  obtain ⟨input, source, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression input source built
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result input source built
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty expression input source built
  have stored := InternedValueMassHeap.initial source semantic.ready.semantic.1.normal.facts
  obtain ⟨rows, after, done, actual, keeps, afterSemantic, afterStored, nodes, edges, resident, rowsClosed, stable⟩ :=
    SourceCurrentAllocatedRowReadNumeric.complete input source (initialBound source) semantic available closed stored
  have warm := MergedFreshOrdinaryColdReplay.nodeEdges_replay
    (readFuel source.nodes.next source.edges.next (initialBound source)) input source after
    semantic.ready.semantic.1.normal.facts.coherent.valid rows after done (grows_refl _)
  exact ⟨input, source, rows, after, built, done, actual, keeps, afterSemantic,
    afterStored, nodes, edges, resident, rowsClosed, warm, stable 19⟩

/-- A source-built productive raw Mu obtains its own computed read and exact warm returned heap. -/
theorem productive_mu_read :
    ∃ input source rows after,
      InternedFreshOrdinaryConstruction.build productive [] empty = .done input source ∧
      (∃ entry body depth ordinary, input = .mu entry body depth ordinary ∧
        ∃ row ∈ InternedEdgeResidency.nodeEdges body, row.entry.key.symbol = 0 ∧ row.children = []) ∧
      nodeEdges (readFuel source.nodes.next source.edges.next (initialBound source)) input source = .done rows after ∧
      SourceEqualityProjectionRead.Read input source rows after ∧
      SourceEqualityRequiredCache.Keeps source after ∧ SourceEqualityRequiredSemanticCache.SemanticReady after ∧
      Stored (readFuel source.nodes.next source.edges.next (initialBound source)) after ∧
      after.nodes.next ≤ readFuel source.nodes.next source.edges.next (initialBound source) ∧
      after.edges.next ≤ readFuel source.nodes.next source.edges.next (initialBound source) ∧
      InternedNestedProvenance.Edges after rows ∧ MergedColdReaderClosedInputs.ClosedEdges rows ∧
      nodeEdges (readFuel source.nodes.next source.edges.next (initialBound source)) input after = .done rows after ∧
      nodeEdges (readFuel source.nodes.next source.edges.next (initialBound source) + 19) input source = .done rows after := by
  obtain ⟨input, source, rows, after, built, rest⟩ := own_read productive
  have shape := productive_shape
  rw [built] at shape
  exact ⟨input, source, rows, after, built, shape, rest⟩

private def unionSource : Syntax Nat Bool := .union [productive, .node [.mk 3 false []]]

private theorem union_shape : match InternedFreshOrdinaryConstruction.build unionSource [] empty with
    | .pending .. => False
    | .done input _ => ∃ entry members depth free, input = .union entry members depth free ∧
        ∃ member ∈ members, ∃ muEntry body level ordinary, member = .mu muEntry body level ordinary := by
  set_option cbv.maxSteps 100000000 in cbv
  exact ⟨_, _, _, _, rfl, _, .head _, _, _, _, _, rfl⟩

/-- A real union containing a productive Mu uses the computed closure fallback and warm replay. -/
theorem explicit_union_read :
    ∃ input source rows after,
      InternedFreshOrdinaryConstruction.build unionSource [] empty = .done input source ∧
      (∃ entry members depth free, input = .union entry members depth free ∧
        ∃ member ∈ members, ∃ muEntry body level ordinary, member = .mu muEntry body level ordinary) ∧
      nodeEdges (readFuel source.nodes.next source.edges.next (initialBound source)) input source = .done rows after ∧
      SourceEqualityProjectionRead.Read input source rows after ∧
      SourceEqualityRequiredCache.Keeps source after ∧ SourceEqualityRequiredSemanticCache.SemanticReady after ∧
      Stored (readFuel source.nodes.next source.edges.next (initialBound source)) after ∧
      after.nodes.next ≤ readFuel source.nodes.next source.edges.next (initialBound source) ∧
      after.edges.next ≤ readFuel source.nodes.next source.edges.next (initialBound source) ∧
      InternedNestedProvenance.Edges after rows ∧ MergedColdReaderClosedInputs.ClosedEdges rows ∧
      nodeEdges (readFuel source.nodes.next source.edges.next (initialBound source)) input after = .done rows after ∧
      nodeEdges (readFuel source.nodes.next source.edges.next (initialBound source) + 19) input source = .done rows after := by
  obtain ⟨input, source, rows, after, built, rest⟩ := own_read unionSource
  have shape := union_shape
  rw [built] at shape
  exact ⟨input, source, rows, after, built, shape, rest⟩

end MicroCFTA.ReaderNumericIntegration

#print axioms MicroCFTA.ReaderNumericIntegration.nested_duplicate_collect
#check @MicroCFTA.ReaderNumericIntegration.nested_duplicate_collect
#print axioms MicroCFTA.ReaderNumericIntegration.productive_mu_read
#check @MicroCFTA.ReaderNumericIntegration.productive_mu_read
#print axioms MicroCFTA.ReaderNumericIntegration.explicit_union_read
#check @MicroCFTA.ReaderNumericIntegration.explicit_union_read
