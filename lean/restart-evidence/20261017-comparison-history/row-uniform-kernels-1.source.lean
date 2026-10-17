import MicroCFTA.SourceCurrentAllocatedRowReadUniform
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
namespace MicroCFTA.RowUniformIntegration
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open InternedValueMassHeap (Stored initialBound)
open SourceCurrentAllocatedRowReadNumeric (readFuel)
open MergedFreshOrdinaryExposure (nodeEdges)
private def Q (heap : State Nat Bool) := max (max heap.nodes.next heap.edges.next) (initialBound heap)
private def R (heap : State Nat Bool) := readFuel (Q heap) (Q heap) (Q heap)
private def productive : Syntax Nat Bool := .binder true (.node [.mk 0 true [], .mk 1 false [.var 0]])
private def alternatives : Syntax Nat Bool := .union [productive, .node [.mk 3 false []]]

private theorem own_read (expression : Syntax Nat Bool) :
    ∃ input source rows after,
      InternedFreshOrdinaryConstruction.build expression [] empty = .done input source ∧
      nodeEdges (R source) input source = .done rows after ∧ SourceEqualityProjectionRead.Read input source rows after ∧
      SourceEqualityRequiredCache.Keeps source after ∧ SourceEqualityRequiredSemanticCache.SemanticReady after ∧
      Stored (R source) after ∧ after.nodes.next ≤ R source ∧ after.edges.next ≤ R source ∧
      InternedNestedProvenance.Edges after rows ∧ MergedColdReaderClosedInputs.ClosedEdges rows ∧
      nodeEdges (readFuel (R source) (R source) (R source)) input after = .done rows after ∧
      nodeEdges (R source + 17) input source = .done rows after := by
  obtain ⟨input, source, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression input source built
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result input source built
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty expression input source built
  have initial := InternedValueMassHeap.initial source semantic.ready.semantic.1.normal.facts
  have stored : Stored (Q source) source := initial.mono (by unfold Q; omega)
  obtain ⟨rows, after, done, actual, kept, ready, afterStored, nodes, edges, resident, rowClosed, stable⟩ :=
    SourceCurrentAllocatedRowReadUniform.complete input source (Q source) semantic available closed stored
      (by unfold Q; omega) (by unfold Q; omega)
  have repeat := MergedFreshOrdinaryColdReplay.nodeEdges_replay (R source) input source after
    semantic.ready.semantic.1.normal.facts.coherent.valid rows after done (grows_refl _)
  have warmRead : SourceEqualityProjectionRead.Read input after rows after := .done (R source) repeat
  have warm := SourceCurrentAllocatedRowReadUniform.of_read warmRead (R source) ready (kept.available _ available)
    closed afterStored nodes edges
  exact ⟨input, source, rows, after, built, done, actual, kept, ready, afterStored, nodes, edges,
    resident, rowClosed, warm.1, stable 17⟩

private theorem mu_shape : match InternedFreshOrdinaryConstruction.build productive [] empty with
    | .pending .. => False
    | .done input _ => ∃ entry body depth ordinary, input = .mu entry body depth ordinary ∧
        ∃ row ∈ InternedEdgeResidency.nodeEdges body, row.entry.key.symbol = 0 ∧ row.children = [] := by
  set_option cbv.maxSteps 100000000 in cbv
  exact ⟨_, _, _, _, rfl, _, .head _, rfl, rfl⟩
private theorem union_shape : match InternedFreshOrdinaryConstruction.build alternatives [] empty with
    | .pending .. => False
    | .done input _ => ∃ entry members depth free, input = .union entry members depth free ∧
        ∃ member ∈ members, ∃ muEntry body level ordinary, member = .mu muEntry body level ordinary := by
  set_option cbv.maxSteps 100000000 in cbv
  exact ⟨_, _, _, _, rfl, _, .head _, _, _, _, _, rfl⟩

/-- A source-built productive Mu has a uniform read and a new-entry uniform warm replay. -/
theorem productive_uniform :
    ∃ input source rows after,
      InternedFreshOrdinaryConstruction.build productive [] empty = .done input source ∧
      (∃ entry body depth ordinary, input = .mu entry body depth ordinary ∧
        ∃ row ∈ InternedEdgeResidency.nodeEdges body, row.entry.key.symbol = 0 ∧ row.children = []) ∧
      nodeEdges (R source) input source = .done rows after ∧ SourceEqualityProjectionRead.Read input source rows after ∧
      SourceEqualityRequiredCache.Keeps source after ∧ SourceEqualityRequiredSemanticCache.SemanticReady after ∧
      Stored (R source) after ∧ after.nodes.next ≤ R source ∧ after.edges.next ≤ R source ∧
      InternedNestedProvenance.Edges after rows ∧ MergedColdReaderClosedInputs.ClosedEdges rows ∧
      nodeEdges (readFuel (R source) (R source) (R source)) input after = .done rows after ∧
      nodeEdges (R source + 17) input source = .done rows after := by
  obtain ⟨input, source, rows, after, built, rest⟩ := own_read productive
  have shape := mu_shape
  rw [built] at shape
  exact ⟨input, source, rows, after, built, shape, rest⟩

/-- A real union contains Mu and uses the same exact closure result at uniform warm fuel. -/
theorem union_uniform :
    ∃ input source rows after,
      InternedFreshOrdinaryConstruction.build alternatives [] empty = .done input source ∧
      (∃ entry members depth free, input = .union entry members depth free ∧
        ∃ member ∈ members, ∃ muEntry body level ordinary, member = .mu muEntry body level ordinary) ∧
      nodeEdges (R source) input source = .done rows after ∧ SourceEqualityProjectionRead.Read input source rows after ∧
      SourceEqualityRequiredCache.Keeps source after ∧ SourceEqualityRequiredSemanticCache.SemanticReady after ∧
      Stored (R source) after ∧ after.nodes.next ≤ R source ∧ after.edges.next ≤ R source ∧
      InternedNestedProvenance.Edges after rows ∧ MergedColdReaderClosedInputs.ClosedEdges rows ∧
      nodeEdges (readFuel (R source) (R source) (R source)) input after = .done rows after ∧
      nodeEdges (R source + 17) input source = .done rows after := by
  obtain ⟨input, source, rows, after, built, rest⟩ := own_read alternatives
  have shape := union_shape
  rw [built] at shape
  exact ⟨input, source, rows, after, built, shape, rest⟩
end MicroCFTA.RowUniformIntegration
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#print axioms MicroCFTA.RowUniformIntegration.productive_uniform
#check @MicroCFTA.RowUniformIntegration.productive_uniform
#print axioms MicroCFTA.RowUniformIntegration.union_uniform
#check @MicroCFTA.RowUniformIntegration.union_uniform
