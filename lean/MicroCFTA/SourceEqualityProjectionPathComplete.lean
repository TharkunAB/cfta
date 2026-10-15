import MicroCFTA.SourceEqualityProjectionPathDomain
import MicroCFTA.SourceEqualityProjectionComplete

/-!
# Finite projection in the selected path domain

Ordinary steps recurse only through selected children at shorter paths.
Recursive heads use the existing closed-input completion theorem. The
domain remains explicit. This module does not derive it from a source gate.
-/
namespace MicroCFTA.SourceEqualityProjectionPathComplete
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityProjectionGraph
open SourceEqualityProjectionPathDomain

private theorem rows_complete [DecidableEq (EdgeKey Symbol Guard)] (path : List Int) (index : Int)
    (childComplete : ∀ (value : Value Symbol Guard) before, SemanticReady before → Available before value →
      NodeClosed path value → ∃ result after, Project path value before result after ∧ Keeps before after ∧
        SemanticReady after ∧ Available after result ∧ result.free = [])
    (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (resident : Edges before edges) (domain : RowsClosed path index edges) :
    ∃ results after, ProjectRows path index edges before results after ∧ Keeps before after ∧
      SemanticReady after ∧ Values after results ∧ ClosedValues results := by
  induction edges generalizing before with
  | nil =>
      exact ⟨[], before, .nil, pure_keeps before semantic.ready, semantic,
        by simp [Values], by simp [ClosedValues]⟩
  | cons edge edges ih =>
      cases found : select edge.children index with
      | none =>
          obtain ⟨results, after, rest, keeps, ready, available, resultClosed⟩ := ih before semantic
            (fun value member => resident value (List.mem_cons_of_mem _ member))
            (fun value member => domain value (List.mem_cons_of_mem _ member))
          exact ⟨results, after, .missing found rest, keeps, ready, available, resultClosed⟩
      | some child =>
          obtain ⟨result, middle, first, keeps, ready, _, _⟩ := childComplete child before semantic
            (semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge
              (resident edge List.mem_cons_self) child (select_member found))
            (domain edge List.mem_cons_self child found)
          obtain ⟨results, after, rest, _, _, _, _⟩ := ih middle ready
            (fun original member => InternedEdgeResidency.edge_grows before middle keeps.growth original
              (resident original (List.mem_cons_of_mem _ member)))
            (fun original member => domain original (List.mem_cons_of_mem _ member))
          have trace := ProjectRows.selected found first rest
          exact ⟨_, _, trace, SourceEqualityProjectionPathDomain.rows_effects trace semantic resident domain⟩

/-- Every finite node path in the selected domain has a complete actual projection. -/
theorem node_complete [DecidableEq (EdgeKey Symbol Guard)] (path : List Int)
    (value : Value Symbol Guard) (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Available before value) (domain : NodeClosed path value) :
    ∃ result after, Project path value before result after ∧ Keeps before after ∧
      SemanticReady after ∧ Available after result ∧ result.free = [] := by
  induction path generalizing value before with
  | nil =>
      exact ⟨value, before, .root, pure_keeps before semantic.ready, semantic, available,
        by simpa only [NodeClosed] using domain⟩
  | cons index path ih =>
      cases value with
      | empty =>
          exact ⟨.empty, before, .empty, pure_keeps before semantic.ready, semantic, available, rfl⟩
      | reference name => simp [NodeClosed, Value.free] at domain
      | node entry edges depth free =>
          have facts := semantic.ready.semantic.1.normal.facts
          have selected : RowsClosed path index edges := by
            simpa only [NodeClosed, RowsClosed] using domain
          obtain ⟨values, middle, rows, _, ready, valuesAvailable, valuesClosed⟩ :=
            rows_complete path index ih edges before semantic
              (InternedEdgeResidency.resident_edges before facts.linked _ available.resident) selected
          obtain ⟨result, after, joined, _, _, _, _⟩ :=
            SourceEqualityProjectionUnion.complete values middle ready valuesAvailable valuesClosed
          have trace : Project (index :: path) (.node entry edges depth free) before result after :=
            .ordinary rows joined
          exact ⟨_, _, trace, SourceEqualityProjectionPathDomain.node_effects trace semantic available domain⟩
      | union entry members depth free =>
          exact SourceEqualityProjectionComplete.complete (index :: path) _ before semantic available
            (by simpa only [NodeClosed] using domain)
      | mu entry body probe ordinary =>
          exact SourceEqualityProjectionComplete.complete (index :: path) _ before semantic available
            (by simpa only [NodeClosed] using domain)

/-- Forest completion reads all root operands or only the selected proper-path operand. -/
theorem forest_complete [DecidableEq (EdgeKey Symbol Guard)] (path : List Int)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Values before values) (domain : ForestClosed path values) :
    ∃ result after, Forest path values before result after ∧ Keeps before after ∧
      SemanticReady after ∧ Available after result ∧ result.free = [] := by
  cases path with
  | nil =>
      obtain ⟨result, after, joined, rest⟩ := SourceEqualityProjectionUnion.complete values before semantic available
        (by simpa only [ForestClosed] using domain)
      exact ⟨result, after, .root joined, rest⟩
  | cons index path =>
      cases found : select values index with
      | none =>
          exact ⟨.empty, before, .missing found, pure_keeps before semantic.ready, semantic, empty_available before, rfl⟩
      | some value =>
          obtain ⟨result, after, body, rest⟩ := node_complete path value before semantic
            (available value (select_member found)) (domain value found)
          exact ⟨result, after, .selected found body, rest⟩

end MicroCFTA.SourceEqualityProjectionPathComplete
