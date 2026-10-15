import MicroCFTA.SourceEqualityProjectionEffects
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

/-!
# Finite general source path projection

The induction decreases path length. Cycles in the input graph do not
increase this length. Each recursive head uses the completed cold reader.
-/
namespace MicroCFTA.SourceEqualityProjectionComplete
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityProjectionGraph

/-- A complete shorter path can be applied to every selected child in a finite row list. -/
theorem rows_complete [DecidableEq (EdgeKey Symbol Guard)] (path : List Int) (index : Int)
    (childComplete : ∀ (value : Value Symbol Guard) before, SemanticReady before → Available before value → value.free = [] →
      ∃ result after, Project path value before result after ∧ Keeps before after ∧ SemanticReady after ∧ Available after result ∧ result.free = [])
    (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (resident : Edges before edges) (closed : ClosedEdges edges) :
    ∃ results after, ProjectRows path index edges before results after ∧ Keeps before after ∧
      SemanticReady after ∧ Values after results ∧ ClosedValues results := by
  induction edges generalizing before with
  | nil => exact ⟨[], before, .nil, pure_keeps before semantic.ready, semantic, by simp [Values], by simp [ClosedValues]⟩
  | cons edge edges ih =>
      cases found : select edge.children index with
      | none =>
          obtain ⟨results, after, rest, keeps, ready, available, resultClosed⟩ := ih before semantic
            (fun value member => resident value (List.mem_cons_of_mem _ member))
            (fun value member => closed value (List.mem_cons_of_mem _ member))
          exact ⟨results, after, .missing found rest, keeps, ready, available, resultClosed⟩
      | some child =>
          have member := select_member found
          obtain ⟨result, middle, first, keeps, ready, _, _⟩ := childComplete child before semantic
            (semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge List.mem_cons_self) child member)
            (closed edge List.mem_cons_self child member)
          obtain ⟨results, after, rest, _, _, _, _⟩ := ih middle ready
            (fun edge present => InternedEdgeResidency.edge_grows before middle keeps.growth edge (resident edge (List.mem_cons_of_mem _ present)))
            (fun edge present => closed edge (List.mem_cons_of_mem _ present))
          have trace := ProjectRows.selected found first rest
          have checked := SourceEqualityProjectionEffects.rows trace semantic resident closed
          exact ⟨_, _, trace, checked⟩

/-- One ordinary step completes after its selected children and the actual closed union. -/
theorem ordinary_complete [DecidableEq (EdgeKey Symbol Guard)] (path : List Int) (index : Int)
    (childComplete : ∀ (value : Value Symbol Guard) before, SemanticReady before → Available before value → value.free = [] →
      ∃ result after, Project path value before result after ∧ Keeps before after ∧ SemanticReady after ∧ Available after result ∧ result.free = [])
    (value : Value Symbol Guard) (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Available before value) (closed : value.free = []) (ordinary : Ordinary value) :
    ∃ result after, Project (index :: path) value before result after ∧ Keeps before after ∧
      SemanticReady after ∧ Available after result ∧ result.free = [] := by
  cases value with
  | empty => exact ⟨.empty, before, .empty, pure_keeps before semantic.ready, semantic, available, rfl⟩
  | reference | union | mu => cases ordinary
  | node entry edges depth free =>
      have facts := semantic.ready.semantic.1.normal.facts
      obtain ⟨values, middle, rows, _, ready, valuesAvailable, valuesClosed⟩ := rows_complete path index childComplete edges before semantic
        (InternedEdgeResidency.resident_edges before facts.linked _ available.resident)
        (MergedColdReaderClosed.node_children_closed before facts entry edges depth free available closed)
      obtain ⟨result, after, union, _, _, _, _⟩ := SourceEqualityProjectionUnion.complete values middle ready valuesAvailable valuesClosed
      have trace : Project (index :: path) (.node entry edges depth free) before result after := .ordinary rows union
      exact ⟨_, _, trace, SourceEqualityProjectionEffects.node trace semantic available closed⟩

/-- Every finite signed path completes on every closed available source value. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)] (path : List Int)
    (value : Value Symbol Guard) (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Available before value) (closed : value.free = []) :
    ∃ result after, Project path value before result after ∧ Keeps before after ∧
      SemanticReady after ∧ Available after result ∧ result.free = [] := by
  induction path generalizing value before with
  | nil => exact ⟨value, before, .root, pure_keeps before semantic.ready, semantic, available, closed⟩
  | cons index path ih =>
      cases value with
      | empty => exact ⟨.empty, before, .empty, pure_keeps before semantic.ready, semantic, available, rfl⟩
      | reference => simp [Value.free] at closed
      | node entry edges depth free => exact ordinary_complete path index ih _ before semantic available closed True.intro
      | union entry members depth free =>
          obtain ⟨exposed, middle, head, _, headAvailable, headClosed, ordinary⟩ :=
            SourceEqualityRequiredHead.complete _ before semantic.ready available closed
          obtain ⟨result, after, body, _, _, _, _⟩ := ordinary_complete path index ih exposed middle
            (SourceEqualityRequiredSemanticCache.head head semantic available closed) headAvailable headClosed ordinary
          have trace : Project (index :: path) (.union entry members depth free) before result after := .recursive True.intro head body
          exact ⟨_, _, trace, SourceEqualityProjectionEffects.node trace semantic available closed⟩
      | mu entry originalBody probe originalOrdinary =>
          obtain ⟨exposed, middle, head, _, headAvailable, headClosed, ordinary⟩ :=
            SourceEqualityRequiredHead.complete _ before semantic.ready available closed
          obtain ⟨result, after, body, _, _, _, _⟩ := ordinary_complete path index ih exposed middle
            (SourceEqualityRequiredSemanticCache.head head semantic available closed) headAvailable headClosed ordinary
          have trace : Project (index :: path) (.mu entry originalBody probe originalOrdinary) before result after := .recursive True.intro head body
          exact ⟨_, _, trace, SourceEqualityProjectionEffects.node trace semantic available closed⟩

/-- Forest getPath completes, including its source root union and missing signed child. -/
theorem forest_complete [DecidableEq (EdgeKey Symbol Guard)] (path : List Int)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Values before values) (closed : ClosedValues values) :
    ∃ result after, Forest path values before result after ∧ Keeps before after ∧
      SemanticReady after ∧ Available after result ∧ result.free = [] := by
  cases path with
  | nil =>
      obtain ⟨result, after, union, rest⟩ := SourceEqualityProjectionUnion.complete values before semantic available closed
      exact ⟨result, after, .root union, rest⟩
  | cons index path =>
      cases found : select values index with
      | none => exact ⟨.empty, before, .missing found, pure_keeps before semantic.ready, semantic, InternedProbeProvenance.empty_available before, rfl⟩
      | some value =>
          obtain ⟨result, after, body, rest⟩ := complete path value before semantic
            (available value (select_member found)) (closed value (select_member found))
          exact ⟨result, after, .selected found body, rest⟩

/-- Original closed source construction derives every premise of general projection completion. -/
theorem source [DecidableEq (EdgeKey Symbol Guard)] (expression : InternedNestedConstruction.Syntax Symbol Guard) (path : List Int) :
    ∃ value before result after, InternedFreshOrdinaryConstruction.build expression [] empty = .done value before ∧
      Project path value before result after ∧ Keeps before after ∧ SemanticReady after ∧ Available after result ∧ result.free = [] := by
  obtain ⟨value, before, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  obtain ⟨result, after, trace, rest⟩ := complete path value before
    (SourceEqualityRequiredSemanticCache.constructed expression value before built)
    ((InternedFreshOrdinaryFacts.closed_verified expression).result value before built)
    (InternedFreshOrdinarySourceFreeNames.closed_free_empty expression value before built)
  exact ⟨value, before, result, after, built, trace, rest⟩

end MicroCFTA.SourceEqualityProjectionComplete
