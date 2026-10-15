import MicroCFTA.SourceEqualityProjectionGraph

/-!
# Cache effects of complete general path projection

Every intermediate cache follows from the actual row, head, and union
requests. Earlier available values remain in scope through both histories.
-/
namespace MicroCFTA.SourceEqualityProjectionEffects
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityProjectionGraph

private def NodeEffects (value : Value Symbol Guard) (before : State Symbol Guard)
    (result : Value Symbol Guard) (after : State Symbol Guard) : Prop :=
  SemanticReady before → Available before value → value.free = [] →
    Keeps before after ∧ SemanticReady after ∧ Available after result ∧ result.free = []

private def RowsEffects (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (results : List (Value Symbol Guard)) (after : State Symbol Guard) : Prop :=
  SemanticReady before → Edges before edges → ClosedEdges edges →
    Keeps before after ∧ SemanticReady after ∧ Values after results ∧ ClosedValues results

private theorem effects [DecidableEq (EdgeKey Symbol Guard)] :
    (∀ path (value : Value Symbol Guard) before result after, Project path value before result after → NodeEffects value before result after) ∧
    (∀ path index (edges : List (EdgeValue Symbol Guard)) before results after,
      ProjectRows path index edges before results after → RowsEffects edges before results after) := by
  have rootCase : ∀ {value : Value Symbol Guard} {state}, NodeEffects value state value state := by
    intro value state semantic available closed
    exact ⟨pure_keeps state semantic.ready, semantic, available, closed⟩
  have emptyCase : ∀ {state}, NodeEffects (.empty : Value Symbol Guard) state .empty state := by
    intro state semantic available closed
    exact ⟨pure_keeps state semantic.ready, semantic, available, closed⟩
  have ordinaryCase : ∀ {path index edges before values middle result after entry depth free},
      ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before values middle →
      SourceEqualityProjectionUnion.Union values middle result after → RowsEffects edges before values middle →
      NodeEffects (.node entry edges depth free) before result after := by
    intro path index edges before values middle result after entry depth free _ union ih semantic available closed
    have facts := semantic.ready.semantic.1.normal.facts
    have rows := ih semantic (InternedEdgeResidency.resident_edges before facts.linked _ available.resident)
      (MergedColdReaderClosed.node_children_closed before facts entry edges depth free available closed)
    have final := union.verified rows.2.1 rows.2.2.1 rows.2.2.2
    exact ⟨rows.1.trans final.1, final.2.1, final.2.2.1, final.2.2.2.1⟩
  have recursiveCase : ∀ {original before exposed middle path index result after},
      SourceEqualityRequiredGraph.Recursive original → SourceEqualityRequiredHead.Head original before exposed middle →
      Project (Symbol := Symbol) (Guard := Guard) (index :: path) exposed middle result after →
      NodeEffects exposed middle result after → NodeEffects original before result after := by
    intro original before exposed middle path index result after _ head _ ih semantic available closed
    have first := head.verified semantic.ready available closed
    have later := ih (SourceEqualityRequiredSemanticCache.head head semantic available closed) first.2.1 first.2.2.1
    exact ⟨first.1.trans later.1, later.2⟩
  have nilCase : ∀ {state}, RowsEffects ([] : List (EdgeValue Symbol Guard)) state [] state := by
    intro state semantic _ _
    exact ⟨pure_keeps state semantic.ready, semantic, by simp [Values], by simp [ClosedValues]⟩
  have missingCase : ∀ {edge path index edges before results after}, select edge.children index = none →
      ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before results after →
      RowsEffects edges before results after → RowsEffects (edge :: edges) before results after := by
    intro edge path index edges before results after _ _ ih semantic resident closed
    exact ih semantic (fun value member => resident value (List.mem_cons_of_mem _ member))
      (fun value member => closed value (List.mem_cons_of_mem _ member))
  have selectedCase : ∀ {edge index child path before result middle edges results after},
      select edge.children index = some child → Project (Symbol := Symbol) (Guard := Guard) path child before result middle →
      ProjectRows path index edges middle results after → NodeEffects child before result middle →
      RowsEffects edges middle results after → RowsEffects (edge :: edges) before (result :: results) after := by
    intro edge index child path before result middle edges results after found _ _ firstIH restIH semantic resident closed
    have member := select_member found
    have first := firstIH semantic
      (semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge List.mem_cons_self) child member)
      (closed edge List.mem_cons_self child member)
    have rest := restIH first.2.1
      (fun edge present => InternedEdgeResidency.edge_grows before middle first.1.growth edge (resident edge (List.mem_cons_of_mem _ present)))
      (fun edge present => closed edge (List.mem_cons_of_mem _ present))
    refine ⟨first.1.trans rest.1, rest.2.1, ?_, ?_⟩
    · intro value present
      rcases List.mem_cons.mp present with rfl | tail
      · exact rest.1.available _ first.2.2.1
      · exact rest.2.2.1 value tail
    · intro value present
      rcases List.mem_cons.mp present with rfl | tail
      · exact first.2.2.2
      · exact rest.2.2.2 value tail
  constructor
  · intro path value before result after trace
    exact Project.rec (motive_1 := fun _ value before result after _ => NodeEffects value before result after)
      (motive_2 := fun _ _ edges before results after _ => RowsEffects edges before results after)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase trace
  · intro path index edges before results after trace
    exact ProjectRows.rec (motive_1 := fun _ value before result after _ => NodeEffects value before result after)
      (motive_2 := fun _ _ edges before results after _ => RowsEffects edges before results after)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase trace

/-- Every completed node projection retains semantic heaps and its closed available result. -/
theorem node [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : Project path value before result after) : NodeEffects value before result after := effects.1 _ _ _ _ _ trace

/-- Every completed row projection retains the complete closed result forest. -/
theorem rows [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {index : Int} {edges : List (EdgeValue Symbol Guard)}
    {results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (trace : ProjectRows path index edges before results after) : RowsEffects edges before results after := effects.2 _ _ _ _ _ _ trace

end MicroCFTA.SourceEqualityProjectionEffects
