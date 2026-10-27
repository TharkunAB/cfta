import MicroCFTA.SourceEqualityExposureCosts
import MicroCFTA.SourceEqualityProjectionGraph

/-!
# Cost heaps through actual path projections

Completed reads, head reconstruction, and source unions retain semantic
and cost heaps. Projection follows its actual rows and selected children.
The input can be open. These effects do not prove finite projection or
closed output. Those properties have separate source proofs.
-/
namespace MicroCFTA.SourceEqualityProjectionCosts
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityProjectionGraph
open SourceEqualityProjectionRead SourceEqualityProjectionUnion
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- An actual completed row read retains both heaps and resident rows without closedness. -/
theorem read_effects [DecidableEq (EdgeKey Symbol Guard)]
    {value : Value Symbol Guard} {before after : State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    (trace : Read value before edges after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Available before value) :
    Keeps before after ∧ SemanticReady after ∧ CostHeap after ∧ Edges after edges := by
  cases trace with
  | done fuel completed =>
      have checked := SourceEqualityExposureCosts.nodeEdges_verified fuel value before semantic costs available
      exact ⟨by simpa only [completed, MergedSourceExposure.Result.state] using checked.keeps,
        by simpa only [completed, MergedSourceExposure.Result.state] using checked.semantic,
        by simpa only [completed, MergedSourceExposure.Result.state] using checked.costs,
        checked.rows edges after completed⟩

private theorem node_effects [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before edges) :
    Keeps before (run (makeNode edges) before).2 ∧ SemanticReady (run (makeNode edges) before).2 ∧
      CostHeap (run (makeNode edges) before).2 ∧
      Available (run (makeNode edges) before).2 (run (makeNode edges) before).1 := by
  have checked := SourceEqualityOpenOrdinaryHead.node edges before semantic resident
  exact ⟨checked.1, checked.2.1,
    InternedFreshOrdinaryCostHeap.preserve before _ costs (InternedShallowHeap.makeNode_noNewMu edges before),
    checked.2.2.1⟩

/-- Actual head reconstruction retains both heaps and the available rebuilt node. -/
theorem head_effects [DecidableEq (EdgeKey Symbol Guard)]
    {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : SourceEqualityRequiredHead.Head value before result after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Available before value) :
    Keeps before after ∧ SemanticReady after ∧ CostHeap after ∧ Available after result := by
  cases trace with
  | read fuel edges middle exposed rebuilt =>
      have first := read_effects (.done fuel exposed) semantic costs available
      have last := node_effects edges middle first.2.1 first.2.2.1 first.2.2.2
      have sameResult := congrArg Prod.fst rebuilt
      have sameState := congrArg Prod.snd rebuilt
      dsimp only at sameResult sameState
      subst result
      subst after
      exact ⟨first.1.trans last.1, last.2⟩

/-- Ordered actual row reads retain both heaps and the concatenated resident rows. -/
theorem readAll_effects [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {before after : State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    (trace : ReadAll values before edges after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Values before values) :
    Keeps before after ∧ SemanticReady after ∧ CostHeap after ∧ Edges after edges := by
  induction trace with
  | nil => exact ⟨pure_keeps _ semantic.ready, semantic, costs, by simp [Edges]⟩
  | @cons value before rows middle values more after first rest ih =>
      have own := read_effects first semantic costs (available _ List.mem_cons_self)
      have later := ih own.2.1 own.2.2.1
        (fun child member => own.1.available child (available child (List.mem_cons_of_mem _ member)))
      refine ⟨own.1.trans later.1, later.2.1, later.2.2.1, ?_⟩
      intro edge member
      rcases List.mem_append.mp member with first | rest
      · exact InternedEdgeResidency.edge_grows middle after later.1.growth edge (own.2.2.2 edge first)
      · exact later.2.2.2 edge rest

/-- The actual source union retains both heaps without a closed-operand premise. -/
theorem union_effects [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {before after : State Symbol Guard} {result : Value Symbol Guard}
    (trace : Union values before result after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Values before values) :
    Keeps before after ∧ SemanticReady after ∧ CostHeap after ∧ Available after result := by
  cases trace with
  | node read built =>
      have first := readAll_effects read semantic costs available
      have last := node_effects _ _ first.2.1 first.2.2.1 first.2.2.2
      have sameResult := congrArg Prod.fst built
      have sameState := congrArg Prod.snd built
      dsimp only at sameResult sameState
      subst result
      subst after
      exact ⟨first.1.trans last.1, last.2⟩

private def NodeEffects (value : Value Symbol Guard) (before : State Symbol Guard)
    (result : Value Symbol Guard) (after : State Symbol Guard) : Prop :=
  SemanticReady before → CostHeap before → Available before value →
    Keeps before after ∧ SemanticReady after ∧ CostHeap after ∧ Available after result

private def RowsEffects (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (results : List (Value Symbol Guard)) (after : State Symbol Guard) : Prop :=
  SemanticReady before → CostHeap before → Edges before edges →
    Keeps before after ∧ SemanticReady after ∧ CostHeap after ∧ Values after results

private theorem effects [DecidableEq (EdgeKey Symbol Guard)] :
    (∀ path (value : Value Symbol Guard) before result after, Project path value before result after → NodeEffects value before result after) ∧
    (∀ path index (edges : List (EdgeValue Symbol Guard)) before results after,
      ProjectRows path index edges before results after → RowsEffects edges before results after) := by
  have rootCase : ∀ {value : Value Symbol Guard} {state}, NodeEffects value state value state := by
    intro value state semantic costs available
    exact ⟨pure_keeps state semantic.ready, semantic, costs, available⟩
  have emptyCase : ∀ {state}, NodeEffects (.empty : Value Symbol Guard) state .empty state := by
    intro state semantic costs available
    exact ⟨pure_keeps state semantic.ready, semantic, costs, available⟩
  have ordinaryCase : ∀ {path index edges before values middle result after entry depth free},
      ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before values middle →
      Union values middle result after → RowsEffects edges before values middle →
      NodeEffects (.node entry edges depth free) before result after := by
    intro path index edges before values middle result after entry depth free _ union ih semantic costs available
    have rows := ih semantic costs
      (InternedEdgeResidency.resident_edges before semantic.ready.semantic.1.normal.facts.linked _ available.resident)
    have last := union_effects union rows.2.1 rows.2.2.1 rows.2.2.2
    exact ⟨rows.1.trans last.1, last.2⟩
  have recursiveCase : ∀ {original before exposed middle path index result after},
      SourceEqualityRequiredGraph.Recursive original → SourceEqualityRequiredHead.Head original before exposed middle →
      Project (Symbol := Symbol) (Guard := Guard) (index :: path) exposed middle result after →
      NodeEffects exposed middle result after → NodeEffects original before result after := by
    intro original before exposed middle path index result after _ head _ ih semantic costs available
    have first := head_effects head semantic costs available
    have later := ih first.2.1 first.2.2.1 first.2.2.2
    exact ⟨first.1.trans later.1, later.2⟩
  have nilCase : ∀ {state}, RowsEffects ([] : List (EdgeValue Symbol Guard)) state [] state := by
    intro state semantic costs _
    exact ⟨pure_keeps state semantic.ready, semantic, costs, by simp [Values]⟩
  have missingCase : ∀ {edge path index edges before results after}, select edge.children index = none →
      ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before results after →
      RowsEffects edges before results after → RowsEffects (edge :: edges) before results after := by
    intro edge path index edges before results after _ _ ih semantic costs resident
    exact ih semantic costs (fun value member => resident value (List.mem_cons_of_mem _ member))
  have selectedCase : ∀ {edge index child path before result middle edges results after},
      select edge.children index = some child → Project (Symbol := Symbol) (Guard := Guard) path child before result middle →
      ProjectRows path index edges middle results after → NodeEffects child before result middle →
      RowsEffects edges middle results after → RowsEffects (edge :: edges) before (result :: results) after := by
    intro edge index child path before result middle edges results after found _ _ firstIH restIH semantic costs resident
    have first := firstIH semantic costs
      (semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge List.mem_cons_self) child (select_member found))
    have rest := restIH first.2.1 first.2.2.1
      (fun edge present => InternedEdgeResidency.edge_grows before middle first.1.growth edge (resident edge (List.mem_cons_of_mem _ present)))
    refine ⟨first.1.trans rest.1, rest.2.1, rest.2.2.1, ?_⟩
    intro value present
    rcases List.mem_cons.mp present with rfl | tail
    · exact rest.1.available _ first.2.2.2
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

/-- Every actual completed path projection retains both heaps and its available result. -/
theorem project_effects [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : Project path value before result after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Available before value) :
    Keeps before after ∧ SemanticReady after ∧ CostHeap after ∧ Available after result :=
  effects.1 _ _ _ _ _ trace semantic costs available

/-- Every actual completed row projection retains both heaps and all returned values. -/
theorem rows_effects [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {index : Int} {edges : List (EdgeValue Symbol Guard)} {results : List (Value Symbol Guard)}
    {before after : State Symbol Guard} (trace : ProjectRows path index edges before results after)
    (semantic : SemanticReady before) (costs : CostHeap before) (resident : Edges before edges) :
    Keeps before after ∧ SemanticReady after ∧ CostHeap after ∧ Values after results :=
  effects.2 _ _ _ _ _ _ trace semantic costs resident

/-- Forest projection retains both heaps in the root, missing, and selected branches. -/
theorem forest_effects [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : Forest path values before result after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Values before values) :
    Keeps before after ∧ SemanticReady after ∧ CostHeap after ∧ Available after result := by
  cases trace with
  | root union => exact union_effects union semantic costs available
  | missing => exact ⟨pure_keeps _ semantic.ready, semantic, costs, empty_available _⟩
  | selected found body => exact project_effects body semantic costs (available _ (select_member found))

end MicroCFTA.SourceEqualityProjectionCosts
