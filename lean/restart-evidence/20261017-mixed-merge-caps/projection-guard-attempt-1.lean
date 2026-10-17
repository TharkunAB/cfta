import MicroCFTA.SourceCurrentConstrainedCapMergeGuardEffects
import MicroCFTA.SourceEqualityProjectionCosts

/-!
# Causal guard heaps through actual signed projections

Actual row exposure retains body-to-probe observations. Projection follows
its literal selected children and returned heaps. Other ordinary siblings
can remain open. No result annotation or future guard heap is assumed.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapProjectionGuard
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceEqualityProjectionRead SourceEqualityProjectionUnion SourceEqualityProjectionGraph
open SourceCurrentConstrainedCapGuardHeap (Heap)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- An actual successful row read preserves the earlier causal guard observations. -/
theorem read (annotation : Guard → Prop)
    {value : Value Symbol Guard} {before after : State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    (actual : Read value before edges after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Available before value) (guards : Heap annotation before) : Heap annotation after := by
  cases actual with
  | done fuel completed =>
      have done : MergedFreshOrdinaryExposure.read fuel value before = .done edges after := by
        simp only [MergedFreshOrdinaryExposure.read, completed]
      exact (SourceCurrentConstrainedCapMergeGuardEffects.read_effect annotation fuel value before
        semantic costs available edges after done).1.guards guards

/-- The actual ordinary node reconstruction adds no new Mu observation. -/
theorem head (annotation : Guard → Prop)
    {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : SourceEqualityRequiredHead.Head value before result after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Available before value) (guards : Heap annotation before) : Heap annotation after := by
  cases actual with
  | read fuel edges middle exposed rebuilt =>
      have first := read annotation (.done fuel exposed) semantic costs available guards
      have retained := SourceCurrentConstrainedCapGuardHeap.preserve annotation middle
        (run (makeNode edges) middle).2 first (InternedShallowHeap.makeNode_noNewMu edges middle)
      simpa only [rebuilt] using retained

/-- Ordered source union reads preserve guard observations at every actual intermediate heap. -/
theorem readAll (annotation : Guard → Prop)
    {values : List (Value Symbol Guard)} {before after : State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    (actual : ReadAll values before edges after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Values before values) (guards : Heap annotation before) : Heap annotation after := by
  induction actual with
  | nil => exact guards
  | @cons value before rows middle values more after first rest ih =>
      have effects := SourceEqualityProjectionCosts.read_effects first semantic costs (available _ List.mem_cons_self)
      exact ih effects.2.1 effects.2.2.1
        (fun child member => effects.1.available child (available child (List.mem_cons_of_mem _ member)))
        (read annotation first semantic costs (available _ List.mem_cons_self) guards)

/-- The complete source union retains the earlier guard heap after its final node request. -/
theorem union (annotation : Guard → Prop)
    {values : List (Value Symbol Guard)} {before after : State Symbol Guard} {result : Value Symbol Guard}
    (actual : Union values before result after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Values before values) (guards : Heap annotation before) : Heap annotation after := by
  cases actual with
  | node rows built =>
      have first := readAll annotation rows semantic costs available guards
      have retained := SourceCurrentConstrainedCapGuardHeap.preserve annotation _ _ first
        (InternedShallowHeap.makeNode_noNewMu _ _)
      simpa only [built] using retained

private def NodePost (annotation : Guard → Prop) (value : Value Symbol Guard) (before after : State Symbol Guard) : Prop :=
  SemanticReady before → CostHeap before → Available before value → Heap annotation before → Heap annotation after

private def RowsPost (annotation : Guard → Prop) (edges : List (EdgeValue Symbol Guard)) (before after : State Symbol Guard) : Prop :=
  SemanticReady before → CostHeap before → Edges before edges → Heap annotation before → Heap annotation after

private theorem all_project (annotation : Guard → Prop) :
    (∀ path (value : Value Symbol Guard) before result after, Project path value before result after → NodePost annotation value before after) ∧
    (∀ path index (edges : List (EdgeValue Symbol Guard)) before results after,
      ProjectRows path index edges before results after → RowsPost annotation edges before after) := by
  have rootCase : ∀ {value : Value Symbol Guard} {state}, NodePost annotation value state state := by
    intro value state _ _ _ guards
    exact guards
  have emptyCase : ∀ {state}, NodePost annotation (.empty : Value Symbol Guard) state state := by
    intro state _ _ _ guards
    exact guards
  have ordinaryCase : ∀ {path index edges before values middle result after entry depth free},
      ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before values middle →
      Union values middle result after → RowsPost annotation edges before middle →
      NodePost annotation (.node entry edges depth free) before after := by
    intro path index edges before values middle result after entry depth free rows combined ih semantic costs available guards
    have resident := InternedEdgeResidency.resident_edges before semantic.ready.semantic.1.normal.facts.linked _ available.resident
    have effects := SourceEqualityProjectionCosts.rows_effects rows semantic costs resident
    exact union annotation combined effects.2.1 effects.2.2.1 effects.2.2.2
      (ih semantic costs resident guards)
  have recursiveCase : ∀ {original before exposed middle path index result after},
      SourceEqualityRequiredGraph.Recursive original → SourceEqualityRequiredHead.Head original before exposed middle →
      Project (Symbol := Symbol) (Guard := Guard) (index :: path) exposed middle result after →
      NodePost annotation exposed middle after → NodePost annotation original before after := by
    intro original before exposed middle path index result after _ exposedHead _ ih semantic costs available guards
    have effects := SourceEqualityProjectionCosts.head_effects exposedHead semantic costs available
    exact ih effects.2.1 effects.2.2.1 effects.2.2.2 (head annotation exposedHead semantic costs available guards)
  have nilCase : ∀ {state}, RowsPost annotation ([] : List (EdgeValue Symbol Guard)) state state := by
    intro state _ _ _ guards
    exact guards
  have missingCase : ∀ {edge path index edges before results after}, select edge.children index = none →
      ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before results after →
      RowsPost annotation edges before after → RowsPost annotation (edge :: edges) before after := by
    intro edge path index edges before results after _ _ ih semantic costs resident guards
    exact ih semantic costs (fun original member => resident original (List.mem_cons_of_mem _ member)) guards
  have selectedCase : ∀ {edge index child path before result middle edges results after},
      select edge.children index = some child → Project (Symbol := Symbol) (Guard := Guard) path child before result middle →
      ProjectRows path index edges middle results after → NodePost annotation child before middle →
      RowsPost annotation edges middle after → RowsPost annotation (edge :: edges) before after := by
    intro edge index child path before result middle edges results after found first _ firstIH restIH semantic costs resident guards
    have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge
      (resident edge List.mem_cons_self) child (select_member found)
    have effects := SourceEqualityProjectionCosts.project_effects first semantic costs available
    exact restIH effects.2.1 effects.2.2.1
      (fun original member => InternedEdgeResidency.edge_grows before middle effects.1.growth original
        (resident original (List.mem_cons_of_mem _ member))) (firstIH semantic costs available guards)
  constructor
  · intro path value before result after actual
    exact Project.rec (motive_1 := fun _ value before _ after _ => NodePost annotation value before after)
      (motive_2 := fun _ _ edges before _ after _ => RowsPost annotation edges before after)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase actual
  · intro path index edges before results after actual
    exact ProjectRows.rec (motive_1 := fun _ value before _ after _ => NodePost annotation value before after)
      (motive_2 := fun _ _ edges before _ after _ => RowsPost annotation edges before after)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase actual

/-- A completed path retains the guard heap through its actual selected descendants. -/
theorem node (annotation : Guard → Prop)
    {path : List Int} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : Project path value before result after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Available before value) (guards : Heap annotation before) : Heap annotation after :=
  (all_project annotation).1 _ _ _ _ _ actual semantic costs available guards

/-- Proper forest paths retain unrelated open siblings without an extra guard premise. -/
theorem forest (annotation : Guard → Prop)
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : Forest path values before result after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Values before values) (guards : Heap annotation before) : Heap annotation after := by
  cases actual with
  | root combined => exact union annotation combined semantic costs available guards
  | missing => exact guards
  | selected found body => exact node annotation body semantic costs (available _ (select_member found)) guards

end MicroCFTA.SourceCurrentConstrainedCapProjectionGuard
