import MicroCFTA.SourceCurrentAllocatedMuRebuild
import MicroCFTA.SourceEqualityProjectionCosts
import MicroCFTA.SourceCurrentRequiredHeapEffects

/-!
# Filtered Mu probes through current open row exposure

Actual stored unfolding derives new filtered probes from its literal build.
Collection retains the exact worklist and canonical fallback. Inputs can
have unrelated open children. Read bounds do not assert completion.
-/
namespace MicroCFTA.SourceCurrentAllocatedProbeExposure
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open InternedNestedConstruction (Outcome)
open MergedFreshOrdinaryExposure
open MergedSourceExposure (Result)
open SourceEqualityRequiredSemanticCache
open InternedFreshOrdinaryProbeHeap (Heap)
open SourceEqualityAnnotationExposure (prepend_state canonical_state)

/-- Bounded collection retains filtered Mu probes with unrelated open inputs. -/
theorem collect_heap [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (state : State Symbol Guard) (semantic : SemanticReady state)
    (heap : Heap state) (seen : List Nat) (pending : List (Value Symbol Guard))
    (inputs : Values state pending) : Heap (collect fuel state seen pending).state := by
  induction fuel generalizing state seen pending with
  | zero => cases pending <;> exact heap
  | succ fuel ih =>
      cases pending with
      | nil => exact heap
      | cons value rest =>
          have available := inputs value List.mem_cons_self
          have restInputs : Values state rest := fun child member => inputs child (List.mem_cons_of_mem _ member)
          cases value with
          | empty => exact ih state semantic heap seen rest restInputs
          | reference => exact heap
          | node entry edges depth free =>
              simpa only [collect, prepend_state] using ih state semantic heap seen rest restInputs
          | union entry members depth free =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [collect, ite_eq_left visited] using ih state semantic heap seen rest restInputs
              · have nextInputs : Values state (members ++ rest) := by
                  intro child member
                  rcases List.mem_append.mp member with first | later
                  · exact available.children child first
                  · exact restInputs child later
                simpa only [collect, ite_eq_right visited] using
                  ih state semantic heap (entry.identity :: seen) (members ++ rest) nextInputs
          | mu entry body depth ordinary =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [collect, ite_eq_left visited] using ih state semantic heap seen rest restInputs
              · obtain ⟨result, after, done, kept, afterSemantic, resultAvailable, _⟩ :=
                  SourceEqualityOpenOrdinaryHead.unfold_complete (.mu entry body depth ordinary) state semantic available
                have retained := SourceEqualityProbeUnfold.unfold
                  (.mu entry body depth ordinary) state semantic.ready.semantic.1 heap available
                have afterHeap : Heap after := by
                  simpa only [done, Outcome.state] using retained
                have nextInputs : Values after (result :: rest) := by
                  intro child member
                  rcases List.mem_cons.mp member with rfl | member
                  · exact resultAvailable
                  · exact kept.available child (restInputs child member)
                simpa only [collect, ite_eq_right visited, done] using
                  ih after afterSemantic afterHeap (entry.identity :: seen) (result :: rest) nextInputs

/-- Actual direct and closure reads retain filtered Mu probes without whole-value closedness. -/
theorem nodeEdges_heap [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (value : Value Symbol Guard) (state : State Symbol Guard)
    (semantic : SemanticReady state) (heap : Heap state) (available : Available state value) :
    Heap (nodeEdges fuel value state).state := by
  have fallback (current : State Symbol Guard) (currentSemantic : SemanticReady current)
      (currentHeap : Heap current) (root : Value Symbol Guard) (rootAvailable : Available current root) :
      Heap (collect fuel current [] [root]).canonical.state := by
    rw [canonical_state]
    exact collect_heap fuel current currentSemantic currentHeap [] [root]
      (by intro child member; simpa only [List.mem_singleton.mp member] using rootAvailable)
  cases value with
  | empty | reference | node => exact heap
  | union => exact fallback state semantic heap _ available
  | mu entry body depth ordinary =>
      obtain ⟨result, after, done, kept, afterSemantic, resultAvailable, _⟩ :=
        SourceEqualityOpenOrdinaryHead.unfold_complete (.mu entry body depth ordinary) state semantic available
      have retained := SourceEqualityProbeUnfold.unfold
        (.mu entry body depth ordinary) state semantic.ready.semantic.1 heap available
      have afterHeap : Heap after := by
        simpa only [done, Outcome.state] using retained
      have closure := fallback after afterSemantic afterHeap (.mu entry body depth ordinary)
        (kept.available _ available)
      cases result with
      | node => simpa only [nodeEdges, done, Result.state] using afterHeap
      | empty | reference | union | mu => simpa only [nodeEdges, done] using closure


open SourceEqualityProjectionRead SourceEqualityProjectionUnion SourceEqualityProjectionGraph
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- A completed read preserves probes at its literal returned heap. -/
theorem read_heap [DecidableEq (EdgeKey Symbol Guard)]
    {value : Value Symbol Guard} {before after : State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    (actual : Read value before edges after) (semantic : SemanticReady before)
    (available : Available before value) (probes : Heap before) : Heap after := by
  cases actual with
  | done fuel completed =>
      simpa only [completed, Result.state] using nodeEdges_heap fuel value before semantic probes available

/-- Actual head reconstruction introduces no additional Mu record. -/
theorem head_heap [DecidableEq (EdgeKey Symbol Guard)]
    {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : SourceEqualityRequiredHead.Head value before result after)
    (semantic : SemanticReady before) (available : Available before value) (probes : Heap before) : Heap after := by
  cases actual with
  | read fuel edges middle exposed rebuilt =>
      have middleProbes := read_heap (.done fuel exposed) semantic available probes
      simpa only [rebuilt] using InternedFreshOrdinaryProbeHeap.node edges middle middleProbes

/-- Ordered reads thread the actual probe heaps through their returned states. -/
theorem readAll_heap [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {before after : State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    (actual : ReadAll values before edges after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Values before values) (probes : Heap before) : Heap after := by
  induction actual with
  | nil => exact probes
  | cons first rest ih =>
      have firstEffects := SourceEqualityProjectionCosts.read_effects first semantic costs (available _ List.mem_cons_self)
      exact ih firstEffects.2.1 firstEffects.2.2.1
        (fun value member => firstEffects.1.available value (available value (List.mem_cons_of_mem _ member)))
        (read_heap first semantic (available _ List.mem_cons_self) probes)

/-- The source union reads its operands before the actual ordinary constructor. -/
theorem union_heap [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {before after : State Symbol Guard} {result : Value Symbol Guard}
    (actual : Union values before result after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Values before values) (probes : Heap before) : Heap after := by
  cases actual with
  | node read built =>
      rename_i edges middle
      have middleProbes := readAll_heap read semantic costs available probes
      simpa only [built] using InternedFreshOrdinaryProbeHeap.node edges middle middleProbes

private def ProjectPreserves (value : Value Symbol Guard) (before after : State Symbol Guard) : Prop :=
  SemanticReady before → CostHeap before → Available before value → Heap before → Heap after

private def RowsPreserves (edges : List (EdgeValue Symbol Guard)) (before after : State Symbol Guard) : Prop :=
  SemanticReady before → CostHeap before → Edges before edges → Heap before → Heap after

private theorem projection_preserves [DecidableEq (EdgeKey Symbol Guard)] :
    (∀ path (value : Value Symbol Guard) before result after,
      Project path value before result after → ProjectPreserves value before after) ∧
    (∀ path index (edges : List (EdgeValue Symbol Guard)) before results after,
      ProjectRows path index edges before results after → RowsPreserves edges before after) := by
  have rootCase : ∀ {value : Value Symbol Guard} {state}, ProjectPreserves value state state := by
    intro value state semantic costs available probes
    exact probes
  have emptyCase : ∀ {state}, ProjectPreserves (.empty : Value Symbol Guard) state state := by
    intro state semantic costs available probes
    exact probes
  have ordinaryCase : ∀ {path index edges before values middle result after entry depth free},
      ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before values middle →
      Union values middle result after → RowsPreserves edges before middle →
      ProjectPreserves (.node entry edges depth free) before after := by
    intro path index edges before values middle result after entry depth free rows union ih semantic costs available probes
    have resident := InternedEdgeResidency.resident_edges before semantic.ready.semantic.1.normal.facts.linked _ available.resident
    have effects := SourceEqualityProjectionCosts.rows_effects rows semantic costs resident
    exact union_heap union effects.2.1 effects.2.2.1 effects.2.2.2 (ih semantic costs resident probes)
  have recursiveCase : ∀ {original before exposed middle path index result after},
      SourceEqualityRequiredGraph.Recursive original → SourceEqualityRequiredHead.Head original before exposed middle →
      Project (Symbol := Symbol) (Guard := Guard) (index :: path) exposed middle result after →
      ProjectPreserves exposed middle after → ProjectPreserves original before after := by
    intro original before exposed middle path index result after _ head _ ih semantic costs available probes
    have effects := SourceEqualityProjectionCosts.head_effects head semantic costs available
    exact ih effects.2.1 effects.2.2.1 effects.2.2.2 (head_heap head semantic available probes)
  have nilCase : ∀ {state}, RowsPreserves ([] : List (EdgeValue Symbol Guard)) state state := by
    intro state semantic costs available probes
    exact probes
  have missingCase : ∀ {edge path index edges before results after}, select edge.children index = none →
      ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before results after →
      RowsPreserves edges before after → RowsPreserves (edge :: edges) before after := by
    intro edge path index edges before results after _ _ ih semantic costs available probes
    exact ih semantic costs (fun value member => available value (List.mem_cons_of_mem _ member)) probes
  have selectedCase : ∀ {edge index child path before result middle edges results after},
      select edge.children index = some child → Project (Symbol := Symbol) (Guard := Guard) path child before result middle →
      ProjectRows path index edges middle results after → ProjectPreserves child before middle →
      RowsPreserves edges middle after → RowsPreserves (edge :: edges) before after := by
    intro edge index child path before result middle edges results after found first _ firstIH restIH semantic costs resident probes
    have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge
      (resident edge List.mem_cons_self) child (select_member found)
    have effects := SourceEqualityProjectionCosts.project_effects first semantic costs available
    exact restIH effects.2.1 effects.2.2.1
      (fun edge member => InternedEdgeResidency.edge_grows before middle effects.1.growth edge (resident edge (List.mem_cons_of_mem _ member)))
      (firstIH semantic costs available probes)
  constructor
  · intro path value before result after actual
    exact Project.rec
      (motive_1 := fun _ value before _ after _ => ProjectPreserves value before after)
      (motive_2 := fun _ _ edges before _ after _ => RowsPreserves edges before after)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase actual
  · intro path index edges before results after actual
    exact ProjectRows.rec
      (motive_1 := fun _ value before _ after _ => ProjectPreserves value before after)
      (motive_2 := fun _ _ edges before _ after _ => RowsPreserves edges before after)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase actual

/-- Actual signed path projection retains probes without a closed input premise. -/
theorem project_heap [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : Project path value before result after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Available before value) (probes : Heap before) : Heap after :=
  projection_preserves.1 _ _ _ _ _ actual semantic costs available probes

/-- Actual row projection follows the original selected positions. -/
theorem projectRows_heap [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {index : Int} {edges : List (EdgeValue Symbol Guard)} {results : List (Value Symbol Guard)}
    {before after : State Symbol Guard} (actual : ProjectRows path index edges before results after)
    (semantic : SemanticReady before) (costs : CostHeap before) (resident : Edges before edges)
    (probes : Heap before) : Heap after :=
  projection_preserves.2 _ _ _ _ _ _ actual semantic costs resident probes

/-- Root, missing, and selected forest branches retain probes at the actual returned heap. -/
theorem forest_heap [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : Forest path values before result after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Values before values) (probes : Heap before) : Heap after := by
  cases actual with
  | root union => exact union_heap union semantic costs available probes
  | missing => exact probes
  | selected found body => exact project_heap body semantic costs (available _ (select_member found)) probes

end MicroCFTA.SourceCurrentAllocatedProbeExposure
