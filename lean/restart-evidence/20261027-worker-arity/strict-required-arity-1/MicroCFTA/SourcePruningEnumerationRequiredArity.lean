import MicroCFTA.SourceCurrentRequiredHeapEffects
import MicroCFTA.SourcePruningEnumerationProbeExposureArity

/-!
# Arity through actual required-child reconstruction

Every kept row copies its original constraint at the same child count.
The proof derives that count from the actual child graph.
Every intermediate heap retains the full edge-record invariant.
-/
namespace MicroCFTA.SourcePruningEnumerationRequiredArity
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityRequiredGraph
open SourcePruningEnumerationArityOrigins (Fits Heap)
variable {Symbol : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

private def Effects (before after : State Symbol Guard) : Prop :=
  Keeps before after ∧ SemanticReady after ∧ CostHeap after ∧ Heap after

/-- Actual ordinary reconstruction retains open semantic heaps, costs, and physical projected arity. -/
theorem node_constructor [DecidableEq (EdgeKey Symbol Guard)]
    (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (semantic : SemanticReady state) (costs : CostHeap state) (fields : Heap state)
    (resident : Edges state edges) :
    Keeps state (run (makeNode edges) state).2 ∧ SemanticReady (run (makeNode edges) state).2 ∧
      CostHeap (run (makeNode edges) state).2 ∧ Heap (run (makeNode edges) state).2 ∧
      Available (run (makeNode edges) state).2 (run (makeNode edges) state).1 := by
  have checked := SourceEqualityOpenOrdinaryHead.node edges state semantic resident
  exact ⟨checked.1, checked.2.1,
    InternedFreshOrdinaryCostHeap.preserve state _ costs (InternedShallowHeap.makeNode_noNewMu edges state),
    SourcePruningEnumerationArityOrigins.node_heap edges state fields,
    checked.2.2.1⟩

/-- Every completed head read derives its actual open result and all physical heap effects. -/
theorem head [DecidableEq (EdgeKey Symbol Guard)]
    {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : SourceEqualityRequiredHead.Head value before result after)
    (semantic : SemanticReady before) (costs : CostHeap before) (fields : Heap before)
    (available : Available before value) :
    Keeps before after ∧ SemanticReady after ∧ CostHeap after ∧ Heap after ∧ Available after result := by
  cases trace with
  | read fuel edges middle exposed rebuilt =>
      have read := SourceEqualityExposureCosts.nodeEdges_verified fuel value before semantic costs available
      have middleSemantic : SemanticReady middle := by simpa only [exposed, MergedSourceExposure.Result.state] using read.semantic
      have middleCosts : CostHeap middle := by simpa only [exposed, MergedSourceExposure.Result.state] using read.costs
      have first : Keeps before middle := by simpa only [exposed, MergedSourceExposure.Result.state] using read.keeps
      have middleFields : Heap middle := by
        simpa only [exposed, MergedSourceExposure.Result.state] using
          SourcePruningEnumerationProbeExposureArity.nodeEdges_heap fuel value before
            semantic.ready.semantic.1.normal.facts fields available
      have checked := node_constructor edges middle middleSemantic middleCosts middleFields (read.rows _ _ exposed)
      have resultEffects : Keeps middle after ∧ SemanticReady after ∧ CostHeap after ∧
          Heap after ∧ Available after result := by simpa only [rebuilt] using checked
      exact ⟨first.trans resultEffects.1, resultEffects.2⟩

private def NodeEffects (value : Value Symbol Guard)
    (before : State Symbol Guard) (result : Value Symbol Guard) (after : State Symbol Guard) : Prop :=
  SemanticReady before → CostHeap before → Heap before → Available before value →
    Effects before after ∧ Available after result

private def ChildrenEffects (values : List (Value Symbol Guard))
    (before : State Symbol Guard) (results : List (Value Symbol Guard)) (after : State Symbol Guard) : Prop :=
  SemanticReady before → CostHeap before → Heap before → Values before values →
    Effects before after ∧ Values after results

private def RowsEffects (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (results : List (EdgeValue Symbol Guard)) (after : State Symbol Guard) : Prop :=
  SemanticReady before → CostHeap before → Heap before → Edges before edges →
    Effects before after ∧ Edges after results

private theorem effects [DecidableEq (EdgeKey Symbol Guard)] :
    (∀ needed (value : Value Symbol Guard) before result after,
      RequireNode needed value before result after → NodeEffects value before result after) ∧
    (∀ entries index (values : List (Value Symbol Guard)) before results after,
      RequireChildren entries index values before results after → ChildrenEffects values before results after) ∧
    (∀ entries (edges : List (EdgeValue Symbol Guard)) before results after,
      RequireRows entries edges before results after → RowsEffects edges before results after) := by
  have identityCase : ∀ {value : Value Symbol Guard} {state}, NodeEffects value state value state := by
    intro value state semantic costs fields available
    exact ⟨⟨pure_keeps state semantic.ready, semantic, costs, fields⟩, available⟩
  have emptyCase : ∀ {entries : List (Int × SourceEqualityNeeded.Needed)} {state},
      entries ≠ [] → NodeEffects (.empty : Value Symbol Guard) state .empty state := by
    intro entries state _ semantic costs fields available
    exact ⟨⟨pure_keeps state semantic.ready, semantic, costs, fields⟩, available⟩
  have ordinaryCase : ∀ {entries edges before rebuilt middle result after entry depth free},
      entries ≠ [] → RequireRows (Symbol := Symbol) (Guard := Guard) entries edges before rebuilt middle →
      run (makeNode rebuilt) middle = (result, after) → RowsEffects edges before rebuilt middle →
      NodeEffects (.node entry edges depth free) before result after := by
    intro entries edges before rebuilt middle result after entry depth free _ _ built ih semantic costs fields available
    have resident := InternedEdgeResidency.resident_edges before semantic.ready.semantic.1.normal.facts.linked _ available.resident
    obtain ⟨⟨first, middleSemantic, middleCosts, middleFields⟩, rows⟩ := ih semantic costs fields resident
    have checked := node_constructor rebuilt middle middleSemantic middleCosts middleFields rows
    have final : Keeps middle after ∧ SemanticReady after ∧ CostHeap after ∧ Heap after ∧ Available after result :=
      by simpa only [built] using checked
    exact ⟨⟨first.trans final.1, final.2.1, final.2.2.1, final.2.2.2.1⟩, final.2.2.2.2⟩
  have recursiveCase : ∀ {entries original before exposed middle result after},
      entries ≠ [] → Recursive original → SourceEqualityRequiredHead.Head original before exposed middle →
      RequireNode (Symbol := Symbol) (Guard := Guard) (.node entries) exposed middle result after →
      NodeEffects exposed middle result after → NodeEffects original before result after := by
    intro entries original before exposed middle result after _ _ trace _ ih semantic costs fields available
    obtain ⟨first, middleSemantic, middleCosts, middleFields, exposedAvailable⟩ := head trace semantic costs fields available
    obtain ⟨⟨kept, finalSemantic, finalCosts, finalFields⟩, resultAvailable⟩ :=
      ih middleSemantic middleCosts middleFields exposedAvailable
    exact ⟨⟨first.trans kept, finalSemantic, finalCosts, finalFields⟩, resultAvailable⟩
  have nilChildren : ∀ {state}, ChildrenEffects ([] : List (Value Symbol Guard)) state [] state := by
    intro state semantic costs fields _
    exact ⟨⟨pure_keeps state semantic.ready, semantic, costs, fields⟩, by simp [Values]⟩
  have unselectedCase : ∀ {entries values before results after value} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = none →
      RequireChildren (Symbol := Symbol) (Guard := Guard) entries (index + 1) values before results after →
      ChildrenEffects values before results after →
      ChildrenEffects (value :: values) before (value :: results) after := by
    intro entries values before results after value index _ _ ih semantic costs fields available
    obtain ⟨effects, resident⟩ := ih semantic costs fields (fun child member => available child (List.mem_cons_of_mem _ member))
    refine ⟨effects, ?_⟩
    intro child member
    rcases List.mem_cons.mp member with rfl | member
    · exact effects.1.available _ (available _ List.mem_cons_self)
    · exact resident child member
  have selectedCase : ∀ {entries needed value before result middle values results after} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = some needed →
      RequireNode (Symbol := Symbol) (Guard := Guard) needed value before result middle →
      RequireChildren (Symbol := Symbol) (Guard := Guard) entries (index + 1) values middle results after →
      NodeEffects value before result middle → ChildrenEffects values middle results after →
      ChildrenEffects (value :: values) before (result :: results) after := by
    intro entries needed value before result middle values results after index _ _ _ firstIH restIH semantic costs fields available
    obtain ⟨⟨first, middleSemantic, middleCosts, middleFields⟩, resultAvailable⟩ :=
      firstIH semantic costs fields (available value List.mem_cons_self)
    obtain ⟨⟨kept, finalSemantic, finalCosts, finalFields⟩, resultsAvailable⟩ :=
      restIH middleSemantic middleCosts middleFields
        (fun child member => first.available child (available child (List.mem_cons_of_mem _ member)))
    refine ⟨⟨first.trans kept, finalSemantic, finalCosts, finalFields⟩, ?_⟩
    intro child member
    rcases List.mem_cons.mp member with rfl | member
    · exact kept.available _ resultAvailable
    · exact resultsAvailable child member
  have nilRows : ∀ {state}, RowsEffects ([] : List (EdgeValue Symbol Guard)) state [] state := by
    intro state semantic costs fields _
    exact ⟨⟨pure_keeps state semantic.ready, semantic, costs, fields⟩, by simp [Edges]⟩
  have rejectedCase : ∀ {entries edges before results after edge},
      SourceEqualityNeeded.fits (.node entries) edge.children.length = false →
      RequireRows (Symbol := Symbol) (Guard := Guard) entries edges before results after →
      RowsEffects edges before results after → RowsEffects (edge :: edges) before results after := by
    intro entries edges before results after edge _ _ ih semantic costs fields resident
    exact ih semantic costs fields (fun original member => resident original (List.mem_cons_of_mem _ member))
  have keptCase : ∀ {entries before values middle result afterEdge edges results after edge},
      SourceEqualityNeeded.fits (.node entries) edge.children.length = true →
      RequireChildren (Symbol := Symbol) (Guard := Guard) entries 0 edge.children before values middle →
      run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle = (result, afterEdge) →
      RequireRows (Symbol := Symbol) (Guard := Guard) entries edges afterEdge results after →
      ChildrenEffects edge.children before values middle → RowsEffects edges afterEdge results after →
      RowsEffects (edge :: edges) before (result :: results) after := by
    intro entries before values middle result afterEdge edges results after edge _ children built _ childIH restIH semantic costs fields resident
    have available : Values before edge.children := semantic.ready.semantic.1.normal.facts.cached.edges
      edge.entry.key edge (resident edge List.mem_cons_self)
    obtain ⟨⟨first, middleSemantic, middleCosts, middleFields⟩, valuesAvailable⟩ := childIH semantic costs fields available
    have checked := SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle middleSemantic.ready valuesAvailable
    have afterSemantic : SemanticReady afterEdge := by
      simpa only [built] using SourceEqualityRequiredSemanticCache.edge edge.entry.key.symbol
        edge.entry.key.constraint values middle middleSemantic valuesAvailable
    have edgeKept : Keeps middle afterEdge := by simpa only [built] using checked.1
    have edgeResident : InternedEdgeResidency.EdgeResident afterEdge result := by simpa only [built] using checked.2.1
    have constructorCosts : CostHeap (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle).2 := middleCosts
    have afterCosts : CostHeap afterEdge := by simpa only [built] using constructorCosts
    have copiedFits : Fits edge.entry.key.constraint values.length := by
      rw [children.length]
      exact fields.edge before semantic.ready.semantic.1.normal.facts.coherent edge (resident edge List.mem_cons_self)
    have afterFields : Heap afterEdge := by
      simpa only [built] using SourcePruningEnumerationArityOrigins.edge_heap
        edge.entry.key.symbol edge.entry.key.constraint values middle middleFields copiedFits
    have growth := (first.trans edgeKept).growth
    obtain ⟨⟨kept, finalSemantic, finalCosts, finalFields⟩, finalRows⟩ :=
      restIH afterSemantic afterCosts afterFields
        (fun original member => InternedEdgeResidency.edge_grows before afterEdge growth original (resident original (List.mem_cons_of_mem _ member)))
    refine ⟨⟨(first.trans edgeKept).trans kept, finalSemantic, finalCosts, finalFields⟩, ?_⟩
    intro original member
    rcases List.mem_cons.mp member with rfl | member
    · exact InternedEdgeResidency.edge_grows afterEdge after kept.growth _ edgeResident
    · exact finalRows original member
  refine ⟨?_, ?_, ?_⟩
  · intro needed value before result after trace
    exact RequireNode.rec
      (motive_1 := fun _ value before result after _ => NodeEffects value before result after)
      (motive_2 := fun _ _ values before results after _ => ChildrenEffects values before results after)
      (motive_3 := fun _ edges before results after _ => RowsEffects edges before results after)
      identityCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) rejectedCase keptCase trace
  · intro entries index values before results after trace
    exact RequireChildren.rec
      (motive_1 := fun _ value before result after _ => NodeEffects value before result after)
      (motive_2 := fun _ _ values before results after _ => ChildrenEffects values before results after)
      (motive_3 := fun _ edges before results after _ => RowsEffects edges before results after)
      identityCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) rejectedCase keptCase trace
  · intro entries edges before results after trace
    exact RequireRows.rec
      (motive_1 := fun _ value before result after _ => NodeEffects value before result after)
      (motive_2 := fun _ _ values before results after _ => ChildrenEffects values before results after)
      (motive_3 := fun _ edges before results after _ => RowsEffects edges before results after)
      identityCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) rejectedCase keptCase trace

/-- Every completed node graph retains semantic heaps, costs, projected arity, and its actual returned value. -/
theorem node [DecidableEq (EdgeKey Symbol Guard)]
    {needed : SourceEqualityNeeded.Needed} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : RequireNode needed value before result after) (semantic : SemanticReady before)
    (costs : CostHeap before) (fields : Heap before) (available : Available before value) :
    Keeps before after ∧ SemanticReady after ∧ CostHeap after ∧ Heap after ∧ Available after result := by
  obtain ⟨⟨kept, ready, finalCosts, finalFields⟩, resident⟩ := effects |>.1 _ _ _ _ _ trace semantic costs fields available
  exact ⟨kept, ready, finalCosts, finalFields, resident⟩

/-- Actual child graphs retain their exact returned positions and all physical heap invariants. -/
theorem children [DecidableEq (EdgeKey Symbol Guard)]
    {entries : List (Int × SourceEqualityNeeded.Needed)} {index : Nat} {values results : List (Value Symbol Guard)}
    {before after : State Symbol Guard} (trace : RequireChildren entries index values before results after)
    (semantic : SemanticReady before) (costs : CostHeap before) (fields : Heap before) (available : Values before values) :
    Keeps before after ∧ SemanticReady after ∧ CostHeap after ∧ Heap after ∧ Values after results := by
  obtain ⟨⟨kept, ready, finalCosts, finalFields⟩, resident⟩ := effects |>.2.1 _ _ _ _ _ _ trace semantic costs fields available
  exact ⟨kept, ready, finalCosts, finalFields, resident⟩

/-- Actual row graphs retain resident rebuilt edges and all physical heap invariants. -/
theorem rows [DecidableEq (EdgeKey Symbol Guard)]
    {entries : List (Int × SourceEqualityNeeded.Needed)} {edges results : List (EdgeValue Symbol Guard)} {before after : State Symbol Guard}
    (trace : RequireRows entries edges before results after) (semantic : SemanticReady before)
    (costs : CostHeap before) (fields : Heap before) (resident : Edges before edges) :
    Keeps before after ∧ SemanticReady after ∧ CostHeap after ∧ Heap after ∧ Edges after results := by
  obtain ⟨⟨kept, ready, finalCosts, finalFields⟩, available⟩ := effects |>.2.2 _ _ _ _ _ trace semantic costs fields resident
  exact ⟨kept, ready, finalCosts, finalFields, available⟩

/-- A completed literal requireAll worker retains costs, projected arity, and exact semantic state. -/
theorem requireAll [DecidableEq (EdgeKey Symbol Guard)]
    (fuel readFuel : Nat) (paths : List (List Int)) (values results : List (Value Symbol Guard)) (before after : State Symbol Guard)
    (done : SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before = .done results after)
    (semantic : SemanticReady before) (costs : CostHeap before) (fields : Heap before) (available : Values before values) :
    Keeps before after ∧ SemanticReady after ∧ CostHeap after ∧ Heap after ∧ Values after results := by
  have trace := (SourceEqualityRequiredExecution.requireAll_execution_iff paths values before results after).mpr ⟨fuel, readFuel, done⟩
  cases compiled : SourceEqualityNeeded.build paths with
  | node entries =>
      simp only [compiled] at trace
      exact children trace semantic costs fields available

end MicroCFTA.SourcePruningEnumerationRequiredArity
