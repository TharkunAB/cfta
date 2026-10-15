import MicroCFTA.SourceEqualityProbeHead
import MicroCFTA.SourceEqualityProjectionEffects

/-!
# Filtered Mu probes through general source path projection

Actual head reads preserve the probe invariant. Ordered projections retain
it at each returned child scope. The final source union reads every operand
and constructs one node without a new Mu.
No complete projection or future output invariant is supplied as a premise.
-/
namespace MicroCFTA.SourceEqualityProbeProjection
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityProjectionGraph
open InternedFreshOrdinaryProbeHeap (Heap)

/-- An actual row read preserves filtered probes in its returned cache. -/
theorem read [DecidableEq (EdgeKey Symbol Guard)]
    {value : Value Symbol Guard} {before after : State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    (trace : SourceEqualityProjectionRead.Read value before edges after) (semantic : SemanticReady before)
    (available : Available before value) (closed : value.free = []) (heap : Heap before) : Heap after := by
  cases trace with
  | done fuel completed =>
      simpa only [completed, MergedSourceExposure.Result.state] using
        SourceEqualityProbeExposure.nodeEdges_heap fuel value before
          semantic.ready.semantic semantic.ready.covered heap available closed

/-- Ordered union operands preserve filtered probes through all actual row reads. -/
theorem readAll [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {before after : State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    (trace : SourceEqualityProjectionUnion.ReadAll values before edges after) (semantic : SemanticReady before)
    (available : Values before values) (closed : ClosedValues values) (heap : Heap before) : Heap after := by
  induction trace with
  | nil => exact heap
  | cons first _ ih =>
      have checked := first.verified semantic (available _ List.mem_cons_self) (closed _ List.mem_cons_self)
      have middleHeap := read first semantic (available _ List.mem_cons_self) (closed _ List.mem_cons_self) heap
      exact ih checked.2.1
        (fun child member => checked.1.available child (available child (List.mem_cons_of_mem _ member)))
        (fun child member => closed child (List.mem_cons_of_mem _ member)) middleHeap

/-- The complete source union retains filtered probes after its row reads and node request. -/
theorem union [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {before after : State Symbol Guard} {result : Value Symbol Guard}
    (trace : SourceEqualityProjectionUnion.Union values before result after) (semantic : SemanticReady before)
    (available : Values before values) (closed : ClosedValues values) (heap : Heap before) : Heap after := by
  cases trace with
  | node rows built =>
      have middleHeap := readAll rows semantic available closed heap
      have final := congrArg Prod.snd built
      dsimp only at final
      rw [← final]
      exact InternedFreshOrdinaryProbeHeap.node _ _ middleHeap

private def NodeLaw (value : Value Symbol Guard) (before after : State Symbol Guard) : Prop :=
  SemanticReady before → Available before value → value.free = [] → Heap before → Heap after

private def RowsLaw (edges : List (EdgeValue Symbol Guard)) (before after : State Symbol Guard) : Prop :=
  SemanticReady before → Edges before edges → ClosedEdges edges → Heap before → Heap after

private theorem effects [DecidableEq (EdgeKey Symbol Guard)] :
    (∀ path (value : Value Symbol Guard) before result after, Project path value before result after → NodeLaw value before after) ∧
    (∀ path index (edges : List (EdgeValue Symbol Guard)) before results after,
      ProjectRows path index edges before results after → RowsLaw edges before after) := by
  have rootCase : ∀ {value : Value Symbol Guard} {state}, NodeLaw value state state := by
    intro value state _ _ _ heap; exact heap
  have emptyCase : ∀ {state}, NodeLaw (.empty : Value Symbol Guard) state state := by
    intro state _ _ _ heap; exact heap
  have ordinaryCase : ∀ {path index edges before values middle result after entry depth free},
      ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before values middle →
      SourceEqualityProjectionUnion.Union values middle result after → RowsLaw edges before middle →
      NodeLaw (.node entry edges depth free) before after := by
    intro path index edges before values middle result after entry depth free trace joined ih semantic available closed heap
    have facts := semantic.ready.semantic.1.normal.facts
    have resident := InternedEdgeResidency.resident_edges before facts.linked _ available.resident
    have closedEdges := MergedColdReaderClosed.node_children_closed before facts entry edges depth free available closed
    have rows := SourceEqualityProjectionEffects.rows trace semantic resident closedEdges
    exact union joined rows.2.1 rows.2.2.1 rows.2.2.2 (ih semantic resident closedEdges heap)
  have recursiveCase : ∀ {original before exposed middle path index result after},
      SourceEqualityRequiredGraph.Recursive original → SourceEqualityRequiredHead.Head original before exposed middle →
      Project (Symbol := Symbol) (Guard := Guard) (index :: path) exposed middle result after →
      NodeLaw exposed middle after → NodeLaw original before after := by
    intro original before exposed middle path index result after _ head _ ih semantic available closed heap
    have first := head.verified semantic.ready available closed
    exact ih (SourceEqualityRequiredSemanticCache.head head semantic available closed) first.2.1 first.2.2.1
      (SourceEqualityProbeHead.head head semantic.ready available closed heap)
  have nilCase : ∀ {state}, RowsLaw ([] : List (EdgeValue Symbol Guard)) state state := by
    intro state _ _ _ heap; exact heap
  have missingCase : ∀ {edge path index edges before results after}, select edge.children index = none →
      ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before results after →
      RowsLaw edges before after → RowsLaw (edge :: edges) before after := by
    intro edge path index edges before results after _ _ ih semantic resident closed heap
    exact ih semantic (fun value member => resident value (List.mem_cons_of_mem _ member))
      (fun value member => closed value (List.mem_cons_of_mem _ member)) heap
  have selectedCase : ∀ {edge index child path before result middle edges results after},
      select edge.children index = some child → Project (Symbol := Symbol) (Guard := Guard) path child before result middle →
      ProjectRows path index edges middle results after → NodeLaw child before middle →
      RowsLaw edges middle after → RowsLaw (edge :: edges) before after := by
    intro edge index child path before result middle edges results after found firstTrace _ firstIH restIH semantic resident closed heap
    have member := select_member found
    have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge List.mem_cons_self) child member
    have childClosed := closed edge List.mem_cons_self child member
    have first := SourceEqualityProjectionEffects.node firstTrace semantic available childClosed
    have middleHeap := firstIH semantic available childClosed heap
    exact restIH first.2.1
      (fun edge present => InternedEdgeResidency.edge_grows before middle first.1.growth edge (resident edge (List.mem_cons_of_mem _ present)))
      (fun edge present => closed edge (List.mem_cons_of_mem _ present)) middleHeap
  constructor
  · intro path value before result after trace
    exact Project.rec (motive_1 := fun _ value before _ after _ => NodeLaw value before after)
      (motive_2 := fun _ _ edges before _ after _ => RowsLaw edges before after)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase trace
  · intro path index edges before results after trace
    exact ProjectRows.rec (motive_1 := fun _ value before _ after _ => NodeLaw value before after)
      (motive_2 := fun _ _ edges before _ after _ => RowsLaw edges before after)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase trace

/-- Every completed general node projection preserves Mu probe filters. -/
theorem node [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : Project path value before result after) (semantic : SemanticReady before) (available : Available before value)
    (closed : value.free = []) (heap : Heap before) : Heap after :=
  (effects).1 _ _ _ _ _ trace semantic available closed heap

/-- Every completed ordered row projection preserves the same probe invariant. -/
theorem rows [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {index : Int} {edges : List (EdgeValue Symbol Guard)} {results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (trace : ProjectRows path index edges before results after) (semantic : SemanticReady before) (resident : Edges before edges)
    (closed : ClosedEdges edges) (heap : Heap before) : Heap after :=
  (effects).2 _ _ _ _ _ _ trace semantic resident closed heap

/-- Forest projection retains filtered probes in its root, missing, and selected branches. -/
theorem forest [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : Forest path values before result after) (semantic : SemanticReady before)
    (available : Values before values) (closed : ClosedValues values) (heap : Heap before) : Heap after := by
  cases trace with
  | root joined => exact union joined semantic available closed heap
  | missing => exact heap
  | selected found body => exact node body semantic (available _ (select_member found)) (closed _ (select_member found)) heap

end MicroCFTA.SourceEqualityProbeProjection
