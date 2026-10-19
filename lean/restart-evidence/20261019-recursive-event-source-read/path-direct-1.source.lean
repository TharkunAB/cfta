import MicroCFTA.SourceCurrentProjectionReadSpine
import MicroCFTA.SourceCurrentClassRecursiveValueOrigins
import MicroCFTA.MergedFreshOrdinaryExposureOrigins
import MicroCFTA.MergedFreshOrdinaryGraphOrigins

/-!
# Full-row path origins at an actual observation reader

Each path step retains an epsilon-origin row and its exact child index.
Actual projection and read intervals supply one later view for all steps.
Literal occurrences prepend their ordinary child path. These receipts do
not assert a completed projection of the whole historical event value.
-/
namespace MicroCFTA.SourceCurrentProjectionPathOrigins
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionGraph SourceEqualityProjectionUnion SourceEqualityProjectionRead
open MergedFreshOrdinaryGraph (Origin)
open SourceCurrentProjectionReadSpine (Spine)
variable {Symbol Guard : Type}
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Heap" => State Symbol Guard
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- Each selected full row has epsilon origins and exact ordered child positions at one view. -/
inductive PathOrigin [DecidableEq (EdgeKey Symbol Guard)] (view : Heap) :
    List Int → Node → Row → Prop where
  /-- An empty path retains the complete row's epsilon origin. -/
  | root {value row} (origin : Origin view [value] row) : PathOrigin view [] value row
  /-- A path step selects the exact natural child of an epsilon-origin row. -/
  | child {value parent child path row} (origin : Origin view [value] parent)
      (index : Nat) (selected : parent.children[index]? = some child)
      (rest : PathOrigin view path child row) :
      PathOrigin view (Int.ofNat index :: path) value row

section Actual
variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem signed_lookup {values : List Node} {index : Int} {value : Node}
    (found : select values index = some value) :
    index = Int.ofNat index.toNat ∧ values[index.toNat]? = some value := by
  unfold select at found
  split at found
  · cases found
  · exact ⟨(Int.toNat_of_nonneg (by omega)).symm,found⟩

private theorem ordinary_origin {value : Node} (ordinary : Ordinary value)
    {view : Heap} {row : Row} (origin : Origin view [value] row) : row ∈ nodeEdges value := by
  cases value with
  | empty => exact (MergedFreshOrdinaryGraph.origin_empty view row origin).elim
  | node entry rows depth free => exact (MergedFreshOrdinaryGraph.origin_node view entry rows depth free row).mp origin
  | reference | union | mu => cases ordinary

private theorem head_ordinary {value result : Node} {before after : Heap}
    (actual : SourceEqualityRequiredHead.Head value before result after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Available before value) : Ordinary result := by
  cases actual with
  | read fuel rows middle exposed built =>
    have phase := SourceEqualityProjectionCosts.read_effects (.done fuel exposed) semantic costs available
    simpa only [built] using SourceEqualityRequiredCache.node_ordinary rows middle
      phase.2.1.ready.semantic.1.normal.facts phase.2.2.2

private theorem head_origin {value result : Node} {before after view : Heap}
    (actual : SourceEqualityRequiredHead.Head value before result after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Available before value) (growth : Grows after view)
    (row : Row) (member : row ∈ nodeEdges result) : Origin view [value] row := by
  cases actual with
  | read fuel rows middle exposed built =>
    have phase := SourceEqualityProjectionCosts.read_effects (.done fuel exposed) semantic costs available
    have rebuilt := SourceEqualityOpenOrdinaryHead.node rows middle phase.2.1 phase.2.2.2
    have physical := EqualityLeafProjectionPhysical.makeNode_edges rows middle
      phase.2.1.ready.semantic.1.normal.facts.coherent
      phase.2.1.ready.semantic.1.normal.facts.linked phase.2.2.2
    rw [built] at physical
    have raw : row ∈ rows :=
      ((EqualityLeafProjectionPhysical.normalized_member middle
        phase.2.1.ready.semantic.1.normal.facts.coherent rows phase.2.2.2 row).mp (physical ▸ member)).1
    have first : Grows middle after := by simpa only [built] using rebuilt.1.growth
    exact MergedFreshOrdinaryExposureOrigins.nodeEdges_origins fuel value before
      semantic.ready.semantic semantic.ready.covered available rows middle exposed view
      (grows_trans first growth) row raw

private theorem spine_law {path value before result after}
    {project : Project (Symbol := Symbol) (Guard := Guard) path value before result after}
    {reader rows readAfter} {read : Read result reader rows readAfter} {position row}
    (spine : Spine project read position row) :
    SemanticReady before → CostHeap before → Available before value →
    SemanticReady reader → CostHeap reader → Keeps after reader →
    ∀ view, Grows readAfter view → PathOrigin view path value row := by
  induction spine with
  | @root value state reader readAfter rows read position row selected =>
    intro semantic costs available readerSemantic readerCosts later view growth
    cases read with
    | done fuel completed =>
      exact .root (MergedFreshOrdinaryExposureOrigins.nodeEdges_origins fuel value reader
        readerSemantic.ready.semantic readerSemantic.ready.covered (later.available value available)
        rows readAfter completed view growth row (List.mem_of_getElem? selected))
  | @ordinary path index sourceEdges before projectedMiddle values allRows unionMiddle result after
      entry depth free projects reads built reader rows readAfter read position row selected canonical rawIndex raw
      operandIndex operand operandSelected earlierRows selectedRows laterRows readStart readFinish
      readPrefix operandRead readSuffix parts readIndex readSelected sourceIndex sourceRow child start finish
      sourceSelected childSelected projectPrefix call projectSuffix rest ih =>
    intro semantic costs available readerSemantic readerCosts later view growth
    have edges := resident_edges before semantic.ready.semantic.1.normal.facts.linked _ available.resident
    have prefix := SourceEqualityProjectionCosts.rows_effects projectPrefix semantic costs
      (fun edge member => edges edge (List.mem_of_mem_take member))
    have projected := SourceEqualityProjectionCosts.rows_effects projects semantic costs edges
    have earlier := SourceEqualityProjectionCosts.readAll_effects readPrefix projected.2.1 projected.2.2.1
      (fun value member => projected.2.2.2 value (List.mem_of_mem_take member))
    have childAvailable := prefix.2.1.ready.semantic.1.normal.facts.cached.edges sourceRow.entry.key sourceRow
      (edge_grows before start prefix.1.growth sourceRow (edges sourceRow (List.mem_of_getElem? sourceSelected)))
      child (select_member childSelected)
    have called := SourceEqualityProjectionCosts.project_effects call prefix.2.1 prefix.2.2.1 childAvailable
    have suffixEdges : Edges finish (sourceEdges.drop (sourceIndex+1)) := by
      intro edge member
      exact edge_grows before finish (grows_trans prefix.1.growth called.1.growth) edge
        (edges edge (List.mem_of_mem_drop member))
    have suffix := SourceEqualityProjectionCosts.rows_effects projectSuffix called.2.1 called.2.2.1 suffixEdges
    have innerLater : Keeps finish readStart := suffix.1.trans earlier.1
    have operandAvailable := earlier.1.available operand
      (projected.2.2.2 operand (List.mem_of_getElem? operandSelected))
    have ownRead := SourceEqualityProjectionCosts.read_effects operandRead earlier.2.1 earlier.2.2.1 operandAvailable
    have remainingReads := SourceEqualityProjectionCosts.readAll_effects readSuffix ownRead.2.1 ownRead.2.2.1
      (fun value member => ownRead.1.available value (earlier.1.available value
        (projected.2.2.2 value (List.mem_of_mem_drop member))))
    have allReads := SourceEqualityProjectionCosts.readAll_effects reads projected.2.1 projected.2.2.1 projected.2.2.2
    have rebuilt := SourceEqualityOpenOrdinaryHead.node allRows unionMiddle allReads.2.1 allReads.2.2.2
    have builtKeeps : Keeps unionMiddle after := by simpa only [built] using rebuilt.1
    have returned : Available after result := by simpa only [built] using rebuilt.2.2.1
    have observed := SourceEqualityProjectionCosts.read_effects read readerSemantic readerCosts
      (later.available result returned)
    have last : Keeps readFinish readAfter := remainingReads.1.trans (builtKeeps.trans (later.trans observed.1))
    have childPath := ih prefix.2.1 prefix.2.2.1 childAvailable earlier.2.1 earlier.2.2.1 innerLater
      view (grows_trans last.growth growth)
    have signed := signed_lookup childSelected
    have step : PathOrigin view (Int.ofNat index.toNat :: path) (.node entry sourceEdges depth free) row :=
      .child ⟨_,.seed List.mem_cons_self,List.mem_of_getElem? sourceSelected⟩ index.toNat signed.2 childPath
    simpa only [←signed.1] using step
  | @recursive original before exposed middle result after index path recursive head body
      reader rows readAfter read position row rest ih =>
    intro semantic costs available readerSemantic readerCosts later view growth
    have first := SourceEqualityProjectionCosts.head_effects head semantic costs available
    have remaining := SourceEqualityProjectionCosts.project_effects body first.2.1 first.2.2.1 first.2.2.2
    have observed := SourceEqualityProjectionCosts.read_effects read readerSemantic readerCosts
      (later.available result remaining.2.2.2)
    have headGrowth : Grows middle view :=
      grows_trans (remaining.1.trans (later.trans observed.1)).growth growth
    have continuation := ih first.2.1 first.2.2.1 first.2.2.2 readerSemantic readerCosts later view growth
    cases continuation with
    | @child value parent child suffix row origin childIndex chosen next =>
      exact .child (head_origin head semantic costs available headGrowth parent
        (ordinary_origin (head_ordinary head semantic costs available) origin)) childIndex chosen next

/-- Actual projection and selected read calls derive the complete path at one retained later view. -/
theorem project_read {path value before result after}
    (project : Project (Symbol := Symbol) (Guard := Guard) path value before result after)
    {reader rows readAfter} (read : Read result reader rows readAfter)
    (position : Nat) (row : Row) (spine : Spine project read position row)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    (readerSemantic : SemanticReady reader) (readerCosts : CostHeap reader) (later : Keeps after reader)
    (view : Heap) (growth : Grows readAfter view) : PathOrigin view path value row :=
  spine_law spine semantic costs available readerSemantic readerCosts later view growth

end Actual

/-- A literal ordinary occurrence prepends its exact child path to an observed continuation. -/
theorem occurs [DecidableEq (EdgeKey (SourceObservations.Label FullSyntax.Formula)
    (SourceSymbolicIndex.Constraint FullSyntax.Formula))]
    {event needle prefix} (occurrence : SourceCurrentClassRecursiveValueOrigins.Occurs event prefix needle)
    {view path row} (continuation : PathOrigin view path needle row) :
    PathOrigin view (prefix.map Int.ofNat ++ path) event row := by
  induction occurrence with
  | root => simpa only [List.map_nil,List.nil_append] using continuation
  | child rowIndex childIndex parent child selected chosen rest ih =>
    simpa only [List.map_cons,List.cons_append] using
      PathOrigin.child ⟨_,.seed List.mem_cons_self,List.mem_of_getElem? selected⟩ childIndex chosen ih

end MicroCFTA.SourceCurrentProjectionPathOrigins
