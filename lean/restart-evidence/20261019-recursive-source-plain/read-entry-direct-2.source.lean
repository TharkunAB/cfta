import MicroCFTA.SourceCurrentRecursivePlainRead
import MicroCFTA.SourceCurrentProjectionRecursiveEntry

/-!
# Guard annotations at an exact first recursive entry

The entry retains the selected projection and row read. Ordinary steps use
their exact child projection and operand read. Their prefix and suffix calls
derive the required physical support. Guard heaps restrict backward along
these actual intervals. No changed-input gate or input closedness is required.
-/
namespace MicroCFTA.SourceCurrentRecursiveEntryPlainRead
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionGraph SourceEqualityProjectionRead SourceEqualityProjectionUnion
open SourceEqualityAnnotationLanguage
open SourceCurrentProjectionRecursiveEntry (Entry)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Heap" => State Symbol Guard
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "Guards" => SourceCurrentConstrainedCapGuardHeap.Heap
private theorem guards_before (annotation : Guard → Prop) {before after : Heap}
    (growth : Grows before after) (guards : Guards annotation after) : Guards annotation before := by
  intro key entry body depth ordinary present
  exact guards key entry body depth ordinary (growth.nodeRecords key _ present)

variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem spine_selected {path value before result after}
    {project : Project path value before result after}
    {reader rows readAfter position row} {read : Read result reader rows readAfter}
    (remaining : SourceCurrentProjectionReadSpine.Spine project read position row) :
    rows[position]? = some row := by
  induction remaining <;> assumption

/-- An annotated first recursive entry constrains its exact selected terminal row. -/
theorem entry (annotation : Guard → Prop)
    {path value before result after} {project : Project path value before result after}
    {reader rows readAfter position row} {read : Read result reader rows readAfter} {initialPath needle}
    (located : Entry project read position row initialPath needle)
    (annotated : Annotated annotation needle)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    (guards : Guards annotation before) (readerSemantic : SemanticReady reader)
    (later : Keeps after reader) (readerGuards : Guards annotation reader) :
    annotation row.entry.key.constraint := by
  revert annotated semantic costs available guards readerSemantic later readerGuards
  induction located with
  | root recursive remaining =>
    intro annotated semantic costs available guards readerSemantic later readerGuards
    exact SourceCurrentRecursivePlainRead.project_read annotation .root semantic costs available guards annotated
      _ readerSemantic later readerGuards _ (List.mem_of_getElem? (spine_selected remaining))
  | head remaining =>
    intro annotated semantic costs available guards readerSemantic later readerGuards
    exact SourceCurrentRecursivePlainRead.project_read annotation _ semantic costs available guards annotated
      _ readerSemantic later readerGuards _ (List.mem_of_getElem? (spine_selected remaining))
  | ordinary frame childIndex signed chosen rest ih =>
    intro annotated semantic costs available guards readerSemantic later readerGuards
    have edges := resident_edges _ semantic.ready.semantic.1.normal.facts.linked _ available.resident
    have projectPrefix := SourceEqualityProjectionCosts.rows_effects frame.projectPrefix semantic costs
      (fun edge member => edges edge (List.mem_of_mem_take member))
    have projected := SourceEqualityProjectionCosts.rows_effects frame.projects semantic costs edges
    have readPrefix := SourceEqualityProjectionCosts.readAll_effects frame.readPrefix
      projected.2.1 projected.2.2.1
      (fun value member => projected.2.2.2 value (List.mem_of_mem_take member))
    have childAvailable := projectPrefix.2.1.ready.semantic.1.normal.facts.cached.edges frame.sourceRow.entry.key frame.sourceRow
      (edge_grows _ _ projectPrefix.1.growth frame.sourceRow (edges frame.sourceRow (List.mem_of_getElem? frame.sourceSelected)))
      frame.child (select_member frame.childSelected)
    have call := SourceEqualityProjectionCosts.project_effects frame.call projectPrefix.2.1 projectPrefix.2.2.1 childAvailable
    have suffixEdges : Edges frame.finish _ := by
      intro edge member
      exact edge_grows _ _ (grows_trans projectPrefix.1.growth call.1.growth) edge
        (edges edge (List.mem_of_mem_drop member))
    have suffix := SourceEqualityProjectionCosts.rows_effects frame.projectSuffix call.2.1 call.2.2.1 suffixEdges
    have innerLater : Keeps frame.finish frame.readStart := suffix.1.trans readPrefix.1
    have operandAvailable := readPrefix.1.available frame.operand
      (projected.2.2.2 frame.operand (List.mem_of_getElem? frame.operandSelected))
    have readCall := SourceEqualityProjectionCosts.read_effects frame.operandRead readPrefix.2.1 readPrefix.2.2.1 operandAvailable
    have readSuffix := SourceEqualityProjectionCosts.readAll_effects frame.readSuffix readCall.2.1 readCall.2.2.1
      (fun value member => readCall.1.available value (readPrefix.1.available value
        (projected.2.2.2 value (List.mem_of_mem_drop member))))
    have builtGrowth : Grows frame.unionMiddle _ := by
      have normal := InternedConstructorTemplates.run_correct (makeNode frame.allRows) frame.unionMiddle
        readSuffix.2.1.ready.semantic.1.normal.facts.coherent.valid
      simpa only [frame.built] using normal.2
    have innerGuards := guards_before annotation
      (grows_trans readCall.1.growth (grows_trans readSuffix.1.growth (grows_trans builtGrowth later.growth))) readerGuards
    exact ih annotated projectPrefix.2.1 projectPrefix.2.2.1 childAvailable
      (guards_before annotation (grows_trans call.1.growth innerLater.growth) innerGuards)
      readPrefix.2.1 innerLater innerGuards

end MicroCFTA.SourceCurrentRecursiveEntryPlainRead
