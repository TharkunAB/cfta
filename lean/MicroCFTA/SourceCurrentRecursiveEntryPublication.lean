import MicroCFTA.SourceCurrentRecursiveEntryObservation
import MicroCFTA.SourceCurrentRequiredPublicationHistory

/-!
# Actual publication prefixes at the first recursive observation

The selected Entry retains one supported remaining observation.
Its prefix history follows actual ordinary projection prefixes only.
Physical Keeps across the outer reader gap supplies no history.
-/
namespace MicroCFTA.SourceCurrentRecursiveEntryPublication
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionGraph SourceEqualityProjectionRead
open SourceCurrentProjectionRecursiveEntry (Entry)
open SourceCurrentRecursiveEntryObservation (Observation)
open SourceCurrentNativeMuPublication (History)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Heap" => State Symbol Guard
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "Guards" => SourceCurrentConstrainedCapGuardHeap.Heap Plain

private theorem guards_before {before after : Heap} (growth : Grows before after)
    (guards : Guards after) : Guards before := by
  intro key entry body depth ordinary found
  exact guards key entry body depth ordinary (growth.nodeRecords key _ found)

variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem selected {path : List Int} {value : Node} {before : Heap} {result : Node} {after : Heap}
    {project : Project path value before result after}
    {reader rows readAfter position row} {read : Read result reader rows readAfter}
    (spine : SourceCurrentProjectionReadSpine.Spine project read position row) : rows[position]? = some row := by
  induction spine <;> assumption

/-- Exact Entry execution derives its supported observation and actual prefix publication history. -/
theorem entry {path value before result after} {project : Project path value before result after}
    {reader rows readAfter position row} {read : Read result reader rows readAfter} {initialPath needle}
    (located : Entry project read position row initialPath needle)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    (guards : Guards before) (readerSemantic : SemanticReady reader) (readerCosts : CostHeap reader)
    (later : Keeps after reader) (readerGuards : Guards reader) :
    ∃ observation : Observation needle row,
      path = initialPath.map Int.ofNat ++ observation.path ∧
      Keeps before observation.before ∧ Keeps observation.reader reader ∧
      Nonempty (History before observation.before) := by
  revert semantic costs available guards readerSemantic readerCosts later readerGuards
  induction located with
  | @root value state reader rows readAfter position row read recursive spine =>
    intro semantic costs available guards readerSemantic readerCosts later readerGuards
    refine ⟨⟨[],state,value,state,reader,rows,readAfter,position,.root,read,selected spine,spine,recursive,
      semantic,costs,available,guards,readerSemantic,readerCosts,later.available value available,later,readerGuards⟩,
      rfl,pure_keeps _ semantic.ready,pure_keeps _ readerSemantic.ready,⟨.refl _⟩⟩
  | @head value before exposed middle result after index path recursive head body reader rows readAfter position row read spine =>
    intro semantic costs available guards readerSemantic readerCosts later readerGuards
    have effects := SourceEqualityProjectionCosts.project_effects (.recursive recursive head body) semantic costs available
    exact ⟨⟨index::path,before,result,after,reader,rows,readAfter,position,.recursive recursive head body,read,
      selected spine,spine,recursive,semantic,costs,available,guards,readerSemantic,readerCosts,
      later.available result effects.2.2.2,later,readerGuards⟩,
      rfl,pure_keeps _ semantic.ready,pure_keeps _ readerSemantic.ready,⟨.refl _⟩⟩
  | @ordinary index path sourceEntry sourceEdges depth free before result after project reader rows readAfter position row read frame childIndex signed chosen initialPath needle rest ih =>
    intro semantic costs available guards readerSemantic readerCosts later readerGuards
    have edges := resident_edges _ semantic.ready.semantic.1.normal.facts.linked _ available.resident
    have projectPrefix := SourceEqualityProjectionCosts.rows_effects frame.projectPrefix semantic costs
      (fun edge member => edges edge (List.mem_of_mem_take member))
    have projected := SourceEqualityProjectionCosts.rows_effects frame.projects semantic costs edges
    have readPrefix := SourceEqualityProjectionCosts.readAll_effects frame.readPrefix projected.2.1 projected.2.2.1
      (fun value member => projected.2.2.2 value (List.mem_of_mem_take member))
    have childAvailable := projectPrefix.2.1.ready.semantic.1.normal.facts.cached.edges frame.sourceRow.entry.key frame.sourceRow
      (edge_grows _ _ projectPrefix.1.growth frame.sourceRow (edges frame.sourceRow (List.mem_of_getElem? frame.sourceSelected)))
      frame.child (select_member frame.childSelected)
    have call := SourceEqualityProjectionCosts.project_effects frame.call projectPrefix.2.1 projectPrefix.2.2.1 childAvailable
    have suffixEdges : Edges frame.finish (sourceEdges.drop (frame.sourceIndex+1)) := by
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
    have allReads := SourceEqualityProjectionCosts.readAll_effects frame.reads projected.2.1 projected.2.2.1 projected.2.2.2
    have builtKeeps : Keeps frame.unionMiddle after := by
      simpa only [frame.built] using
        (SourceEqualityOpenOrdinaryHead.node frame.allRows frame.unionMiddle allReads.2.1 allReads.2.2.2).1
    have readerLater : Keeps frame.readStart reader := readCall.1.trans (readSuffix.1.trans (builtKeeps.trans later))
    have innerGuards := guards_before readerLater.growth readerGuards
    obtain ⟨observation,splitPath,first,last,⟨innerHistory⟩⟩ := ih projectPrefix.2.1 projectPrefix.2.2.1 childAvailable
      (guards_before (call.1.trans innerLater).growth innerGuards) readPrefix.2.1 readPrefix.2.2.1 innerLater innerGuards
    obtain ⟨initialHistory⟩ := SourceCurrentRequiredPublicationHistory.projectRows frame.projectPrefix semantic costs
      (fun edge member => edges edge (List.mem_of_mem_take member))
    refine ⟨observation,?_,projectPrefix.1.trans first,last.trans readerLater,⟨.trans initialHistory innerHistory⟩⟩
    simp only [List.map_cons,List.cons_append]
    rw [signed,splitPath]

end MicroCFTA.SourceCurrentRecursiveEntryPublication
