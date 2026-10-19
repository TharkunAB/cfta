import MicroCFTA.SourceCurrentClassObservationSpines
import MicroCFTA.MergedFreshOrdinaryExposureOrigins

/-!
# Source rows at an actual recursive observation

An empty residual retains the selected terminal read's epsilon origin.
A nonempty residual retains its actual Head, the selected complete Head
row, and that row's exact child projection and operand read. The source
row can differ from the final selected row. No closedness or future
completion is required. This result does not project a whole event value.
-/
namespace MicroCFTA.SourceCurrentRecursiveObservationReadOrigins
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionGraph SourceEqualityProjectionRead SourceEqualityProjectionUnion
open SourceEqualityRequiredHead (Head)
open SourceCurrentClassObservationSpines (ProjectionFrame)
open SourceCurrentProjectionReadSpine (Spine)
open MergedFreshOrdinaryGraph (Origin)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Heap" => State Symbol Guard
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "Recursive" => SourceEqualityRequiredGraph.Recursive

private theorem signed_lookup {values : List Node} {index : Int} {value : Node}
    (found : select values index = some value) :
    index = Int.ofNat index.toNat ∧ values[index.toNat]? = some value := by
  unfold select at found
  split at found
  · cases found
  · exact ⟨(Int.toNat_of_nonneg (by omega)).symm,found⟩

private theorem incompatible {value : Node} (recursive : Recursive value) (ordinary : Ordinary value) : False := by
  cases value <;> contradiction

variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem head_ordinary {value result : Node} {before after : Heap}
    (actual : Head value before result after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Available before value) : Ordinary result := by
  cases actual with
  | read fuel rows middle exposed built =>
    have phase := SourceEqualityProjectionCosts.read_effects (.done fuel exposed) semantic costs available
    have ordinary := SourceEqualityRequiredCache.node_ordinary rows middle
      phase.2.1.ready.semantic.1.normal.facts phase.2.2.2
    simpa only [built] using ordinary

private theorem head_row {value result : Node} {before after : Heap}
    (actual : Head value before result after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Available before value)
    (rowIndex : Nat) (row : Row) (selected : (nodeEdges result)[rowIndex]? = some row) :
    ∃ (fuel : Nat) (rows : List Row) (middle : Heap) (rawIndex : Nat),
      MergedFreshOrdinaryExposure.nodeEdges fuel value before = .done rows middle ∧
      run (makeNode rows) middle = (result,after) ∧ rows[rawIndex]? = some row ∧
      Origin after [value] row := by
  cases actual with
  | read fuel rows middle exposed built =>
    have phase := SourceEqualityProjectionCosts.read_effects (.done fuel exposed) semantic costs available
    have rebuilt := SourceEqualityOpenOrdinaryHead.node rows middle phase.2.1 phase.2.2.2
    have physical := EqualityLeafProjectionPhysical.makeNode_edges rows middle
      phase.2.1.ready.semantic.1.normal.facts.coherent
      phase.2.1.ready.semantic.1.normal.facts.linked phase.2.2.2
    rw [built] at physical
    have member : row ∈ rows :=
      ((EqualityLeafProjectionPhysical.normalized_member middle
        phase.2.1.ready.semantic.1.normal.facts.coherent rows phase.2.2.2 row).mp
        (physical ▸ List.mem_of_getElem? selected)).1
    obtain ⟨rawIndex,raw⟩ := List.mem_iff_getElem?.mp member
    have growth : Grows middle after := by simpa only [built] using rebuilt.1.growth
    have origin := MergedFreshOrdinaryExposureOrigins.nodeEdges_origins fuel value before
      semantic.ready.semantic semantic.ready.covered available rows middle exposed after growth row member
    exact ⟨fuel,rows,middle,rawIndex,exposed,built,raw,origin⟩

/-- An actual recursive observation retains its terminal origin or its exact selected Head-row continuation. -/
theorem project_read {path : List Int} {needle result : Node} {before after : Heap}
    (project : Project path needle before result after) (recursive : Recursive needle)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before needle)
    {reader rows readAfter} (read : Read result reader rows readAfter)
    (position : Nat) (row : Row) (remaining : Spine project read position row)
    (readerSemantic : SemanticReady reader) (later : Keeps after reader) :
    (path = [] ∧ Origin readAfter [needle] row) ∨
      ∃ index suffix entry edges depth free headAfter,
      ∃ head : Head needle before (.node entry edges depth free) headAfter,
      ∃ body : Project (index :: suffix) (.node entry edges depth free) headAfter result after,
      ∃ frame : ProjectionFrame body read position row,
        path = index :: suffix ∧ HEq project (Project.recursive recursive head body) ∧
        ∃ (fuel : Nat) (headRows : List Row) (headMiddle : Heap) (rawIndex childIndex : Nat),
          MergedFreshOrdinaryExposure.nodeEdges fuel needle before = .done headRows headMiddle ∧
          run (makeNode headRows) headMiddle = (.node entry edges depth free,headAfter) ∧
          headRows[rawIndex]? = some frame.sourceRow ∧
          Origin headAfter [needle] frame.sourceRow ∧
          index = Int.ofNat childIndex ∧ frame.sourceRow.children[childIndex]? = some frame.child := by
  cases remaining with
  | @root value state reader readAfter rows read position row selected =>
    have resident := later.available _ available
    cases read with
    | done fuel completed =>
      exact .inl ⟨rfl,MergedFreshOrdinaryExposureOrigins.nodeEdges_origins fuel _ reader
        readerSemantic.ready.semantic readerSemantic.ready.covered resident rows readAfter completed
        readAfter (grows_refl _) row (List.mem_of_getElem? selected)⟩
  | ordinary => cases recursive
  | @recursive original before exposed middle result after index path rec head body
      reader rows readAfter read position row rest =>
    have ordinary := head_ordinary head semantic costs available
    cases rest with
    | @ordinary suffix childPosition sourceEdges headAfter projectedMiddle values allRows unionMiddle result after
        sourceEntry sourceDepth sourceFree projects reads built reader rows readAfter read position row selected
        canonical rawIndex raw operandIndex operand operandSelected earlierRows selectedRows laterRows readStart readFinish
        readPrefix operandRead readSuffix parts readIndex readSelected sourceIndex sourceRow child start finish
        sourceSelected childSelected projectPrefix call projectSuffix childRest =>
      let frame : ProjectionFrame (.ordinary (entry := sourceEntry) (depth := sourceDepth)
          (free := sourceFree) projects (.node reads built)) read position row :=
        ⟨values,projectedMiddle,allRows,unionMiddle,projects,reads,built,rfl,selected,canonical,rawIndex,raw,
          operandIndex,operand,operandSelected,earlierRows,selectedRows,laterRows,readStart,readFinish,
          readPrefix,operandRead,readSuffix,parts,readIndex,readSelected,sourceIndex,sourceRow,child,start,finish,
          sourceSelected,childSelected,projectPrefix,call,projectSuffix,childRest⟩
      obtain ⟨fuel,headRows,headMiddle,headRawIndex,readDone,made,headSelected,origin⟩ :=
        head_row head semantic costs available sourceIndex sourceRow sourceSelected
      have signed := signed_lookup childSelected
      exact .inr ⟨index,path,sourceEntry,sourceEdges,sourceDepth,sourceFree,middle,head,
        .ordinary projects (.node reads built),frame,rfl,HEq.rfl,fuel,headRows,headMiddle,headRawIndex,
        index.toNat,readDone,made,headSelected,origin,signed.1,signed.2⟩
    | recursive => exact False.elim (incompatible (by assumption) ordinary)

end MicroCFTA.SourceCurrentRecursiveObservationReadOrigins
