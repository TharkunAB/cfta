import MicroCFTA.SourceCurrentClassRecursiveValueOrigins
import MicroCFTA.SourceCurrentClassObservationSpines
import MicroCFTA.SourceEqualityProjectionPathDomain

/-!
# First recursive values in an actual selected observation

The selected projection and row read either retain an ordinary source
row or reach a first Mu or union through literal ordinary children.
The path domain excludes a bare reference at the selected endpoint.
Unrelated ordinary children need not be closed.
-/
namespace MicroCFTA.SourceCurrentProjectionRecursiveEntry
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionGraph SourceEqualityProjectionRead SourceEqualityProjectionUnion
open SourceCurrentClassRecursiveValueOrigins (Occurs)
open SourceCurrentClassObservationSpines (ProjectionFrame)
open SourceCurrentPositiveProjectionSourceRoute (Route)
open SourceEqualityProjectionPathDomain (NodeClosed)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Heap" => State Symbol Guard
local notation "Spine" => SourceCurrentProjectionReadSpine.Spine
local notation "Recursive" => SourceEqualityRequiredGraph.Recursive
private theorem signed_lookup {values : List Node} {index : Int} {value : Node}
    (found : select values index = some value) :
    index = Int.ofNat index.toNat ∧ values[index.toNat]? = some value := by
  unfold select at found
  split at found
  · cases found
  · exact ⟨(Int.toNat_of_nonneg (by omega)).symm,found⟩

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- The first recursive value retains the exact remaining selected observation. -/
inductive Entry :
    {path : List Int} → {value : Node} → {before : Heap} → {result : Node} → {after : Heap} →
    Project path value before result after →
    {reader : Heap} → {rows : List Row} → {readAfter : Heap} →
    Read result reader rows readAfter → Nat → Row → List Nat → Node → Prop where
  /-- An empty-path read starts at this recursive value. -/
  | root {value state reader rows readAfter position row}
      {read : Read value reader rows readAfter}
      (recursive : Recursive value)
      (remaining : Spine (Project.root (state := state)) read position row) :
      Entry (Project.root (state := state)) read position row [] value
  /-- The first actual recursive Project retains its Head and body continuation. -/
  | head {value before exposed middle result after index path}
      {recursive : Recursive value}
      {head : SourceEqualityRequiredHead.Head value before exposed middle}
      {body : Project (index :: path) exposed middle result after}
      {reader rows readAfter position row} {read : Read result reader rows readAfter}
      (remaining : Spine (.recursive recursive head body) read position row) :
      Entry (.recursive recursive head body) read position row [] value
  /-- An ordinary step follows the same selected child projection and operand read. -/
  | ordinary {index path entry edges depth free before result after}
      {project : Project (index :: path) (.node entry edges depth free) before result after}
      {reader rows readAfter position row} {read : Read result reader rows readAfter}
      (frame : ProjectionFrame project read position row)
      (childIndex : Nat) (signed : index = Int.ofNat childIndex)
      (chosen : frame.sourceRow.children[childIndex]? = some frame.child)
      {initialPath needle} (rest : Entry frame.call frame.operandRead frame.readIndex row initialPath needle) :
      Entry project read position row (childIndex :: initialPath) needle

/-- The first recursive reader value is the same literal value at the retained child path. -/
theorem occurs {path value before result after} {project : Project path value before result after}
    {reader rows readAfter position row} {read : Read result reader rows readAfter} {initialPath needle}
    (entry : Entry project read position row initialPath needle) : Occurs value initialPath needle ∧ Recursive needle := by
  induction entry with
  | root recursive => exact ⟨.root _,recursive⟩
  | head => exact ⟨.root _,by assumption⟩
  | ordinary frame childIndex signed chosen rest ih =>
    exact ⟨.child frame.sourceIndex childIndex frame.sourceRow frame.child frame.sourceSelected chosen ih.1,ih.2⟩

private theorem ordinary_read {value : Node} (ordinary : Ordinary value) {before rows after}
    (actual : Read value before rows after) : rows = nodeEdges value := by
  cases value with
  | empty | node =>
    cases actual with
    | done fuel completed => exact (MergedSourceExposure.Result.done.inj completed).1.symm
  | reference | union | mu => cases ordinary

private def Law {path} {value : Node} {before result after} (project : Project path value before result after)
    {reader rows readAfter} {position : Nat} {row : Row} (read : Read result reader rows readAfter) : Prop :=
  NodeClosed path value → Route path value row ∨ ∃ initialPath needle, Entry project read position row initialPath needle

set_option maxHeartbeats 1600000 in
private theorem first_law {path value before result after} {project : Project path value before result after}
    {reader rows readAfter position row} {read : Read result reader rows readAfter}
    (remaining : Spine project read position row) : Law (position := position) (row := row) project read := by
  induction remaining with
  | @root value state reader readAfter rows read position row selected =>
    intro domain
    cases value with
    | empty =>
      have same := ordinary_read (value := .empty) trivial read
      simp only [same,nodeEdges,List.getElem?_nil] at selected
      cases selected
    | reference name =>
      simp [NodeClosed,Value.free] at domain
    | node entry edges depth free =>
      have canonical : edges[position]? = some row := by
        simpa only [ordinary_read (value := .node entry edges depth free) trivial read,nodeEdges] using selected
      exact .inl (.root entry edges depth free position row canonical)
    | union entry members depth free =>
      exact .inr ⟨[],_,.root trivial (.root read position row selected)⟩
    | mu entry body depth ordinary =>
      exact .inr ⟨[],_,.root trivial (.root read position row selected)⟩
  | @ordinary path index edges before middle values allRows unionMiddle result after entry depth free
      projects reads built reader rows readAfter read position row selected canonical rawIndex raw
      operandIndex operand operandSelected earlierRows selectedRows laterRows readStart readFinish
      readPrefix operandRead readSuffix parts readIndex readSelected sourceIndex sourceRow child start finish
      sourceSelected childSelected projectPrefix call projectSuffix rest ih =>
    intro domain
    have domainRows : ∀ edge ∈ edges, ∀ child, select edge.children index = some child → NodeClosed path child := by
      simpa only [NodeClosed] using domain
    have childDomain : NodeClosed path child := domainRows sourceRow (List.mem_of_getElem? sourceSelected) child childSelected
    rcases ih childDomain with route | entered
    · exact .inl (.child entry edges depth free sourceIndex sourceRow sourceSelected index child childSelected route)
    · obtain ⟨initialPath,needle,entered⟩ := entered
      let retained : ProjectionFrame (.ordinary (entry := entry) (depth := depth) (free := free) projects (.node reads built)) read position row :=
        ⟨values,middle,allRows,unionMiddle,projects,reads,built,rfl,selected,canonical,rawIndex,raw,
          operandIndex,operand,operandSelected,earlierRows,selectedRows,laterRows,readStart,readFinish,
          readPrefix,operandRead,readSuffix,parts,readIndex,readSelected,sourceIndex,sourceRow,child,start,finish,
          sourceSelected,childSelected,projectPrefix,call,projectSuffix,rest⟩
      exact .inr ⟨index.toNat :: initialPath,needle,
        .ordinary retained index.toNat (signed_lookup childSelected).1 (signed_lookup childSelected).2 entered⟩
  | @recursive original before exposed middle result after index path recursive head body reader rows readAfter read position row rest ih =>
    intro domain
    exact .inr ⟨[],original,.head (recursive := recursive) (head := head) (body := body)
      (.recursive (recursive := recursive) (head := head) (body := body) rest)⟩

/-- Actual selected reads in the path domain derive an ordinary source or their first recursive entry. -/
theorem first {path value before result after} {project : Project path value before result after}
    {reader rows readAfter position row} {read : Read result reader rows readAfter}
    (remaining : Spine project read position row) (domain : NodeClosed path value) :
    Route path value row ∨ ∃ initialPath needle, Entry project read position row initialPath needle :=
  first_law remaining domain

end MicroCFTA.SourceCurrentProjectionRecursiveEntry
