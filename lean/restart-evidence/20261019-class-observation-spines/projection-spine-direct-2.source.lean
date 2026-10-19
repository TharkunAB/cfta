import MicroCFTA.SourceCurrentProjectionIndexedOrigins
import MicroCFTA.SourceEqualityProjectionCosts

/-!
# Actual projection branches through complete row reads

Each selected row retains its actual terminal read. The read can unfold Mu.
Ordinary steps retain distinct source, projected operand, canonical output
and raw union row indices. Every earlier and suffix uses its actual heap.
The producer uses successful graph effects. It does not require closed inputs.
-/
namespace MicroCFTA.SourceCurrentProjectionReadSpine
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionGraph SourceEqualityProjectionUnion SourceEqualityProjectionRead
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Heap" => State Symbol Guard
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- A selected observed row retains its exact recursive projection and row-read calls. -/
inductive Spine :
    {path : List Int} → {value : Node} → {before : Heap} → {result : Node} → {after : Heap} →
    Project path value before result after →
    {reader : Heap} → {rows : List Row} → {readAfter : Heap} →
    Read result reader rows readAfter → Nat → Row → Prop where
  /-- At an empty path, the literal read can perform recursive unfolding. -/
  | root {value : Node} {state reader readAfter : Heap} {rows : List Row}
      (read : Read value reader rows readAfter) (position : Nat) (row : Row)
      (selected : rows[position]? = some row) : Spine (Project.root (state := state)) read position row
  /-- An ordinary branch retains the actual selected projection and union-read intervals. -/
  | ordinary {path : List Int} {index : Int} {edges : List Row} {before middle : Heap}
      {values : List Node} {allRows : List Row} {unionMiddle : Heap} {result : Node} {after : Heap}
      {entry depth free} {projects : ProjectRows path index edges before values middle}
      {reads : ReadAll values middle allRows unionMiddle}
      {built : run (makeNode allRows) unionMiddle = (result,after)}
      {reader observed readAfter} (read : Read result reader observed readAfter)
      (position : Nat) (row : Row) (selected : observed[position]? = some row)
      (canonical : (nodeEdges result)[position]? = some row)
      (rawIndex : Nat) (raw : allRows[rawIndex]? = some row)
      (operandIndex : Nat) (operand : Node) (operandSelected : values[operandIndex]? = some operand)
      (earlierRows selectedRows laterRows : List Row) (readStart readFinish : Heap)
      (readPrefix : ReadAll (values.take operandIndex) middle earlierRows readStart)
      (operandRead : Read operand readStart selectedRows readFinish)
      (readSuffix : ReadAll (values.drop (operandIndex+1)) readFinish laterRows unionMiddle)
      (parts : allRows = earlierRows ++ selectedRows ++ laterRows)
      (readIndex : Nat) (readSelected : selectedRows[readIndex]? = some row)
      (sourceIndex : Nat) (source : Row) (child : Node) (start finish : Heap)
      (sourceSelected : edges[sourceIndex]? = some source)
      (childSelected : select source.children index = some child)
      (projectPrefix : ProjectRows path index (edges.take sourceIndex) before (values.take operandIndex) start)
      (call : Project path child start operand finish)
      (projectSuffix : ProjectRows path index (edges.drop (sourceIndex+1)) finish (values.drop (operandIndex+1)) middle)
      (rest : Spine call operandRead readIndex row) :
      Spine (.ordinary (entry := entry) (depth := depth) (free := free) projects (.node reads built)) read position row
  /-- A recursive path step retains its actual Head and remaining projection. -/
  | recursive {original : Node} {before exposed middle result after}
      {index : Int} {path : List Int}
      {recursive : SourceEqualityRequiredGraph.Recursive original}
      {head : SourceEqualityRequiredHead.Head original before exposed middle}
      {body : Project (index :: path) exposed middle result after}
      {reader rows readAfter} {read : Read result reader rows readAfter} {position row}
      (rest : Spine body read position row) : Spine (.recursive recursive head body) read position row

private theorem ordinary_read {value : Node} (ordinary : Ordinary value) {before rows after}
    (actual : Read value before rows after) : rows = nodeEdges value := by
  cases value with
  | empty | node =>
    cases actual with
    | done fuel completed => exact (MergedSourceExposure.Result.done.inj completed).1.symm
  | reference | union | mu => cases ordinary

private theorem read_all_member {values before rows after}
    (actual : ReadAll (Symbol := Symbol) (Guard := Guard) values before rows after)
    (row : Row) (member : row ∈ rows) :
    ∃ position value earlier selected later start finish,
      values[position]? = some value ∧
      ReadAll (values.take position) before earlier start ∧
      Read value start selected finish ∧
      ReadAll (values.drop (position+1)) finish later after ∧
      rows = earlier ++ selected ++ later ∧ row ∈ selected := by
  induction actual with
  | nil => cases member
  | @cons value before own middle values more after first rest ih =>
    rcases List.mem_append.mp member with here | later
    · exact ⟨0,value,[],own,more,before,middle,rfl,.nil,first,rest,rfl,here⟩
    · obtain ⟨position,original,earlier,selected,later,start,finish,found,earlier,called,suffix,parts,present⟩ := ih later
      refine ⟨position+1,original,own ++ earlier,selected,later,start,finish,?_,?_,called,?_,?_,present⟩
      · simpa only [List.getElem?_cons_succ] using found
      · simpa only [List.take_succ_cons] using ReadAll.cons first earlier
      · simpa only [Nat.add_assoc,List.drop_succ_cons] using suffix
      · simp only [parts,List.append_assoc]

private def NodeLaw {path value before result after}
    (actual : Project (Symbol := Symbol) (Guard := Guard) path value before result after) : Prop :=
  SemanticReady before → CostHeap before → Available before value →
    ∀ reader rows readAfter (read : Read result reader rows readAfter) position row,
      rows[position]? = some row → Spine actual read position row

private def RowsLaw {path index edges before values after}
    (_actual : ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before values after) : Prop :=
  SemanticReady before → CostHeap before → Edges before edges →
    ∀ position value, values[position]? = some value →
      ∀ reader rows readAfter (read : Read value reader rows readAfter) readIndex row,
        rows[readIndex]? = some row →
        ∃ sourceIndex source child start finish,
        ∃ call : Project path child start value finish,
          edges[sourceIndex]? = some source ∧ select source.children index = some child ∧
          ProjectRows path index (edges.take sourceIndex) before (values.take position) start ∧
          ProjectRows path index (edges.drop (sourceIndex+1)) finish (values.drop (position+1)) after ∧
          Spine call read readIndex row

set_option maxHeartbeats 1600000 in
private theorem project_law {path value before result after}
    (actual : Project (Symbol := Symbol) (Guard := Guard) path value before result after) : NodeLaw actual := by
  refine Project.rec
    (motive_1 := fun _ _ _ _ _ actual => NodeLaw actual)
    (motive_2 := fun _ _ _ _ _ _ actual => RowsLaw actual)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ actual
  · intro value state semantic costs available reader rows readAfter read position row selected
    exact .root read position row selected
  · intro index path state semantic costs available reader rows readAfter read position row selected
    have same := ordinary_read (value := (.empty : Node)) (by trivial) read
    simp [same,nodeEdges] at selected
  · intro index path edges before values middle result after entry depth free projects union ih
      semantic costs available reader observed readAfter read position row selected
    have resident := resident_edges before semantic.ready.semantic.1.normal.facts.linked _ available.resident
    have phase := SourceEqualityProjectionCosts.rows_effects projects semantic costs resident
    cases union with
    | node reads built =>
      have exposed := SourceEqualityProjectionCosts.readAll_effects reads phase.2.1 phase.2.2.1 phase.2.2.2
      have physical := EqualityLeafProjectionPhysical.makeNode_edges _ _
        exposed.2.1.ready.semantic.1.normal.facts.coherent
        exposed.2.1.ready.semantic.1.normal.facts.linked exposed.2.2.2
      rw [built] at physical
      have ordinary : Ordinary result := by
        simpa only [built] using SourceEqualityRequiredCache.node_ordinary _ _
          exposed.2.1.ready.semantic.1.normal.facts exposed.2.2.2
      have canonical : (nodeEdges result)[position]? = some row := by
        simpa only [ordinary_read ordinary read] using selected
      have member : row ∈ nodeEdges result := List.mem_of_getElem? canonical
      have kept := (EqualityLeafProjectionPhysical.normalized_member _
        exposed.2.1.ready.semantic.1.normal.facts.coherent _ exposed.2.2.2 row).mp (physical ▸ member)
      obtain ⟨rawIndex,raw⟩ := List.mem_iff_getElem?.mp kept.1
      obtain ⟨operandIndex,operand,earlierRows,selectedRows,laterRows,readStart,readFinish,
        operandSelected,readPrefix,operandRead,readSuffix,parts,readMember⟩ := read_all_member reads row kept.1
      obtain ⟨readIndex,readSelected⟩ := List.mem_iff_getElem?.mp readMember
      obtain ⟨sourceIndex,source,child,start,finish,call,sourceSelected,childSelected,earlier,suffix,rest⟩ :=
        ih semantic costs resident operandIndex operand operandSelected _ _ _ operandRead readIndex row readSelected
      exact .ordinary read position row selected canonical rawIndex raw operandIndex operand operandSelected
        earlierRows selectedRows laterRows readStart readFinish readPrefix operandRead readSuffix parts readIndex readSelected
        sourceIndex source child start finish sourceSelected childSelected earlier call suffix rest
  · intro original before exposed middle index path result after recursive head body ih
      semantic costs available reader rows readAfter read position row selected
    have phase := SourceEqualityProjectionCosts.head_effects head semantic costs available
    exact .recursive (ih phase.2.1 phase.2.2.1 phase.2.2.2 _ _ _ read position row selected)
  · intro path index state semantic costs resident position value selected
    simp at selected
  · intro edge path index edges before values after absent rest ih semantic costs resident
      position value selected reader rows readAfter read readIndex row readSelected
    obtain ⟨sourceIndex,source,child,start,finish,call,found,chosen,earlier,suffix,spine⟩ :=
      ih semantic costs (fun edge member => resident edge (List.mem_cons_of_mem _ member))
        position value selected _ _ _ read readIndex row readSelected
    refine ⟨sourceIndex+1,source,child,start,finish,call,?_,chosen,?_,?_,spine⟩
    · simpa only [List.getElem?_cons_succ] using found
    · simpa only [List.take_succ_cons] using ProjectRows.missing absent earlier
    · simpa only [Nat.add_assoc,List.drop_succ_cons] using suffix
  · intro edge index child path before result middle edges values after found first rest firstIH restIH
      semantic costs resident position value selected reader rows readAfter read readIndex row readSelected
    have childAvailable := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge
      (resident edge List.mem_cons_self) child (select_member found)
    cases position with
    | zero =>
      have same : result = value := by simpa using selected
      subst value
      exact ⟨0,edge,child,before,middle,first,rfl,found,.nil,rest,
        firstIH semantic costs childAvailable _ _ _ read readIndex row readSelected⟩
    | succ position =>
      have phase := SourceEqualityProjectionCosts.project_effects first semantic costs childAvailable
      obtain ⟨sourceIndex,source,child,start,finish,call,present,chosen,earlier,suffix,spine⟩ :=
        restIH phase.2.1 phase.2.2.1
          (fun edge member => edge_grows before middle phase.1.growth edge (resident edge (List.mem_cons_of_mem _ member)))
          position value (by simpa only [List.getElem?_cons_succ] using selected) _ _ _ read readIndex row readSelected
      refine ⟨sourceIndex+1,source,child,start,finish,call,?_,chosen,?_,?_,spine⟩
      · simpa only [List.getElem?_cons_succ] using present
      · simpa only [List.take_succ_cons] using ProjectRows.selected found first earlier
      · simpa only [Nat.add_assoc,List.drop_succ_cons] using suffix

/-- Actual successful projection and observation derive the full indexed read history, including Mu reads. -/
theorem project {path value before result after}
    (actual : Project (Symbol := Symbol) (Guard := Guard) path value before result after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    {reader rows readAfter} (read : Read result reader rows readAfter)
    (position : Nat) (row : Row) (selected : rows[position]? = some row) : Spine actual read position row :=
  project_law actual semantic costs available _ _ _ read position row selected

end MicroCFTA.SourceCurrentProjectionReadSpine
