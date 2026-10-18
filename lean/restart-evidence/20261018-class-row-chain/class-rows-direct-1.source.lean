import MicroCFTA.SourceCurrentClassFoldGuardOrigins
import MicroCFTA.SourceCurrentSharedEditChildLineage
import MicroCFTA.SourceCurrentClassPassPhaseLineage
import MicroCFTA.SourceCurrentParentRowWriterLineage
import MicroCFTA.SourceCurrentNativeQueryRowOrigins
import MicroCFTA.SourceCurrentRecursiveHeadRowOrigins

/-!
# Individual row chains through actual class edits

Each surviving row retains its exact source row and actual reconstruction.
Ordered child calls remain attached to each ordinary reconstruction.
The chain follows the literal class right fold at the same forest index.
Native queries and recursive Head exposure retain their actual origin events.
-/
namespace MicroCFTA.SourceCurrentClassFoldRowOrigins
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceEqualityEdits SourceEqualityEditLeafPaths SourceCurrentEditDomains
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentAllocatedSharedEditGraph
open SourceCurrentAllocatedSharedEditEffects
open SourceCurrentNativeEdgeWriterGrowth (History)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "SharedReady" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Inventory" => SourceCurrentAllocatedNativeInventoryState.Inventory
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Edge" => EdgeValue Symbol Guard
private theorem propagate_selected (values : List (Value Symbol Guard)) (index : Nat)
    (value : Value Symbol Guard) (selected : (EqualityLeafProjectionRuntimeEmpty.propagate values)[index]? = some value)
    (row : EdgeValue Symbol Guard) (member : row ∈ nodeEdges value) :
    EqualityLeafProjectionRuntimeEmpty.propagate values = values := by
  by_cases test : values.any (fun value => value.referenceOf == .empty) = true
  · have erased : value ∈ values.map (fun _ => (Value.empty : Value Symbol Guard)) := by
      simpa only [EqualityLeafProjectionRuntimeEmpty.propagate,test,ite_true,EqualityLeafProjectionRuntimeEmpty.erase]
        using List.mem_of_getElem? selected
    obtain ⟨original,present,same⟩ := List.mem_map.mp erased
    cases same
    cases member
  · simp [EqualityLeafProjectionRuntimeEmpty.propagate,test]

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- A literal input contains this complete source row. -/
def Original (value : Value Symbol Guard) (row : Edge) : Prop := row ∈ nodeEdges value

/-- An ordinary reconstruction retains its exact row source and ordered child reads. -/
def Rebuild (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (base : Heap)
    {record originals entries edges before rebuilt middle}
    (actual : EditRows (width := width) record originals entries edges before rebuilt middle)
    (source result : Edge) : Prop :=
  ∃ index start rowMiddle values rowHeap startInventory middleInventory first rowMemos rowFinal,
  ∃ earlier : EditRows record originals entries (edges.take index) before (rebuilt.take index) start,
  ∃ call : EditChildren record originals entries 0 source.children start values rowMiddle,
    edges[index]? = some source ∧ rebuilt[index]? = some result ∧
    RowsReads formulas solver base earlier first rowMemos ∧
    ChildrenReads formulas solver base call rowMemos rowFinal ∧
    EndpointMemoGateTrace.Valid start.checked.native.machine.heap rowMemos ∧
    run (makeEdge source.entry.key.symbol source.entry.key.constraint values)
      rowMiddle.checked.native.machine.heap = (result,rowHeap) ∧
    result.entry.key.symbol = source.entry.key.symbol ∧
    result.entry.key.constraint = source.entry.key.constraint ∧ result.children = values ∧
    SharedReady formulas solver startInventory record originals base start ∧
    SharedReady formulas solver middleInventory record originals base rowMiddle ∧
    History start.checked ∧ History rowMiddle.checked ∧
    (∀ childIndex child, values[childIndex]? = some child →
      SourceCurrentSharedEditChildLineage.Slice formulas solver base record originals entries 0
        source.children start values rowMiddle rowMemos rowFinal childIndex child)

/-- A leaf source retains its exact target query and the selected full row. -/
def LeafSource (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {record originals path input before result after}
    (actual : SourceCurrentAllocatedSharedTargetLeaf.Leaf (width := width)
      record originals path input before result after) (row : Edge) : Prop :=
  ∃ (memos final : Memos),
    SourceCurrentAllocatedSharedTargetLeaf.Reads formulas solver actual memos final ∧
    ∃ target middle forceInventory next base,
      SourceCurrentAllocatedSharedTargetForce.Receipt formulas solver forceInventory record originals base path
        before target middle memos final ∧
      SourceCurrentAllocatedTargetQuery.Receipt formulas solver next target input middle.checked result after.checked final ∧
      after = SourceCurrentAllocatedSharedTargetState.advance middle after.checked ∧
      ∃ rowIndex, (nodeEdges result)[rowIndex]? = some row ∧
        SourceCurrentNativeQueryRowOrigins.RowOrigin after.checked
          ⟨IntersectionEmptyDomain.emptyDomain,target,input⟩ result rowIndex row

/-- A root field event occurs in the exact node edit that returns it. -/
inductive NodeEvent (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (row : Edge) :
    {record : Record} → {originals : List (Value Symbol Guard)} → {edits : Edits EqualityNormalize.Path} →
    {input : Value Symbol Guard} → {before : SharedState width} → {result : Value Symbol Guard} →
    {after : SharedState width} → EditNode record originals edits input before result after → Prop where
  /-- An actual leaf query supplies its returned row field. -/
  | leaf {record originals path input before result after}
      {actual : SourceCurrentAllocatedSharedTargetLeaf.Leaf record originals path input before result after}
      (source : LeafSource formulas solver actual row) : NodeEvent formulas solver row (.leaf actual)
  /-- A selected exposed row supplies its field before the below edit. -/
  | exposed {record originals entries original before exposed heap value after}
      {recursive : SourceEqualityRequiredGraph.Recursive original}
      {head : SourceEqualityRequiredHead.Head original before.checked.native.machine.heap exposed heap}
      {body : EditNode record originals (.editBelow entries) exposed (advanceHeap before heap) value after}
      {memos current : Memos} (read : SourceCurrentRequiredQueryMemos.HeadReads head memos current)
      (origins : SourceCurrentRecursiveHeadRowOrigins.HeadRows original before.checked.native.machine.heap exposed heap)
      (source : row ∈ nodeEdges exposed) : NodeEvent formulas solver row (.recursive recursive head body)
  /-- A later root field event remains inside the same actual Head branch. -/
  | recursive {record originals entries original before exposed heap value after}
      {recursive : SourceEqualityRequiredGraph.Recursive original}
      {head : SourceEqualityRequiredHead.Head original before.checked.native.machine.heap exposed heap}
      {body : EditNode record originals (.editBelow entries) exposed (advanceHeap before heap) value after}
      (source : NodeEvent formulas solver row body) : NodeEvent formulas solver row (.recursive recursive head body)

/-- Actual leaf reads derive a full-field source without a caller-supplied row law. -/
theorem leaf_source {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {record originals path input before result after memos final}
    {actual : SourceCurrentAllocatedSharedTargetLeaf.Leaf (width := width) record originals path input before result after}
    (reads : SourceCurrentAllocatedSharedTargetLeaf.Reads formulas solver actual memos final)
    (history : History before.checked) (closed : input.free = [])
    (row : EdgeValue Symbol Guard) (selected : row ∈ nodeEdges result) :
    LeafSource formulas solver actual row := by
  obtain ⟨index,present⟩ := List.mem_iff_getElem?.mp selected
  obtain ⟨target,middle,forceInventory,next,base,force,query,same,_,origin⟩ :=
    SourceCurrentNativeQueryRowOrigins.leaf reads history closed index row present
  exact ⟨memos,final,reads,target,middle,forceInventory,next,base,force,query,same,index,present,origin⟩

/-- Each row flow refers to its literal node execution. -/
inductive NodeFlow (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (base : Heap) :
    {record : Record} → {originals : List (Value Symbol Guard)} → {edits : Edits EqualityNormalize.Path} →
    {input : Value Symbol Guard} → {before : SharedState width} → {result : Value Symbol Guard} →
    {after : SharedState width} → EditNode record originals edits input before result after → Edge → Edge → Prop where
  /-- A leaf row starts at its exact native result. -/
  | leaf {record originals path input before result after}
      {actual : SourceCurrentAllocatedSharedTargetLeaf.Leaf record originals path input before result after}
      (row : Edge) : NodeFlow formulas solver base (.leaf actual) row row
  /-- An ordinary node retains its exact captured row reconstruction. -/
  | node {record originals entries edges before rebuilt middle value heap entry depth free}
      {rows : EditRows record originals entries edges before rebuilt middle}
      {built : run (makeNode rebuilt) middle.checked.native.machine.heap = (value,heap)}
      {source row : Edge} (receipt : Rebuild formulas solver base rows source row) :
      NodeFlow formulas solver base (.node (entry := entry) (depth := depth) (free := free) rows built) source row
  /-- Recursive exposure retains the exact later below-edit row flow. -/
  | recursive {record originals entries original before exposed heap value after}
      {recursive : SourceEqualityRequiredGraph.Recursive original}
      {head : SourceEqualityRequiredHead.Head original before.checked.native.machine.heap exposed heap}
      {body : EditNode record originals (.editBelow entries) exposed (advanceHeap before heap) value after}
      {source row : Edge} (flow : NodeFlow formulas solver base body source row) :
      NodeFlow formulas solver base (.recursive recursive head body) source row

private def NodeLaw (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (base : Heap)
    {record originals edits input before result after}
    (actual : EditNode (width := width) record originals edits input before result after)
    (memos : Memos) : Prop :=
  ∀ inventory, Populated edits → HasLeaf edits → Allowed record edits →
    SharedReady formulas solver inventory record originals base before → Available before.checked.native.machine.heap input →
    Safe edits input → EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos → History before.checked →
    ∀ row ∈ nodeEdges result, ∃ source,
      (Original input source ∨ NodeEvent formulas solver source actual) ∧ NodeFlow formulas solver base actual source row

private theorem node_law {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {base : Heap}
    {record originals edits input before result after memos final}
    {actual : EditNode (width := width) record originals edits input before result after}
    (reads : NodeReads formulas solver base actual memos final) : NodeLaw formulas solver base actual memos := by
  refine NodeReads.rec
    (motive_1 := fun {record originals edits input before result after} actual memos _ _ =>
      NodeLaw formulas solver base actual memos)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ reads
  · intro next record originals path input before result after memos saved receipt
      inventory populated nonempty allowed ready available safe valid history row selected
    have closed : input.free = [] := by
      have domain := safe [] path (by simp [leaves])
      simpa only [SourceEqualityProjectionPathDomain.NodeClosed] using domain
    exact ⟨row,.inr (.leaf (leaf_source receipt.reads history closed row selected)),.leaf row⟩
  · intro record originals entries state memos inventory populated nonempty allowed ready available safe valid history row selected
    cases selected
  · intro record originals memos saved entries edges before rebuilt middle value heap entry depth free rows built reads ih
      inventory populated nonempty allowed ready available safe valid history row selected
    have facts := ready.checked.semantic.ready.semantic.1.normal.facts
    obtain ⟨index,original,start,rowMiddle,children,rowHeap,startInventory,middleInventory,rowMemos,rowFinal,
      earlier,call,rawIndex,sourceIndex,prefixReads,childReads,startValid,edgeBuilt,symbol,field,childrenSame,
      startReady,middleReady,startGrowth,middleGrowth,heapGrowth,live⟩ :=
      SourceCurrentSharedEditRowLineage.node_survivor reads built inventory populated allowed ready
        (InternedEdgeResidency.resident_edges _ facts.linked _ available.resident) (ordinary_rows safe) valid selected
    have startHistory := SourceCurrentParentNativeHistory.edit_rows prefixReads history facts.coherent.valid
    have middleHistory := SourceCurrentParentNativeHistory.edit_children childReads startHistory.1 startHistory.2
    have rebuilt : Rebuild formulas solver base rows original row :=
      ⟨index,start,rowMiddle,children,rowHeap,startInventory,middleInventory,memos,rowMemos,rowFinal,
        earlier,call,sourceIndex,rawIndex,prefixReads,childReads,startValid,edgeBuilt,symbol,field,childrenSame,
        startReady,middleReady,startHistory.1,middleHistory.1,
        fun childIndex child chosen => SourceCurrentSharedEditChildLineage.indexed childReads chosen⟩
    exact ⟨original,.inl (List.mem_of_getElem? sourceIndex),.node rebuilt⟩
  · intro record originals memos current saved entries original before exposed heap value after recursive head body
      headRead headGlobal bodyRead ih inventory populated nonempty allowed ready available safe valid history row selected
    have closed := recursive_closed recursive nonempty safe
    have first := head_physical ready head available
    have checked := head.verified ready.checked.semantic.ready available closed
    have found := ih inventory populated nonempty allowed first.1 first.2.2
      (closed_safe _ exposed heap first.1.checked.semantic first.2.2 checked.2.2.1) headGlobal.valid
      (history.advance _ headGlobal.keeps.growth) row selected
    obtain ⟨source,origin,flow⟩ := found
    rcases origin with originalSource | event
    · obtain ⟨chosen,chosenHeap,actualHead,_,_,_,_,origins⟩ :=
        SourceCurrentRecursiveHeadRowOrigins.complete original before.checked.native.machine.heap
          ready.checked.semantic.ready available closed
      obtain ⟨rfl,rfl⟩ := actualHead.unique head
      exact ⟨source,.inr (.exposed (recursive := recursive) (body := body) headRead origins originalSource),.recursive flow⟩
    · exact ⟨source,.inr (.recursive (recursive := recursive) (head := head) event),.recursive flow⟩
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial

/-- Every returned node guard comes from its literal input or an actual query or Head event. -/
theorem node {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {base : Heap}
    {record originals edits input before result after memos final}
    {actual : EditNode (width := width) record originals edits input before result after}
    (reads : NodeReads formulas solver base actual memos final)
    (inventory : Inventory) (populated : Populated edits) (nonempty : HasLeaf edits) (allowed : Allowed record edits)
    (ready : SharedReady formulas solver inventory record originals base before)
    (available : Available before.checked.native.machine.heap input) (safe : Safe edits input)
    (valid : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos) (history : History before.checked)
    (row : EdgeValue Symbol Guard) (selected : row ∈ nodeEdges result) :
    ∃ source, (Original input source ∨ NodeEvent formulas solver source actual) ∧
      NodeFlow formulas solver base actual source row :=
  node_law reads inventory populated nonempty allowed ready available safe valid history row selected

/-- The selected forest index retains an event in its actual child call. -/
inductive ChildEvent (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (row : Edge) :
    {record : Record} → {originals : List (Value Symbol Guard)} →
    {entries : List (Int × Edits EqualityNormalize.Path)} → {offset : Nat} →
    {inputs : List (Value Symbol Guard)} → {before : SharedState width} →
    {results : List (Value Symbol Guard)} → {after : SharedState width} →
    EditChildren record originals entries offset inputs before results after → Nat → Prop where
  /-- The current selected child supplies a root field event. -/
  | here {record originals entries value before result middle values results after edits} {offset : Nat}
      {found : SourceEqualityNeededMap.lookup (offset : Int) entries = some edits}
      {first : EditNode record originals edits value before result middle}
      {rest : EditChildren record originals entries (offset+1) values middle results after}
      (source : NodeEvent formulas solver row first) : ChildEvent formulas solver row (.selected offset found first rest) 0
  /-- An unselected earlier position leaves the later event index unchanged. -/
  | unselected {record originals entries value values before results after index} {offset : Nat}
      {absent : SourceEqualityNeededMap.lookup (offset : Int) entries = none}
      {rest : EditChildren record originals entries (offset+1) values before results after}
      (source : ChildEvent formulas solver row rest index) :
      ChildEvent formulas solver row (.unselected (value := value) offset absent rest) (index+1)
  /-- A selected earlier position precedes the later event. -/
  | selected {record originals entries value before result middle values results after edits index} {offset : Nat}
      {found : SourceEqualityNeededMap.lookup (offset : Int) entries = some edits}
      {first : EditNode record originals edits value before result middle}
      {rest : EditChildren record originals entries (offset+1) values middle results after}
      (source : ChildEvent formulas solver row rest index) :
      ChildEvent formulas solver row (.selected offset found first rest) (index+1)


end MicroCFTA.SourceCurrentClassFoldRowOrigins
