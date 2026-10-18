import MicroCFTA.SourceCurrentClassFoldRowOrigins
import MicroCFTA.SourceCurrentRequiredRowOrigins

/-!
# Structural row occurrences through actual class edits

An occurrence either retains a complete original row or descends from an
actual native leaf or Head exposure. Ordinary event lifts retain the
canonical output index, raw row index, and exact child execution slice.
-/
namespace MicroCFTA.SourceCurrentClassStructuralOrigins
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceEqualityEdits SourceEqualityEditLeafPaths SourceCurrentEditDomains
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentAllocatedSharedEditGraph SourceCurrentAllocatedSharedEditEffects
open SourceCurrentNativeEdgeWriterGrowth (History)
open SourceCurrentRequiredRowOrigins (RowAt Position)
open SourceCurrentRequiredGuardOrigins (RowOrigin)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "SharedReady" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Inventory" => SourceCurrentAllocatedNativeInventoryState.Inventory
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

mutual
/-- An actual native leaf or Head exposure supplies this event value. -/
inductive Event (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (base : Heap) :
    {record : Record} → {originals : List Node} → {edits : Edits EqualityNormalize.Path} →
    {input : Node} → {before : SharedState width} → {result : Node} → {after : SharedState width} →
    EditNode record originals edits input before result after → Node → Prop where
  /-- The native leaf supplies its actual returned value. -/
  | leaf {record originals path input before result after memos final}
      {actual : SourceCurrentAllocatedSharedTargetLeaf.Leaf record originals path input before result after}
      (read : SourceCurrentAllocatedSharedTargetLeaf.Reads formulas solver actual memos final)
      (history : History before.checked) : Event formulas solver base (.leaf actual) result
  /-- Head supplies its exposed value before the recursive edit. -/
  | head {record originals entries original before exposed heap result after memos current final}
      {recursive : SourceEqualityRequiredGraph.Recursive original}
      {head : SourceEqualityRequiredHead.Head original before.checked.native.machine.heap exposed heap}
      {body : EditNode record originals (.editBelow entries) exposed (advanceHeap before heap) result after}
      (read : SourceCurrentRequiredQueryMemos.HeadReads head memos current)
      (bodyRead : NodeReads formulas solver base body current final)
      (history : History before.checked) : Event formulas solver base (.recursive recursive head body) exposed
  /-- A recursive edit retains an event from its actual body call. -/
  | recursive {record originals entries original before exposed heap result after event}
      {recursive : SourceEqualityRequiredGraph.Recursive original}
      {head : SourceEqualityRequiredHead.Head original before.checked.native.machine.heap exposed heap}
      {body : EditNode record originals (.editBelow entries) exposed (advanceHeap before heap) result after}
      (source : Event formulas solver base body event) :
      Event formulas solver base (.recursive recursive head body) event
  /-- A canonical survivor retains distinct output and raw source indices. -/
  | ordinary {record originals entries edges before rebuilt middle value heap entry depth free event}
      {actual : EditRows record originals entries edges before rebuilt middle}
      {built : run (makeNode rebuilt) middle.checked.native.machine.heap = (value,heap)}
      {memos final : Memos} (read : RowsReads formulas solver base actual memos final)
      (outputIndex rawIndex childIndex : Nat) (parent : Edge)
      (output : (nodeEdges value)[outputIndex]? = some parent)
      (raw : rebuilt[rawIndex]? = some parent)
      (source : RowEvent formulas solver base actual rawIndex childIndex event) :
      Event formulas solver base (.ordinary (entry := entry) (depth := depth) (free := free) actual built) event

/-- The indexed child event retains its actual ordered dispatch. -/
inductive ChildEvent (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (base : Heap) :
    {record : Record} → {originals : List Node} → {entries : List (Int × Edits EqualityNormalize.Path)} →
    {offset : Nat} → {inputs : List Node} → {before : SharedState width} →
    {results : List Node} → {after : SharedState width} →
    EditChildren record originals entries offset inputs before results after → Nat → Node → Prop where
  /-- The selected current child supplies its actual node event. -/
  | here {record originals entries value before result middle values results after edits event} {offset : Nat}
      {found : SourceEqualityNeededMap.lookup (offset : Int) entries = some edits}
      {first : EditNode record originals edits value before result middle}
      {rest : EditChildren record originals entries (offset+1) values middle results after}
      (source : Event formulas solver base first event) :
      ChildEvent formulas solver base (.selected offset found first rest) 0 event
  /-- An earlier unselected child precedes the event. -/
  | unselected {record originals entries value values before results after index event} {offset : Nat}
      {absent : SourceEqualityNeededMap.lookup (offset : Int) entries = none}
      {rest : EditChildren record originals entries (offset+1) values before results after}
      (source : ChildEvent formulas solver base rest index event) :
      ChildEvent formulas solver base (.unselected (value := value) offset absent rest) (index+1) event
  /-- An earlier selected child precedes the event. -/
  | selected {record originals entries value before result middle values results after edits index event} {offset : Nat}
      {found : SourceEqualityNeededMap.lookup (offset : Int) entries = some edits}
      {first : EditNode record originals edits value before result middle}
      {rest : EditChildren record originals entries (offset+1) values middle results after}
      (source : ChildEvent formulas solver base rest index event) :
      ChildEvent formulas solver base (.selected offset found first rest) (index+1) event

/-- The raw row event retains its exact selected child slice. -/
inductive RowEvent (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (base : Heap) :
    {record : Record} → {originals : List Node} → {entries : List (Int × Edits EqualityNormalize.Path)} →
    {inputs : List Edge} → {before : SharedState width} → {results : List Edge} → {after : SharedState width} →
    EditRows record originals entries inputs before results after → Nat → Nat → Node → Prop where
  /-- The current row retains the selected child and its complete execution slice. -/
  | here {record originals entries before values middle result heap edges results after event} {edge : Edge}
      {children : EditChildren record originals entries 0 edge.children before values middle}
      {built : run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values)
        middle.checked.native.machine.heap = (result,heap)}
      {rest : EditRows record originals entries edges (advanceHeap middle heap) results after}
      {memos current : Memos} (read : ChildrenReads formulas solver base children memos current)
      (childIndex : Nat) (child : Node) (selected : values[childIndex]? = some child)
      (slice : SourceCurrentSharedEditChildLineage.Slice formulas solver base record originals entries 0
        edge.children before values middle memos current childIndex child)
      (source : ChildEvent formulas solver base children childIndex event) :
      RowEvent formulas solver base (.cons children built rest) 0 childIndex event
  /-- A later row retains its distinct raw scan index. -/
  | later {record originals entries before values middle result heap edges results after rowIndex childIndex event} {edge : Edge}
      {children : EditChildren record originals entries 0 edge.children before values middle}
      {built : run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values)
        middle.checked.native.machine.heap = (result,heap)}
      {rest : EditRows record originals entries edges (advanceHeap middle heap) results after}
      (source : RowEvent formulas solver base rest rowIndex childIndex event) :
      RowEvent formulas solver base (.cons children built rest) (rowIndex+1) childIndex event
end

private def Source (input : Node) (row : Edge) : Prop :=
  ∃ path index original, RowAt input path index original ∧ RowOrigin original row

private def FromEvent {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {base : Heap}
    {record originals edits input before result after}
    (actual : EditNode (width := width) record originals edits input before result after) (row : Edge) : Prop :=
  ∃ event path index original, Event formulas solver base actual event ∧
    RowAt event path index original ∧ RowOrigin original row

private def NodeLaw (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (base : Heap)
    {record originals edits input before result after}
    (actual : EditNode (width := width) record originals edits input before result after) (memos : Memos) : Prop :=
  ∀ inventory, Populated edits → HasLeaf edits → Allowed record edits →
    SharedReady formulas solver inventory record originals base before → Available before.checked.native.machine.heap input →
    Safe edits input → EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos → History before.checked →
    ∀ path index row, RowAt result path index row → Source input row ∨ FromEvent (formulas := formulas) (solver := solver) (base := base) actual row

private def ChildrenLaw (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (base : Heap)
    {record originals entries offset inputs before results after}
    (actual : EditChildren (width := width) record originals entries offset inputs before results after) (memos : Memos) : Prop :=
  ∀ inventory, Populated (.editBelow entries) → Allowed record (.editBelow entries) →
    SharedReady formulas solver inventory record originals base before → Values before.checked.native.machine.heap inputs →
    ChildrenSafe entries offset inputs → EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos → History before.checked →
    ∀ childIndex child, results[childIndex]? = some child → ∀ path index row, RowAt child path index row →
    (∃ original, inputs[childIndex]? = some original ∧ Source original row) ∨
      ∃ event suffix sourceIndex original, ChildEvent formulas solver base actual childIndex event ∧
        RowAt event suffix sourceIndex original ∧ RowOrigin original row

private def RowsLaw (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (base : Heap)
    {record originals entries inputs before results after}
    (actual : EditRows (width := width) record originals entries inputs before results after) (memos : Memos) : Prop :=
  ∀ inventory, Populated (.editBelow entries) → Allowed record (.editBelow entries) →
    SharedReady formulas solver inventory record originals base before → Edges before.checked.native.machine.heap inputs →
    RowsSafe entries inputs → EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos → History before.checked →
    ∀ rawIndex output, results[rawIndex]? = some output →
    ∃ original, inputs[rawIndex]? = some original ∧ RowOrigin original output ∧
      ∀ childIndex child, output.children[childIndex]? = some child → ∀ path index row, RowAt child path index row →
      (∃ inputChild, original.children[childIndex]? = some inputChild ∧ Source inputChild row) ∨
        ∃ event suffix sourceIndex source, RowEvent formulas solver base actual rawIndex childIndex event ∧
          RowAt event suffix sourceIndex source ∧ RowOrigin source row

set_option maxHeartbeats 2400000 in
private theorem node_law {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {base : Heap}
    {record originals edits input before result after memos final}
    {actual : EditNode (width := width) record originals edits input before result after}
    (reads : NodeReads formulas solver base actual memos final) : NodeLaw formulas solver base actual memos := by
  refine NodeReads.rec
    (motive_1 := fun {record originals edits input before result after} actual memos _ _ =>
      NodeLaw formulas solver base actual memos)
    (motive_2 := fun {record originals entries offset inputs before results after} actual memos _ _ =>
      ChildrenLaw formulas solver base actual memos)
    (motive_3 := fun {record originals entries inputs before results after} actual memos _ _ =>
      RowsLaw formulas solver base actual memos)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ reads
  · intro next record originals path input before result after memos saved receipt
      inventory populated nonempty allowed ready available safe valid history positions index row occurrence
    exact .inr ⟨result,positions,index,row,.leaf receipt.reads history,occurrence,rfl,rfl,rfl⟩
  · intro record originals entries state memos inventory populated nonempty allowed ready available safe valid history positions index row occurrence
    cases occurrence with
    | root selected => simp [nodeEdges] at selected
    | child rowIndex childIndex parent child selected found rest => simp [nodeEdges] at selected
  · intro record originals memos saved entries edges before rebuilt middle value heap entry depth free actual built read ih
      inventory populated nonempty allowed ready available safe valid history positions index row occurrence
    have facts := ready.checked.semantic.ready.semantic.1.normal.facts
    have resident := resident_edges _ facts.linked _ available.resident
    obtain ⟨next,receipt⟩ := rows_effects read populated allowed ready resident (ordinary_rows safe) valid
    have nextFacts := receipt.ready.checked.semantic.ready.semantic.1.normal.facts
    have equalEdges : nodeEdges value = canonicalEdges (surviving rebuilt) := by
      simpa only [built] using EqualityLeafProjectionPhysical.makeNode_edges rebuilt middle.checked.native.machine.heap
        nextFacts.coherent nextFacts.linked receipt.available
    have ordinary : Ordinary value := by
      simpa only [built] using SourceEqualityRequiredCache.node_ordinary rebuilt middle.checked.native.machine.heap
        nextFacts receipt.available
    have select : ∀ outputIndex parent, (nodeEdges value)[outputIndex]? = some parent →
        ∃ rawIndex, rebuilt[rawIndex]? = some parent := by
      intro outputIndex parent selected
      have present := List.mem_of_getElem? selected
      rw [equalEdges] at present
      exact List.mem_iff_getElem?.mp (List.mem_filter.mp (canonicalEdges_member _ parent present)).1
    cases occurrence with
    | root selected =>
      obtain ⟨rawIndex,raw⟩ := select index row selected
      obtain ⟨original,found,fields,_⟩ := ih inventory populated allowed ready resident (ordinary_rows safe) valid history rawIndex row raw
      exact .inl ⟨[],rawIndex,original,.root found,fields⟩
    | child outputIndex childIndex parent child selected chosen rest =>
      obtain ⟨rawIndex,raw⟩ := select outputIndex parent selected
      obtain ⟨original,found,fields,children⟩ := ih inventory populated allowed ready resident (ordinary_rows safe) valid history rawIndex parent raw
      rcases children childIndex child chosen _ index row rest with source | event
      · obtain ⟨inputChild,inputFound,path,sourceIndex,source,sourceAt,origin⟩ := source
        exact .inl ⟨.child rawIndex childIndex :: path,sourceIndex,source,
          .child rawIndex childIndex original inputChild found inputFound sourceAt,origin⟩
      · obtain ⟨event,suffix,sourceIndex,source,eventAt,sourceAt,origin⟩ := event
        exact .inr ⟨event,suffix,sourceIndex,source,
          .ordinary (built := built) read outputIndex rawIndex childIndex parent selected raw eventAt,sourceAt,origin⟩
    | member _ _ _ _ _ _ _ _ => cases ordinary
    | body _ _ _ _ _ => cases ordinary
  · intro record originals memos current saved entries original before exposed heap value after recursive head body
      headRead headGlobal bodyRead ih inventory populated nonempty allowed ready available safe valid history positions index row occurrence
    have closed := recursive_closed recursive nonempty safe
    have first := head_physical ready head available
    have checked := head.verified ready.checked.semantic.ready available closed
    have found := ih inventory populated nonempty allowed first.1 first.2.2
      (closed_safe _ exposed heap first.1.checked.semantic first.2.2 checked.2.2.1) headGlobal.valid
      (history.advance _ headGlobal.keeps.growth) positions index row occurrence
    rcases found with source | event
    · obtain ⟨path,sourceIndex,source,sourceAt,origin⟩ := source
      exact .inr ⟨exposed,path,sourceIndex,source,.head headRead bodyRead history,sourceAt,origin⟩
    · obtain ⟨event,path,sourceIndex,source,eventAt,sourceAt,origin⟩ := event
      exact .inr ⟨event,path,sourceIndex,source,.recursive eventAt,sourceAt,origin⟩
  · intro record originals entries offset state memos inventory populated allowed ready available safe valid history childIndex child selected path index row occurrence
    simp at selected
  · intro record originals memos saved entries values before results after original offset absent rest read ih
      inventory populated allowed ready available safe valid history childIndex child selected path index row occurrence
    cases childIndex with
    | zero =>
      have same : original = child := by simpa using selected
      subst child
      exact .inl ⟨original,rfl,path,index,row,occurrence,rfl,rfl,rfl⟩
    | succ childIndex =>
      have found := ih inventory populated allowed ready
        (fun value present => available value (List.mem_cons_of_mem _ present)) (children_tail safe) valid history
        childIndex child (by simpa using selected) path index row occurrence
      rcases found with source | event
      · obtain ⟨original,present,source⟩ := source
        exact .inl ⟨original,by simpa using present,source⟩
      · obtain ⟨event,suffix,sourceIndex,source,eventAt,sourceAt,origin⟩ := event
        exact .inr ⟨event,suffix,sourceIndex,source,.unselected eventAt,sourceAt,origin⟩
  · intro record originals memos current saved entries edits original before result middle values results after offset found first rest firstRead restRead firstIH ih
      inventory populated allowed ready available safe valid history childIndex child selected path index row occurrence
    have present := SourceEqualityNeededMap.lookup_mem _ _ _ found
    have support := (show ∀ index child, (index,child) ∈ entries → Populated child ∧ HasLeaf child from
      by simpa only [Populated] using populated) _ _ present
    have childAllowed : Allowed record edits := by
      rw [Allowed,All] at allowed
      exact allowed _ _ present
    have childSafe : Safe edits original := safe 0 _ (by simpa using found) original rfl
    cases childIndex with
    | zero =>
      have same : result = child := by simpa using selected
      subst child
      have childResult := firstIH inventory support.1 support.2 childAllowed ready
        (available _ List.mem_cons_self) childSafe valid history path index row occurrence
      rcases childResult with source | event
      · exact .inl ⟨original,rfl,source⟩
      · obtain ⟨event,suffix,sourceIndex,source,eventAt,sourceAt,origin⟩ := event
        exact .inr ⟨event,suffix,sourceIndex,source,.here eventAt,sourceAt,origin⟩
    | succ childIndex =>
      obtain ⟨next,receipt⟩ := node_effects firstRead support.1 support.2 childAllowed ready
        (available _ List.mem_cons_self) childSafe valid
      have oneRead : ChildrenReads formulas solver base
          (EditChildren.selected offset found first EditChildren.nil) memos current :=
        .selected (found := found) firstRead .nil
      have nextHistory := (SourceCurrentParentNativeHistory.edit_children oneRead history
        ready.checked.semantic.ready.semantic.1.normal.facts.coherent.valid).1
      have childResult := ih next populated allowed receipt.ready
        (fun value present => receipt.effects.keeps.available value (available value (List.mem_cons_of_mem _ present)))
        (children_tail safe) receipt.globals.valid nextHistory childIndex child (by simpa using selected) path index row occurrence
      rcases childResult with source | event
      · obtain ⟨original,present,source⟩ := source
        exact .inl ⟨original,by simpa using present,source⟩
      · obtain ⟨event,suffix,sourceIndex,source,eventAt,sourceAt,origin⟩ := event
        exact .inr ⟨event,suffix,sourceIndex,source,.selected eventAt,sourceAt,origin⟩
  · intro record originals entries state memos inventory populated allowed ready resident safe valid history rawIndex output selected
    simp at selected
  · intro record originals memos current saved entries before values middle result heap edges results after edge children built rest
      firstRead restRead firstIH ih inventory populated allowed ready resident safe valid history rawIndex output selected
    have facts := ready.checked.semantic.ready.semantic.1.normal.facts
    have childAvailable := facts.cached.edges edge.entry.key edge (resident _ List.mem_cons_self)
    obtain ⟨middleInventory,receipt⟩ := children_effects firstRead populated allowed ready childAvailable
      (safe _ List.mem_cons_self) valid
    have fields := MergedPhysicalGroupEdges.makeEdge_fields middle.checked.native.machine.heap
      receipt.ready.checked.semantic.ready.semantic.1.normal.facts edge.entry.key.symbol edge.entry.key.constraint values receipt.available
    have sameChildren : result.children = values := by simpa only [built] using fields.2.2
    have rowOrigin : RowOrigin edge result :=
      ⟨by simpa only [built] using fields.2.1,by simpa only [built] using fields.1,
        (congrArg List.length sameChildren).trans (children_length children)⟩
    cases rawIndex with
    | zero =>
      have same : result = output := by simpa using selected
      subst output
      refine ⟨edge,rfl,rowOrigin,?_⟩
      intro childIndex child childSelected path index row occurrence
      have chosen : values[childIndex]? = some child := by simpa only [sameChildren] using childSelected
      have childResult := firstIH inventory populated allowed ready childAvailable (safe _ List.mem_cons_self)
        valid history childIndex child chosen path index row occurrence
      rcases childResult with source | event
      · exact .inl source
      · obtain ⟨event,suffix,sourceIndex,source,eventAt,sourceAt,origin⟩ := event
        exact .inr ⟨event,suffix,sourceIndex,source,
          .here firstRead childIndex child chosen (SourceCurrentSharedEditChildLineage.indexed firstRead chosen) eventAt,sourceAt,origin⟩
    | succ rawIndex =>
      have oneRead : RowsReads formulas solver base (EditRows.cons children built EditRows.nil) memos current :=
        .cons firstRead .nil
      obtain ⟨next,firstReceipt⟩ := rows_effects oneRead populated allowed ready
        (fun row present => by simpa using resident row (by simpa using present))
        (fun row present => safe row (by simpa using present)) valid
      have nextHistory := (SourceCurrentParentNativeHistory.edit_rows oneRead history facts.coherent.valid).1
      obtain ⟨original,present,origin,childrenResult⟩ := ih next populated allowed firstReceipt.ready
        (fun row present => edge_grows _ _ firstReceipt.effects.keeps.growth row (resident row (List.mem_cons_of_mem _ present)))
        (fun row present => safe row (List.mem_cons_of_mem _ present)) firstReceipt.globals.valid nextHistory
        rawIndex output (by simpa using selected)
      refine ⟨original,by simpa using present,origin,?_⟩
      intro childIndex child chosen path index row occurrence
      rcases childrenResult childIndex child chosen path index row occurrence with source | event
      · exact .inl source
      · obtain ⟨event,suffix,sourceIndex,source,eventAt,sourceAt,fields⟩ := event
        exact .inr ⟨event,suffix,sourceIndex,source,.later eventAt,sourceAt,fields⟩

/-- Every structural output row retains an original occurrence or an actual event source. -/
theorem node {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {base : Heap}
    {record originals edits input before result after memos final}
    {actual : EditNode (width := width) record originals edits input before result after}
    (reads : NodeReads formulas solver base actual memos final)
    (inventory : Inventory) (populated : Populated edits) (nonempty : HasLeaf edits) (allowed : Allowed record edits)
    (ready : SharedReady formulas solver inventory record originals base before)
    (available : Available before.checked.native.machine.heap input) (safe : Safe edits input)
    (valid : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos) (history : History before.checked)
    {positions index row} (occurrence : RowAt result positions index row) :
    (∃ sourcePath sourceIndex original, RowAt input sourcePath sourceIndex original ∧ RowOrigin original row) ∨
      ∃ event suffix sourceIndex original, Event formulas solver base actual event ∧
        RowAt event suffix sourceIndex original ∧ RowOrigin original row :=
  node_law reads inventory populated nonempty allowed ready available safe valid history positions index row occurrence

end MicroCFTA.SourceCurrentClassStructuralOrigins


