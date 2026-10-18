import MicroCFTA.SourceCurrentClassPassPhaseLineage
import MicroCFTA.SourceCurrentParentRowWriterLineage
import MicroCFTA.SourceCurrentNativeQueryRowOrigins
import MicroCFTA.SourceCurrentRecursiveHeadRowOrigins

/-!
# Full guard origins through actual class edits

Ordinary reconstruction retains the complete source guard. Leaf queries
and recursive Head exposure supply new root rows. The source relation
records those actual events before composition through the class fold.
-/
namespace MicroCFTA.SourceCurrentClassFoldGuardOrigins
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
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- A literal input row supplies the complete guard. -/
def Original (value : Value Symbol Guard) (field : Guard) : Prop :=
  ∃ row ∈ nodeEdges value, row.entry.key.constraint = field

/-- A leaf source retains its exact target query and the selected full row. -/
def LeafSource (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {record originals path input before result after}
    (actual : SourceCurrentAllocatedSharedTargetLeaf.Leaf (width := width)
      record originals path input before result after) (field : Guard) : Prop :=
  ∃ (memos final : Memos),
    SourceCurrentAllocatedSharedTargetLeaf.Reads formulas solver actual memos final ∧
    ∃ target middle forceInventory next base,
      SourceCurrentAllocatedSharedTargetForce.Receipt formulas solver forceInventory record originals base path
        before target middle memos final ∧
      SourceCurrentAllocatedTargetQuery.Receipt formulas solver next target input middle.checked result after.checked final ∧
      after = SourceCurrentAllocatedSharedTargetState.advance middle after.checked ∧
      ∃ rowIndex row, (nodeEdges result)[rowIndex]? = some row ∧ row.entry.key.constraint = field ∧
        SourceCurrentNativeQueryRowOrigins.RowOrigin after.checked
          ⟨IntersectionEmptyDomain.emptyDomain,target,input⟩ result rowIndex row

/-- A root field event occurs in the exact node edit that returns it. -/
inductive NodeEvent (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (field : Guard) :
    {record : Record} → {originals : List (Value Symbol Guard)} → {edits : Edits EqualityNormalize.Path} →
    {input : Value Symbol Guard} → {before : SharedState width} → {result : Value Symbol Guard} →
    {after : SharedState width} → EditNode record originals edits input before result after → Prop where
  /-- An actual leaf query supplies its returned row field. -/
  | leaf {record originals path input before result after}
      {actual : SourceCurrentAllocatedSharedTargetLeaf.Leaf record originals path input before result after}
      (source : LeafSource formulas solver actual field) : NodeEvent formulas solver field (.leaf actual)
  /-- A selected exposed row supplies its field before the below edit. -/
  | exposed {record originals entries original before exposed heap value after}
      {recursive : SourceEqualityRequiredGraph.Recursive original}
      {head : SourceEqualityRequiredHead.Head original before.checked.native.machine.heap exposed heap}
      {body : EditNode record originals (.editBelow entries) exposed (advanceHeap before heap) value after}
      {memos current : Memos} (read : SourceCurrentRequiredQueryMemos.HeadReads head memos current)
      (origins : SourceCurrentRecursiveHeadRowOrigins.HeadRows original before.checked.native.machine.heap exposed heap)
      (source : Original exposed field) : NodeEvent formulas solver field (.recursive recursive head body)
  /-- A later root field event remains inside the same actual Head branch. -/
  | recursive {record originals entries original before exposed heap value after}
      {recursive : SourceEqualityRequiredGraph.Recursive original}
      {head : SourceEqualityRequiredHead.Head original before.checked.native.machine.heap exposed heap}
      {body : EditNode record originals (.editBelow entries) exposed (advanceHeap before heap) value after}
      (source : NodeEvent formulas solver field body) : NodeEvent formulas solver field (.recursive recursive head body)

/-- Actual leaf reads derive a full-field source without a caller-supplied row law. -/
theorem leaf_source {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {record originals path input before result after memos final}
    {actual : SourceCurrentAllocatedSharedTargetLeaf.Leaf (width := width) record originals path input before result after}
    (reads : SourceCurrentAllocatedSharedTargetLeaf.Reads formulas solver actual memos final)
    (history : History before.checked) (closed : input.free = [])
    (row : EdgeValue Symbol Guard) (selected : row ∈ nodeEdges result) :
    LeafSource formulas solver actual row.entry.key.constraint := by
  obtain ⟨index,present⟩ := List.mem_iff_getElem?.mp selected
  obtain ⟨target,middle,forceInventory,next,base,force,query,same,_,origin⟩ :=
    SourceCurrentNativeQueryRowOrigins.leaf reads history closed index row present
  exact ⟨memos,final,reads,target,middle,forceInventory,next,base,force,query,same,index,row,present,rfl,origin⟩

private def NodeLaw (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (base : Heap)
    {record originals edits input before result after}
    (actual : EditNode (width := width) record originals edits input before result after)
    (memos : Memos) : Prop :=
  ∀ inventory, Populated edits → HasLeaf edits → Allowed record edits →
    SharedReady formulas solver inventory record originals base before → Available before.checked.native.machine.heap input →
    Safe edits input → EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos → History before.checked →
    ∀ row ∈ nodeEdges result, Original input row.entry.key.constraint ∨ NodeEvent formulas solver row.entry.key.constraint actual

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
    exact .inr (.leaf (leaf_source receipt.reads history closed row selected))
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
    exact .inl ⟨original,List.mem_of_getElem? sourceIndex,field.symm⟩
  · intro record originals memos current saved entries original before exposed heap value after recursive head body
      headRead headGlobal bodyRead ih inventory populated nonempty allowed ready available safe valid history row selected
    have closed := recursive_closed recursive nonempty safe
    have first := head_physical ready head available
    have checked := head.verified ready.checked.semantic.ready available closed
    have found := ih inventory populated nonempty allowed first.1 first.2.2
      (closed_safe _ exposed heap first.1.checked.semantic first.2.2 checked.2.2.1) headGlobal.valid
      (history.advance _ headGlobal.keeps.growth) row selected
    rcases found with originalSource | event
    · obtain ⟨chosen,chosenHeap,actualHead,_,_,_,_,origins⟩ :=
        SourceCurrentRecursiveHeadRowOrigins.complete original before.checked.native.machine.heap
          ready.checked.semantic.ready available closed
      obtain ⟨rfl,rfl⟩ := actualHead.unique head
      exact .inr (.exposed (recursive := recursive) (body := body) headRead origins originalSource)
    · exact .inr (.recursive (recursive := recursive) (head := head) event)
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
    Original input row.entry.key.constraint ∨ NodeEvent formulas solver row.entry.key.constraint actual :=
  node_law reads inventory populated nonempty allowed ready available safe valid history row selected

/-- The selected forest index retains an event in its actual child call. -/
inductive ChildEvent (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (field : Guard) :
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
      (source : NodeEvent formulas solver field first) : ChildEvent formulas solver field (.selected offset found first rest) 0
  /-- An unselected earlier position leaves the later event index unchanged. -/
  | unselected {record originals entries value values before results after index} {offset : Nat}
      {absent : SourceEqualityNeededMap.lookup (offset : Int) entries = none}
      {rest : EditChildren record originals entries (offset+1) values before results after}
      (source : ChildEvent formulas solver field rest index) :
      ChildEvent formulas solver field (.unselected (value := value) offset absent rest) (index+1)
  /-- A selected earlier position precedes the later event. -/
  | selected {record originals entries value before result middle values results after edits index} {offset : Nat}
      {found : SourceEqualityNeededMap.lookup (offset : Int) entries = some edits}
      {first : EditNode record originals edits value before result middle}
      {rest : EditChildren record originals entries (offset+1) values middle results after}
      (source : ChildEvent formulas solver field rest index) :
      ChildEvent formulas solver field (.selected offset found first rest) (index+1)

private def ChildrenLaw (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (base : Heap)
    {record originals entries offset inputs before results after}
    (actual : EditChildren (width := width) record originals entries offset inputs before results after)
    (memos : Memos) : Prop :=
  ∀ inventory, Populated (.editBelow entries) → Allowed record (.editBelow entries) →
    SharedReady formulas solver inventory record originals base before → Values before.checked.native.machine.heap inputs →
    ChildrenSafe entries offset inputs → EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos →
    History before.checked → ∀ index value, results[index]? = some value → ∀ row ∈ nodeEdges value,
    ∃ original, inputs[index]? = some original ∧
      (Original original row.entry.key.constraint ∨ ChildEvent formulas solver row.entry.key.constraint actual index)

private theorem children_law {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {base : Heap}
    {record originals entries offset inputs before results after memos final}
    {actual : EditChildren (width := width) record originals entries offset inputs before results after}
    (reads : ChildrenReads formulas solver base actual memos final) : ChildrenLaw formulas solver base actual memos := by
  refine ChildrenReads.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun {record originals entries offset inputs before results after} actual memos _ _ =>
      ChildrenLaw formulas solver base actual memos)
    (motive_3 := fun _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ reads
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intro record originals entries offset state memos inventory populated allowed ready available safe valid history index value selected row member
    simp at selected
  · intro record originals memos saved entries values before results after original offset absent rest read ih
      inventory populated allowed ready available safe valid history index value selected row member
    cases index with
    | zero =>
      have same : original = value := by simpa using selected
      subst value
      exact ⟨original,rfl,.inl ⟨row,member,rfl⟩⟩
    | succ index =>
      obtain ⟨source,found,origin⟩ := ih inventory populated allowed ready
        (fun value present => available value (List.mem_cons_of_mem _ present)) (children_tail safe) valid history
        index value (by simpa using selected) row member
      refine ⟨source,by simpa using found,?_⟩
      exact origin.imp id (fun event => .unselected (absent := absent) event)
  · intro record originals memos current saved entries edits original before result middle values results after offset found first rest firstRead restRead firstIH ih
      inventory populated allowed ready available safe valid history index value selected row member
    have present := SourceEqualityNeededMap.lookup_mem _ _ _ found
    have childSupport := (show ∀ index child, (index,child) ∈ entries → Populated child ∧ HasLeaf child from
      by simpa only [Populated] using populated) _ _ present
    have childAllowed : Allowed record edits := by
      rw [Allowed,All] at allowed
      exact allowed _ _ present
    have childSafe : Safe edits original := safe 0 _ (by simpa using found) original rfl
    cases index with
    | zero =>
      have same : result = value := by simpa using selected
      subst value
      have origin := node firstRead inventory childSupport.1 childSupport.2 childAllowed ready
        (available _ List.mem_cons_self) childSafe valid history row member
      refine ⟨original,rfl,?_⟩
      exact origin.imp id (fun event => .here (rest := rest) (found := found) event)
    | succ index =>
      obtain ⟨next,firstReceipt⟩ := node_effects firstRead childSupport.1 childSupport.2 childAllowed ready
        (available _ List.mem_cons_self) childSafe valid
      have oneRead : ChildrenReads formulas solver base
          (EditChildren.selected offset found first EditChildren.nil) memos current :=
        .selected (found := found) firstRead .nil
      have nextHistory := (SourceCurrentParentNativeHistory.edit_children oneRead history
        ready.checked.semantic.ready.semantic.1.normal.facts.coherent.valid).1
      obtain ⟨source,present,origin⟩ := ih next populated allowed firstReceipt.ready
        (fun value present => firstReceipt.effects.keeps.available value (available value (List.mem_cons_of_mem _ present)))
        (children_tail safe) firstReceipt.globals.valid nextHistory index value (by simpa using selected) row member
      refine ⟨source,by simpa using present,?_⟩
      exact origin.imp id (fun event => .selected (first := first) (found := found) event)
  · intros; trivial
  · intros; trivial

/-- Ordered child edits derive exact initial-index or actual-event guard origins. -/
theorem children {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {base : Heap}
    {record originals entries offset inputs before results after memos final}
    {actual : EditChildren (width := width) record originals entries offset inputs before results after}
    (reads : ChildrenReads formulas solver base actual memos final)
    (inventory : Inventory) (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : SharedReady formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap inputs) (safe : ChildrenSafe entries offset inputs)
    (valid : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos) (history : History before.checked)
    (index : Nat) (value : Value Symbol Guard) (selected : results[index]? = some value)
    (row : EdgeValue Symbol Guard) (member : row ∈ nodeEdges value) :
    ∃ original, inputs[index]? = some original ∧
      (Original original row.entry.key.constraint ∨ ChildEvent formulas solver row.entry.key.constraint actual index) :=
  children_law reads inventory populated allowed ready available safe valid history index value selected row member

/-- A below-edit child event occurs in the exact list execution. -/
inductive ListEvent (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (field : Guard) :
    {record : Record} → {originals : List (Value Symbol Guard)} → {edits : Edits EqualityNormalize.Path} →
    {inputs : List (Value Symbol Guard)} → {before : SharedState width} →
    {results : List (Value Symbol Guard)} → {after : SharedState width} →
    EditList record originals edits inputs before results after → Nat → Prop where
  /-- The actual child scan supplies the list event. -/
  | children {record originals entries inputs before results after index}
      {actual : EditChildren record originals entries 0 inputs before results after}
      (source : ChildEvent formulas solver field actual index) : ListEvent formulas solver field (.children actual) index

/-- Actual list execution retains source guards at the same forest index. -/
theorem list {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {base : Heap}
    {record originals edits inputs before results after memos final}
    {actual : EditList (width := width) record originals edits inputs before results after}
    (reads : ListReads formulas solver base actual memos final)
    (inventory : Inventory) (populated : Populated edits) (allowed : Allowed record edits)
    (ready : SharedReady formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap inputs) (safe : ListSafe edits inputs)
    (valid : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos) (history : History before.checked)
    (index : Nat) (value : Value Symbol Guard) (selected : results[index]? = some value)
    (row : EdgeValue Symbol Guard) (member : row ∈ nodeEdges value) :
    ∃ original, inputs[index]? = some original ∧
      (Original original row.entry.key.constraint ∨ ListEvent formulas solver row.entry.key.constraint actual index) := by
  cases reads with
  | leaf => exact ⟨value,selected,.inl ⟨row,member,rfl⟩⟩
  | children read =>
    obtain ⟨original,found,origin⟩ := children read inventory populated allowed ready available safe valid history
      index value selected row member
    exact ⟨original,found,origin.imp id (fun event => .children event)⟩

/-- A class event retains the literal compiled edit and its captured forest. -/
inductive ClassEvent (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (field : Guard) :
    {record : Record} → {inputs : List (Value Symbol Guard)} → {before : Checked width} →
    {memo : SourceCurrentMemoMergeGraph.Memo Symbol Guard} → {results : List (Value Symbol Guard)} →
    {after : Checked width} → {saved : SourceCurrentMemoMergeGraph.Memo Symbol Guard} →
    SourceCurrentAllocatedClassEdits.Class record inputs before memo results after saved → Nat → Prop where
  /-- The exact compiled list execution supplies the class event. -/
  | edit {record inputs before memo results shared index}
      {actual : EditList record inputs (SourceCurrentAllocatedClassEditPlan.compiled record) inputs
        (SourceCurrentAllocatedSharedTargetState.initial before memo) results shared}
      (source : ListEvent formulas solver field actual index) : ClassEvent formulas solver field (.edit actual) index

/-- Initial class facts and actual reads derive initial-row or local-event full guard origins. -/
theorem class_sources {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {record inputs before memo results after saved memos final}
    {actual : SourceCurrentAllocatedClassEdits.Class (width := width) record inputs before memo results after saved}
    (reads : SourceCurrentAllocatedClassEdits.ClassReads formulas solver actual memos final)
    (inventory : Inventory) (coherent : SourceEqualityClassOrder.Coherent record)
    (active : EqualityNormalize.Nontrivial record.paths) (ready : SourceCurrentConjunctionClassScan.Ready before)
    (admitted : SourceCurrentAllocatedNativeInventoryState.At formulas solver inventory before)
    (available : Values before.native.machine.heap inputs)
    (domains : ∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) inputs)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) (history : History before)
    (index : Nat) (value : Value Symbol Guard) (selected : results[index]? = some value)
    (row : EdgeValue Symbol Guard) (member : row ∈ nodeEdges value) :
    ∃ original, inputs[index]? = some original ∧
      (Original original row.entry.key.constraint ∨ ClassEvent formulas solver row.entry.key.constraint actual index) := by
  cases reads with
  | edit lower =>
    have initialReady := SourceCurrentAllocatedSharedTargetState.initial_ready formulas solver inventory record inputs
      before.native.machine.heap before memo ready admitted (SourceEqualityRequiredCache.pure_keeps _ ready.semantic.ready) stored covered
    have safe : ListSafe (SourceCurrentAllocatedClassEditPlan.compiled record) inputs := by
      obtain ⟨entries,built⟩ := SourceCurrentAllocatedClassEditPlan.compiled_children record coherent active
      rw [built]
      exact SourceCurrentAllocatedClassEditPlan.compiled_safe record coherent inputs domains entries built
    obtain ⟨original,found,origin⟩ := list lower inventory
      (SourceCurrentAllocatedClassEditPlan.compiled_populated record) (SourceCurrentAllocatedClassEditPlan.compiled_allowed record)
      initialReady available safe valid history index value selected row member
    exact ⟨original,found,origin.imp id (fun event => .edit event)⟩

/-- An event retains its exact class occurrence in the literal right fold. -/
inductive FoldEvent (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (field : Guard) :
    {records : List Record} → {inputs : List (Value Symbol Guard)} → {before : Checked width} →
    {memo : SourceCurrentMemoMergeGraph.Memo Symbol Guard} → {results : List (Value Symbol Guard)} →
    {after : Checked width} → {saved : SourceCurrentMemoMergeGraph.Memo Symbol Guard} →
    SourceCurrentAllocatedClassPass.Fold records inputs before memo results after saved → Nat → Prop where
  /-- The current head class supplies the event. -/
  | head {records inputs before memo middle next current record results after saved index}
      {tail : SourceCurrentAllocatedClassPass.Fold records inputs before memo middle next current}
      {head : SourceCurrentAllocatedClassEdits.Class record middle next current results after saved}
      (source : ClassEvent formulas solver field head index) : FoldEvent formulas solver field (.cons tail head) index
  /-- Earlier tail execution supplies a field retained through the current head. -/
  | tail {records inputs before memo middle next current record results after saved index}
      {tail : SourceCurrentAllocatedClassPass.Fold records inputs before memo middle next current}
      {head : SourceCurrentAllocatedClassEdits.Class record middle next current results after saved}
      (source : FoldEvent formulas solver field tail index) : FoldEvent formulas solver field (.cons tail head) index

/-- Every final guard comes from the initial same-index forest or an actual fold event. -/
theorem fold {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {records inputs before memo results after saved memos final}
    {actual : SourceCurrentAllocatedClassPass.Fold (width := width) records inputs before memo results after saved}
    (reads : SourceCurrentAllocatedClassPass.FoldReads formulas solver actual memos final)
    (inventory : Inventory)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : SourceCurrentConjunctionClassScan.Ready before)
    (admitted : SourceCurrentAllocatedNativeInventoryState.At formulas solver inventory before)
    (available : Values before.native.machine.heap inputs)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) inputs)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) (history : History before)
    (index : Nat) (value : Value Symbol Guard) (selected : results[index]? = some value)
    (row : EdgeValue Symbol Guard) (member : row ∈ nodeEdges value) :
    (∃ original, inputs[index]? = some original ∧ Original original row.entry.key.constraint) ∨
      FoldEvent formulas solver row.entry.key.constraint actual index := by
  induction reads generalizing inventory index value row with
  | nil => exact .inl ⟨value,selected,row,member,rfl⟩
  | @cons records inputs before memo middle step current record results after saved memos stepMemos final tail head tailReads headReads ih =>
    have tailCoherent := fun own member => coherent own (List.mem_cons_of_mem record member)
    have tailActive := fun own member => active own (List.mem_cons_of_mem record member)
    have tailDomains := fun own member => domains own (List.mem_cons_of_mem record member)
    obtain ⟨phaseInventory,receipt⟩ := SourceCurrentAllocatedClassPass.Fold.verified formulas solver inventory tailReads
      tailCoherent tailActive ready admitted available tailDomains stored covered valid
    have phaseHistory := SourceCurrentParentNativeHistory.class_pass
      (SourceCurrentAllocatedClassPass.PassReads.done tailReads) history ready
    obtain ⟨phaseInput,phaseSelected,origin⟩ := class_sources headReads phaseInventory
      (coherent record List.mem_cons_self) (active record List.mem_cons_self) receipt.ready receipt.admitted receipt.available
      (fun path member => receipt.domains _ (domains record List.mem_cons_self path member))
      receipt.stored receipt.covered receipt.globals.valid phaseHistory index value selected row member
    rcases origin with ⟨sourceRow,sourceMember,field⟩ | event
    · have earlier := ih inventory tailCoherent tailActive ready admitted available tailDomains stored covered valid history
        index phaseInput phaseSelected sourceRow sourceMember
      rw [field] at earlier
      exact earlier.imp id (fun event => .tail (head := head) event)
    · exact .inr (.head (tail := tail) event)

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

/-- A surviving pass row retains its actual full fold and initial or event guard source. -/
theorem pass {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {records inputs before memo results after saved memos final}
    {actual : SourceCurrentAllocatedClassPass.Pass (width := width) records inputs before memo results after saved}
    (reads : SourceCurrentAllocatedClassPass.PassReads formulas solver actual memos final)
    (inventory : Inventory)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : SourceCurrentConjunctionClassScan.Ready before)
    (admitted : SourceCurrentAllocatedNativeInventoryState.At formulas solver inventory before)
    (available : Values before.native.machine.heap inputs)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) inputs)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) (history : History before)
    (index : Nat) (value : Value Symbol Guard) (selected : results[index]? = some value)
    (row : EdgeValue Symbol Guard) (member : row ∈ nodeEdges value) :
    ∃ full : SourceCurrentAllocatedClassPass.Fold records inputs before memo results after saved,
      SourceCurrentAllocatedClassPass.FoldReads formulas solver full memos final ∧
      ((∃ original, inputs[index]? = some original ∧ Original original row.entry.key.constraint) ∨
        FoldEvent formulas solver row.entry.key.constraint full index) := by
  cases reads with
  | @done records inputs before memo raw after saved full read =>
    have same := propagate_selected raw index value selected row member
    rw [same] at selected ⊢
    exact ⟨full,read,fold read inventory coherent active ready admitted available domains stored covered valid history
      index value selected row member⟩

end MicroCFTA.SourceCurrentClassFoldGuardOrigins
