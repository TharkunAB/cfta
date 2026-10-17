import MicroCFTA.SourceCurrentParentNativeHistory
import MicroCFTA.SourceCurrentNativeWriterReadyRetention
import MicroCFTA.SourceCurrentClassSelectedChildLineage

/-!
# Native reader retention through actual shared computations

Completed target, leaf, edit, and class reads retain both native returned
cell families and their published handles. Actual query receipts supply
their initial shape. Heap-only stages leave both tables unchanged.
-/
namespace MicroCFTA.SourceCurrentNativeReaderRetention
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityNativeDemandMemo (Retained)
open SourceCurrentAllocatedNativeEffects (physical)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "Inventory" => SourceCurrentAllocatedNativeInventoryState.Inventory
local notation "Memos" => EndpointMemoGateTrace.Memos
variable {width : Nat}

private theorem tables {before after : Checked width}
    (nodes : after.native.nodes = before.native.nodes)
    (edges : after.native.edges = before.native.edges) : Retained before.native after.native := by
  refine ⟨?_,?_,?_,?_⟩
  · rw [nodes]; exact FlatMemoThunk.Returned.refl _
  · rw [edges]; exact FlatMemoThunk.Returned.refl _
  · rw [nodes]; exact extends_refl _
  · rw [edges]; exact extends_refl _

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem target_fold {formulas solver values seed paths before memo value after saved memos final}
    {actual : SourceCurrentAllocatedTargetGraph.Fold (width := width) values seed paths before memo value after saved}
    (reads : SourceCurrentAllocatedTargetComplete.FoldReads formulas solver actual memos final) :
    Retained before.native after.native ∧ Ready after := by
  induction reads with
  | nil receipt => exact ⟨tables receipt.nodes receipt.edges,receipt.ready⟩
  | cons first rest query ih =>
    have earlier :=  tables first.nodes first.edges
    cases query.actual with
    | run trace =>
      exact ⟨earlier.trans (ih.1.trans
        (SourceCurrentNativeWriterReadyRetention.trace_retained trace ih.2.good.native.shape)),query.ready⟩

/-- Actual target reads retain all earlier native returned cells and handles. -/
theorem target {formulas solver values paths before memo value after saved memos final}
    {actual : SourceCurrentAllocatedTargetGraph.Target (width := width) values paths before memo value after saved}
    (reads : SourceCurrentAllocatedTargetComplete.TargetReads formulas solver actual memos final) :
    Retained before.native after.native := by
  cases reads with
  | nil => exact .refl _
  | cons reads => exact (target_fold reads).1

/-- Slot hits retain the identical tables; misses retain them through actual target reads. -/
theorem force {formulas solver inventory record values base path before value after memos final}
    (receipt : SourceCurrentAllocatedSharedTargetForce.Receipt (width := width) formulas solver inventory
      record values base path before value after memos final) :
    Retained before.checked.native after.checked.native := by
  cases receipt.reads with
  | hit => exact .refl _
  | miss absent reads => exact target reads

/-- Actual leaf reads retain earlier cells through forcing and their own checked query. -/
theorem leaf {formulas solver inventory record values base path input before value after memos final}
    (receipt : SourceCurrentAllocatedSharedTargetLeaf.Receipt (width := width) formulas solver inventory
      record values base path input before value after memos final) :
    Retained before.checked.native after.checked.native := by
  cases receipt.reads with
  | apply first query =>
    cases query.actual with
    | run trace =>
      exact (force first).trans
        (SourceCurrentNativeWriterReadyRetention.trace_retained trace first.ready.checked.good.native.shape)

/-- Actual child scans retain earlier returned cells through every selected node call. -/
theorem edit_children {formulas solver base record originals entries offset values before results after memos final}
    {actual : SourceCurrentAllocatedSharedEditGraph.EditChildren (width := width) record originals entries offset values before results after}
    (reads : SourceCurrentAllocatedSharedEditGraph.ChildrenReads formulas solver base actual memos final) :
    Retained before.checked.native after.checked.native := by
  refine SourceCurrentAllocatedSharedEditGraph.ChildrenReads.rec
    (motive_1 := fun {record originals edits value before result after} _ _ _ _ => Retained before.checked.native after.checked.native)
    (motive_2 := fun {record originals entries offset values before results after} _ _ _ _ => Retained before.checked.native after.checked.native)
    (motive_3 := fun {record originals entries edges before results after} _ _ _ _ => Retained before.checked.native after.checked.native)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ reads
  · intro next record originals path value before result after memos saved receipt
    exact leaf receipt
  · intros; exact .refl _
  · intro record originals memos saved entries edges before rebuilt middle value heap entry depth free actual built read ih
    exact ih.trans (SourceEqualityNativeDemandMemo.advance_retained _ _)
  · intro record originals memos current saved entries original before exposed heap value after recursive head body headRead headGlobal bodyRead ih
    exact (SourceEqualityNativeDemandMemo.advance_retained _ _).trans ih
  · intros; exact .refl _
  · intro record originals memos saved entries values before results after value offset absent rest read ih
    exact ih
  · intro record originals memos current saved entries edits value before result middle values results after offset found first rest firstRead restRead firstIH restIH
    exact firstIH.trans restIH
  · intros; exact .refl _
  · intro record originals memos current saved entries before values middle result heap edges results after edge children rebuilt rest firstRead restRead firstIH restIH
    exact (firstIH.trans (SourceEqualityNativeDemandMemo.advance_retained _ _)).trans restIH

/-- Actual row scans retain earlier cells through their child calls and raw constructors. -/
theorem edit_rows {formulas solver base record originals entries edges before results after memos final}
    {actual : SourceCurrentAllocatedSharedEditGraph.EditRows (width := width) record originals entries edges before results after}
    (reads : SourceCurrentAllocatedSharedEditGraph.RowsReads formulas solver base actual memos final) :
    Retained before.checked.native after.checked.native := by
  refine SourceCurrentAllocatedSharedEditGraph.RowsReads.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun {record originals entries edges before results after} _ _ _ _ => Retained before.checked.native after.checked.native)
    (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial) ?_ ?_ reads
  · intros; exact .refl _
  · intro record originals memos current saved entries before values middle result heap edges results after edge children rebuilt rest firstRead restRead ignored ih
    exact ((edit_children firstRead).trans (SourceEqualityNativeDemandMemo.advance_retained _ _)).trans ih

/-- Actual node reads retain earlier cells across recursive heads and ordinary row reconstruction. -/
theorem edit_node {formulas solver base record originals edits value before result after memos final}
    {actual : SourceCurrentAllocatedSharedEditGraph.EditNode (width := width) record originals edits value before result after}
    (reads : SourceCurrentAllocatedSharedEditGraph.NodeReads formulas solver base actual memos final) :
    Retained before.checked.native after.checked.native := by
  refine SourceCurrentAllocatedSharedEditGraph.NodeReads.rec
    (motive_1 := fun {record originals edits value before result after} _ _ _ _ => Retained before.checked.native after.checked.native)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True)
    ?_ ?_ ?_ ?_ (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) reads
  · intro next record originals path value before result after memos saved receipt
    exact leaf receipt
  · intros; exact .refl _
  · intro record originals memos saved entries edges before rebuilt middle value heap entry depth free actual built read ignored
    exact (edit_rows read).trans (SourceEqualityNativeDemandMemo.advance_retained _ _)
  · intro record originals memos current saved entries original before exposed heap value after recursive head body headRead headGlobal bodyRead ih
    exact (SourceEqualityNativeDemandMemo.advance_retained _ _).trans ih

/-- Actual list edits retain the same earlier native completed cells. -/
theorem edit_list {formulas solver base record originals edits values before results after memos final}
    {actual : SourceCurrentAllocatedSharedEditGraph.EditList (width := width) record originals edits values before results after}
    (reads : SourceCurrentAllocatedSharedEditGraph.ListReads formulas solver base actual memos final) :
    Retained before.checked.native after.checked.native := by
  cases reads with
  | leaf => exact .refl _
  | children read => exact edit_children read

/-- Actual compiled classes retain earlier cells while clearing only their local target slots. -/
theorem class_read {formulas solver record values before memo results after saved memos final}
    {actual : SourceCurrentAllocatedClassEdits.Class (width := width) record values before memo results after saved}
    (reads : SourceCurrentAllocatedClassEdits.ClassReads formulas solver actual memos final) :
    Retained before.native after.native := by
  cases reads with
  | edit lower => exact edit_list lower

/-- The actual right fold retains completed native cells across every class phase. -/
theorem class_fold {formulas solver records values before memo results after saved memos final}
    {actual : SourceCurrentAllocatedClassPass.Fold (width := width) records values before memo results after saved}
    (reads : SourceCurrentAllocatedClassPass.FoldReads formulas solver actual memos final) :
    Retained before.native after.native := by
  induction reads with
  | nil => exact .refl _
  | cons first last ih => exact ih.trans (class_read last)

/-- Final empty propagation retains the complete native tables of the actual fold. -/
theorem class_pass {formulas solver records values before memo results after saved memos final}
    {actual : SourceCurrentAllocatedClassPass.Pass (width := width) records values before memo results after saved}
    (reads : SourceCurrentAllocatedClassPass.PassReads formulas solver actual memos final) :
    Retained before.native after.native := by
  cases reads with
  | done read => exact class_fold read

private theorem list_history {formulas solver base record originals edits values before results after memos final}
    {actual : SourceCurrentAllocatedSharedEditGraph.EditList (width := width) record originals edits values before results after}
    (reads : SourceCurrentAllocatedSharedEditGraph.ListReads formulas solver base actual memos final) :
    SourceCurrentNativeEdgeWriterGrowth.History before.checked → InternedConstructorTemplates.Valid before.checked.native.machine.heap →
      SourceCurrentNativeEdgeWriterGrowth.History after.checked ∧ InternedConstructorTemplates.Valid after.checked.native.machine.heap := by
  cases reads with
  | leaf => exact fun history valid => ⟨history,valid⟩
  | children read => exact SourceCurrentParentNativeHistory.edit_children read

private theorem fold_history {formulas solver records values before memo results after saved memos final}
    {actual : SourceCurrentAllocatedClassPass.Fold (width := width) records values before memo results after saved}
    (reads : SourceCurrentAllocatedClassPass.FoldReads formulas solver actual memos final) :
    SourceCurrentNativeEdgeWriterGrowth.History before → InternedConstructorTemplates.Valid before.native.machine.heap →
      SourceCurrentNativeEdgeWriterGrowth.History after ∧ InternedConstructorTemplates.Valid after.native.machine.heap := by
  induction reads with
  | nil => exact fun history valid => ⟨history,valid⟩
  | cons first last ih =>
    intro history valid
    obtain ⟨current,currentValid⟩ := ih history valid
    cases last with
    | edit lower => exact list_history lower current currentValid

/-- Actual child and class suffixes retain the selected leaf's exact writer at the full reader. -/
theorem selected_leaf {formulas solver record values before memo results after saved memos final index result path}
    {records finalResults finalSaved completed} {reader : Checked width}
    {remaining : SourceCurrentAllocatedClassPass.Fold (width := width) records results after saved finalResults reader finalSaved}
    (selected : SourceCurrentClassSelectedChildLineage.Selection formulas solver record values before memo results after saved
      memos final index result (.editAt path) reader.native.machine.heap)
    (reads : SourceCurrentAllocatedClassPass.FoldReads formulas solver remaining final completed) :
    ∃ (original : Value Symbol Guard) (start finish : Shared width) (current returned : Memos) (leafInventory : Inventory),
    ∃ _leaf : SourceCurrentAllocatedSharedTargetLeaf.Receipt formulas solver leafInventory record values
      before.native.machine.heap path original start result finish current returned,
    ∃ (target : Value Symbol Guard) (middle : Shared width) (queryInventory : Inventory) (handle : Nat),
      values[index]? = some original ∧ original.free = [] ∧ target.free = [] ∧
      SourceCurrentAllocatedTargetQuery.Receipt formulas solver queryInventory target original middle.checked result finish.checked returned ∧
      SourceCurrentAllocatedSharedTargetState.SlotReceipt width formulas solver record values
        finish.checked.native.machine.heap finish.memo path target ∧
      SourceCurrentNativeEdgeWriterGrowth.History start.checked ∧
      SourceCurrentNativeEdgeWriterGrowth.History middle.checked ∧
      SourceCurrentNativeEdgeWriterGrowth.History finish.checked ∧
      Grows start.checked.native.machine.heap reader.native.machine.heap ∧
      Grows finish.checked.native.machine.heap reader.native.machine.heap ∧
      SourceCurrentNativeEdgeWriterGrowth.History reader ∧
      Retained finish.checked.native reader.native ∧
      finish.checked.native.nodes.cells handle = some ⟨⟨IntersectionEmptyDomain.emptyDomain,target,original⟩,.returned result⟩ ∧
      reader.native.nodes.cells handle = some ⟨⟨IntersectionEmptyDomain.emptyDomain,target,original⟩,.returned result⟩ ∧
      SourceCurrentNativeWriterReadyRetention.Written (width := width) handle
        ⟨IntersectionEmptyDomain.emptyDomain,target,original⟩ result reader.native := by
  obtain ⟨entries,shared,start,finish,current,returned,original,startInventory,finishInventory,
    earlier,call,later,built,sameState,sameMemo,output,input,found,prefixRead,callRead,suffixRead,
    safe,startReady,finishReady,startHistory,finishHistory,first,middle,last,readerGrowth⟩ := selected
  have childRetained := edit_children suffixRead
  rw [sameState] at childRetained
  have kept := childRetained.trans (class_fold reads)
  have childHistory := SourceCurrentParentNativeHistory.edit_children suffixRead finishHistory
    finishReady.checked.semantic.ready.semantic.1.normal.facts.coherent.valid
  rw [sameState] at childHistory
  have readerHistory := (fold_history reads childHistory.1 childHistory.2).1
  have closed : original.free = [] := by
    simpa only [SourceEqualityProjectionPathDomain.NodeClosed] using
      safe [] path (by simp [SourceEqualityEditLeafPaths.leaves])
  cases callRead with
  | leaf receipt =>
    obtain ⟨target,forced,forceInventory,queryInventory,base,force,query,shape,slot,
      forcedHistory,resultHistory,forcedGood,resultGood,forceGrowth,queryGrowth,origin⟩ :=
      SourceCurrentSharedLeafNativeLineage.leaf receipt.reads startHistory
    obtain ⟨handle,returnedCell,written⟩ := origin.returned force.closed closed
    have present : finish.targets path = some target := by
      rw [shape]
      exact force.present
    have finishGrowth := grows_trans last readerGrowth
    have currentCell := kept.nodes handle ⟨IntersectionEmptyDomain.emptyDomain,target,original⟩ result returnedCell
    obtain ⟨writerBefore,writerAfter,fuel,good,ready,owner,body,retained,finished,firstGrowth,lastGrowth,cells⟩ := written
    have currentWriter : SourceCurrentNativeWriterReadyRetention.Written (width := width) handle
        ⟨IntersectionEmptyDomain.emptyDomain,target,original⟩ result reader.native :=
      ⟨writerBefore,writerAfter,fuel,good,ready,owner,body,retained,finished,
        grows_trans firstGrowth finishGrowth,grows_trans lastGrowth finishGrowth,cells.trans kept⟩
    exact ⟨original,start,finish,current,returned,_,receipt,target,forced,queryInventory,handle,
      input,closed,force.closed,query,receipt.ready.receipts path target present,startHistory,forcedHistory,resultHistory,
      grows_trans middle finishGrowth,finishGrowth,readerHistory,kept,returnedCell,currentCell,currentWriter⟩

end MicroCFTA.SourceCurrentNativeReaderRetention
