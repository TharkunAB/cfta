import MicroCFTA.SourceCurrentParentNativeHistory
import MicroCFTA.SourceCurrentNativeWriterReadyRetention

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

end MicroCFTA.SourceCurrentNativeReaderRetention
