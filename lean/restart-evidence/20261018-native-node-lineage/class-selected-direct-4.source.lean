import MicroCFTA.SourceCurrentClassPassPhaseLineage
import MicroCFTA.SourceCurrentSharedEditChildLineage
import MicroCFTA.SourceCurrentSharedLeafNativeLineage
import MicroCFTA.SourceCurrentNativeNodeRowLineage

/-!+# Actual selected child calls inside class phases

The class compiler supplies the selected child map. Actual class reads
retain the preceding and following child executions. Initial supported
facts derive the selected call's readiness and native histories. Later
class phases retain growth into the actual final reader.
-/
namespace MicroCFTA.SourceCurrentClassSelectedChildLineage
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityEdits SourceCurrentEditDomains
open SourceCurrentAllocatedSharedEditGraph
open SourceCurrentAllocatedClassEditPlan
open SourceCurrentAllocatedClassEdits (Class ClassReads)
open SourceCurrentAllocatedClassPass (Fold FoldReads)
open SourceCurrentNativeEdgeWriterGrowth (History)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Inventory" => SourceCurrentAllocatedNativeInventoryState.Inventory
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "SharedReady" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "initial" => SourceCurrentAllocatedSharedTargetState.initial
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- One class occurrence retains its actual selected child call and both chronological schedules. -/
def Selection (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (before : Checked width) (memo : Memo) (results : List (Value Symbol Guard))
    (after : Checked width) (saved : Memo) (memos final : Memos)
    (index : Nat) (result : Value Symbol Guard) (edits : Edits EqualityNormalize.Path) (reader : Heap) : Prop :=
  ∃ entries, ∃ shared start finish : SharedState width, ∃ current returned : Memos,
  ∃ original : Value Symbol Guard, ∃ startInventory finishInventory : Inventory,
  ∃ earlier : EditChildren record values entries 0 (values.take index)
      (initial before memo) (results.take index) start,
  ∃ call : EditNode record values edits original start result finish,
  ∃ later : EditChildren record values entries (0 + index + 1)
      (values.drop (index + 1)) finish (results.drop (index + 1)) shared,
    compiled record = .editBelow entries ∧
    shared.checked = after ∧ shared.memo = saved ∧
    results[index]? = some result ∧ values[index]? = some original ∧
    SourceEqualityNeededMap.lookup (index : Int) entries = some edits ∧
    ChildrenReads formulas solver before.native.machine.heap earlier memos current ∧
    NodeReads formulas solver before.native.machine.heap call current returned ∧
    ChildrenReads formulas solver before.native.machine.heap later returned final ∧
    Safe edits original ∧
    SharedReady formulas solver startInventory record values before.native.machine.heap start ∧
    SharedReady formulas solver finishInventory record values before.native.machine.heap finish ∧
    History start.checked ∧ History finish.checked ∧
    Grows before.native.machine.heap start.checked.native.machine.heap ∧
    Grows start.checked.native.machine.heap finish.checked.native.machine.heap ∧
    Grows finish.checked.native.machine.heap after.native.machine.heap ∧
    Grows after.native.machine.heap reader

/-- A later actual heap retains the same selected call, captured histories, and source indices. -/
theorem Selection.grows {formulas solver record values before memo results after saved memos final index result edits}
    {reader next : Heap}
    (selected : Selection (width := width) formulas solver record values before memo results after saved
      memos final index result edits reader) (growth : Grows reader next) :
    Selection formulas solver record values before memo results after saved memos final index result edits next := by
  obtain ⟨entries,shared,start,finish,current,returned,original,startInventory,finishInventory,
    earlier,call,later,built,sameState,sameMemo,output,input,found,prefixRead,callRead,suffixRead,
    safe,startReady,finishReady,startHistory,finishHistory,first,middle,last,readerGrowth⟩ := selected
  exact ⟨entries,shared,start,finish,current,returned,original,startInventory,finishInventory,
    earlier,call,later,built,sameState,sameMemo,output,input,found,prefixRead,callRead,suffixRead,
    safe,startReady,finishReady,startHistory,finishHistory,first,middle,last,grows_trans readerGrowth growth⟩

private theorem list_selected {formulas solver inventory record values before memo results shared memos final edits}
    {actual : EditList (width := width) record values edits values (initial before memo) results shared}
    (reads : ListReads formulas solver before.native.machine.heap actual memos final)
    (same : compiled record = edits)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (ready : Ready before)
    (admitted : SourceCurrentAllocatedNativeInventoryState.At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) values)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers
      (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) (history : History before)
    {index : Nat} {result : Value Symbol Guard} {selectedEdits : Edits EqualityNormalize.Path}
    (output : results[index]? = some result)
    (selected : ∀ entries, compiled record = .editBelow entries →
      SourceEqualityNeededMap.lookup (index : Int) entries = some selectedEdits) :
    Selection formulas solver record values before memo results shared.checked shared.memo memos final
      index result selectedEdits shared.checked.native.machine.heap := by
  cases reads with
  | leaf => exact False.elim (compiled_not_leaf record coherent active _ same)
  | children childReads =>
      have initialReady := SourceCurrentAllocatedSharedTargetState.initial_ready formulas solver inventory record values
        before.native.machine.heap before memo ready admitted
        (SourceEqualityRequiredCache.pure_keeps _ ready.semantic.ready) stored covered
      obtain ⟨original,start,finish,current,returned,startInventory,finishInventory,earlier,call,later,
        input,prefixRead,callRead,suffixRead,startReady,finishReady,startHistory,finishHistory,first,middle,last⟩ :=
        SourceCurrentSharedEditChildLineage.selected childReads inventory
          (by simpa only [same] using compiled_populated record)
          (by simpa only [same] using compiled_allowed record) initialReady available
          (compiled_safe record coherent values domains _ same) valid history output
          (by simpa using selected _ same)
      exact ⟨_,_,start,finish,current,returned,original,startInventory,finishInventory,
        earlier,call,later,same,rfl,rfl,output,input,selected _ same,
        prefixRead,callRead,suffixRead,
        compiled_safe record coherent values domains _ same index selectedEdits
          (by simpa using selected _ same) original input,
        startReady,finishReady,startHistory,finishHistory,
        first,middle,last,grows_refl _⟩

/-- Initial class support derives an exact selected child receipt from the actual compiled class reads. -/
theorem class_selected {formulas solver inventory record values before memo results after saved memos final}
    {actual : Class (width := width) record values before memo results after saved}
    (reads : ClassReads formulas solver actual memos final)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (ready : Ready before)
    (admitted : SourceCurrentAllocatedNativeInventoryState.At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) values)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers
      (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) (history : History before)
    {index : Nat} {result : Value Symbol Guard} {edits : Edits EqualityNormalize.Path}
    (output : results[index]? = some result)
    (selected : ∀ entries, compiled record = .editBelow entries →
      SourceEqualityNeededMap.lookup (index : Int) entries = some edits) :
    Selection formulas solver record values before memo results after saved memos final
      index result edits after.native.machine.heap := by
  cases reads with
  | edit lower =>
      exact list_selected lower rfl coherent active ready admitted available domains stored covered valid history output selected

/-- A selected leaf derives its historical target, exact native writer, and ordinary-row child lineage. -/
theorem Selection.native {formulas solver record values before memo results after saved memos final index result path reader}
    (selected : Selection (width := width) formulas solver record values before memo results after saved
      memos final index result (.editAt path) reader) :
    ∃ (original : Value Symbol Guard) (start finish : SharedState width) (current returned : Memos)
      (leafInventory : Inventory),
    ∃ leaf : SourceCurrentAllocatedSharedTargetLeaf.Receipt formulas solver leafInventory record values
      before.native.machine.heap path original start result finish current returned,
    ∃ (target : Value Symbol Guard) (middle : SharedState width) (queryInventory : Inventory) (handle : Nat),
      values[index]? = some original ∧ original.free = [] ∧ target.free = [] ∧
      SourceCurrentAllocatedTargetQuery.Receipt formulas solver queryInventory target original middle.checked
        result finish.checked returned ∧
      SourceCurrentAllocatedSharedTargetState.SlotReceipt width formulas solver record values
        finish.checked.native.machine.heap finish.memo path target ∧
      History start.checked ∧ History middle.checked ∧ History finish.checked ∧
      Grows start.checked.native.machine.heap reader ∧ Grows finish.checked.native.machine.heap reader ∧
      finish.checked.native.nodes.cells handle =
        some ⟨⟨IntersectionEmptyDomain.emptyDomain,target,original⟩,.returned result⟩ ∧
      SourceCurrentNativeWriterReadyRetention.Written (width := width) handle
        ⟨IntersectionEmptyDomain.emptyDomain,target,original⟩ result finish.checked.native ∧
      ∀ (leftEntry rightEntry : Interned InternedBinderProtocol.NodeKey)
        (leftRows rightRows : List (EdgeValue Symbol Guard)) (leftDepth rightDepth : Nat)
        (leftFree rightFree : List InternedBinderProtocol.Reference),
        target = .node leftEntry leftRows leftDepth leftFree →
        original = .node rightEntry rightRows rightDepth rightFree →
        SourceRecursiveIntersectionControl.decision IntersectionEmptyDomain.emptyDomain.key target original = .ordinary →
        ∀ (rowIndex : Nat) (row : EdgeValue Symbol Guard),
          (InternedEdgeResidency.nodeEdges result)[rowIndex]? = some row →
          ∀ (childIndex : Nat) (value : Value Symbol Guard), row.children[childIndex]? = some value →
            SourceCurrentNativeNodeRowLineage.Lineage finish.checked handle
              ⟨IntersectionEmptyDomain.emptyDomain,target,original⟩ result rowIndex row childIndex value := by
  obtain ⟨entries,shared,start,finish,current,returned,original,startInventory,finishInventory,
    earlier,call,later,built,sameState,sameMemo,output,input,found,prefixRead,callRead,suffixRead,
    safe,startReady,finishReady,startHistory,finishHistory,first,middle,last,readerGrowth⟩ := selected
  have closed : original.free = [] := by
    exact safe [] path (by simp [SourceEqualityEdits.leaves])
  cases callRead with
  | leaf receipt =>
      obtain ⟨target,forced,forceInventory,queryInventory,base,force,query,shape,slot,
        forcedHistory,resultHistory,forcedGood,resultGood,forceGrowth,queryGrowth,origin⟩ :=
        SourceCurrentSharedLeafNativeLineage.leaf receipt.reads startHistory
      obtain ⟨handle,returnedCell,written⟩ := origin.returned force.closed closed
      have present : finish.targets path = some target := by
        rw [shape]
        exact force.present
      refine ⟨original,start,finish,current,returned,_,receipt,target,forced,queryInventory,handle,
        input,closed,force.closed,query,receipt.ready.receipts path target present,
        startHistory,forcedHistory,resultHistory,
        grows_trans middle (grows_trans last readerGrowth),grows_trans last readerGrowth,
        returnedCell,written,?_⟩
      intro leftEntry rightEntry leftRows rightRows leftDepth rightDepth leftFree rightFree left right branch
        rowIndex row rowSelected childIndex value childSelected
      exact SourceCurrentNativeNodeRowLineage.ordinary resultHistory handle
        ⟨IntersectionEmptyDomain.emptyDomain,target,original⟩ result returnedCell
        leftEntry rightEntry leftRows rightRows leftDepth rightDepth leftFree rightFree left right branch
        rowIndex row rowSelected childIndex value childSelected

/-- Every selected class phase derives its child-call receipts at the actual complete fold reader. -/
theorem fold_selected {formulas solver records values before memo results after saved memos final}
    {actual : Fold (width := width) records values before memo results after saved}
    (reads : FoldReads formulas solver actual memos final)
    (inventory : Inventory)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : Ready before)
    (admitted : SourceCurrentAllocatedNativeInventoryState.At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths,
      SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) values)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers
      (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) (history : History before)
    {classIndex : Nat} {record : SourceEqualityClassOrder.Record} (chosen : records[classIndex]? = some record) :
    ∃ phaseValues phaseState phaseMemo phaseMemos headValues headState headMemo headMemos,
    ∃ tail : Fold (records.drop (classIndex + 1)) values before memo phaseValues phaseState phaseMemo,
    ∃ call : Class record phaseValues phaseState phaseMemo headValues headState headMemo,
    ∃ later : Fold (records.take classIndex) headValues headState headMemo results after saved,
      FoldReads formulas solver tail memos phaseMemos ∧
      ClassReads formulas solver call phaseMemos headMemos ∧
      FoldReads formulas solver later headMemos final ∧
      History phaseState ∧ History headState ∧ History after ∧
      ∀ (index : Nat) (result : Value Symbol Guard) (edits : Edits EqualityNormalize.Path),
        headValues[index]? = some result →
        (∀ entries, compiled record = .editBelow entries →
          SourceEqualityNeededMap.lookup (index : Int) entries = some edits) →
        Selection formulas solver record phaseValues phaseState phaseMemo headValues headState headMemo
          phaseMemos headMemos index result edits after.native.machine.heap := by
  obtain ⟨phaseValues,phaseState,phaseMemo,phaseMemos,headValues,headState,headMemo,headMemos,
    tail,call,later,phaseInventory,headInventory,finalInventory,tailReads,callReads,laterReads,
    tailReceipt,callReceipt,laterReceipt,phaseHistory,headHistory,finalHistory,first,last⟩ :=
    SourceCurrentClassPassPhaseLineage.fold_phase reads inventory coherent active ready admitted available
      domains stored covered valid history chosen
  refine ⟨phaseValues,phaseState,phaseMemo,phaseMemos,headValues,headState,headMemo,headMemos,
    tail,call,later,tailReads,callReads,laterReads,phaseHistory,headHistory,finalHistory,?_⟩
  intro index result edits output selected
  have member := List.mem_of_getElem? chosen
  exact (class_selected callReads (coherent record member) (active record member)
    tailReceipt.ready tailReceipt.admitted tailReceipt.available
    (fun path present => tailReceipt.domains _ (domains record member path present))
    tailReceipt.stored tailReceipt.covered tailReceipt.globals.valid phaseHistory output selected).grows
      laterReceipt.effects.keeps.growth

end MicroCFTA.SourceCurrentClassSelectedChildLineage
