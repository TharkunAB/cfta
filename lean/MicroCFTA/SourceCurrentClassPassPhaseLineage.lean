import MicroCFTA.SourceCurrentAllocatedClassPass
import MicroCFTA.SourceCurrentParentNativeHistory

/-!
# Indexed phases of actual class right folds

Each source occurrence retains the exact completed tail, class call, and
later head schedule. Initial supported inputs derive the captured states,
heap growth, and native histories. This result does not prove termination.
-/
namespace MicroCFTA.SourceCurrentClassPassPhaseLineage
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityProjectionPathDomain
open SourceCurrentAllocatedClassPass (Fold FoldReads Pass PassReads)
open SourceCurrentAllocatedClassEdits (Class ClassReads)
open SourceCurrentNativeEdgeWriterGrowth (History)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Inventory" => SourceCurrentAllocatedNativeInventoryState.Inventory
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- An indexed source occurrence retains its actual tail and later head schedule. -/
theorem fold_indexed {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {records values before memo results after saved memos final}
    {actual : Fold (width := width) records values before memo results after saved}
    (reads : FoldReads formulas solver actual memos final)
    {index : Nat} {record : SourceEqualityClassOrder.Record}
    (selected : records[index]? = some record) :
    ∃ phaseValues phaseState phaseMemo phaseMemos headValues headState headMemo headMemos,
    ∃ tail : Fold (records.drop (index + 1)) values before memo phaseValues phaseState phaseMemo,
    ∃ call : Class record phaseValues phaseState phaseMemo headValues headState headMemo,
    ∃ later : Fold (records.take index) headValues headState headMemo results after saved,
      FoldReads formulas solver tail memos phaseMemos ∧
      ClassReads formulas solver call phaseMemos headMemos ∧
      FoldReads formulas solver later headMemos final := by
  induction reads generalizing index record with
  | nil => simp at selected
  | @cons records values before memo middle step current own results after saved memos stepMemos final
      tail head tailReads headReads ih =>
      cases index with
      | zero =>
          have same : own = record := by simpa using selected
          subst record
          exact ⟨middle, step, current, stepMemos, results, after, saved, final,
            tail, head, .nil, tailReads, headReads, .nil⟩
      | succ index =>
          obtain ⟨phaseValues, phaseState, phaseMemo, phaseMemos, headValues, headState, headMemo,
            headMemos, earlierTail, call, later, earlierReads, callReads, laterReads⟩ :=
            ih (index := index) (record := record) (by simpa using selected)
          have laterActual : Fold ((own :: records).take (index + 1)) headValues headState headMemo
              results after saved := by
            simpa only [List.take_succ_cons] using Fold.cons later head
          have laterRead : FoldReads formulas solver laterActual headMemos final := by
            exact .cons (tail := later) (head := head) laterReads headReads
          refine ⟨phaseValues, phaseState, phaseMemo, phaseMemos, headValues, headState, headMemo,
            headMemos, ?_, call, laterActual, earlierReads, callReads, laterRead⟩
          simpa only [List.drop_succ_cons] using earlierTail

private theorem fold_history {formulas solver records values before memo results after saved memos final}
    {actual : Fold (width := width) records values before memo results after saved}
    (reads : FoldReads formulas solver actual memos final)
    (history : History before) (ready : Ready before) : History after :=
  SourceCurrentParentNativeHistory.class_pass (PassReads.done (actual := actual) reads) history ready

/-- Initial supported inputs derive both captured phase states and their actual histories. -/
theorem fold_phase {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {records values before memo results after saved memos final}
    {actual : Fold (width := width) records values before memo results after saved}
    (reads : FoldReads formulas solver actual memos final)
    (inventory : Inventory)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : Ready before)
    (admitted : SourceCurrentAllocatedNativeInventoryState.At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers
      (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (history : History before)
    {index : Nat} {record : SourceEqualityClassOrder.Record}
    (selected : records[index]? = some record) :
    ∃ phaseValues phaseState phaseMemo phaseMemos headValues headState headMemo headMemos,
    ∃ tail : Fold (records.drop (index + 1)) values before memo phaseValues phaseState phaseMemo,
    ∃ call : Class record phaseValues phaseState phaseMemo headValues headState headMemo,
    ∃ later : Fold (records.take index) headValues headState headMemo results after saved,
    ∃ phaseInventory headInventory finalInventory,
      FoldReads formulas solver tail memos phaseMemos ∧
      ClassReads formulas solver call phaseMemos headMemos ∧
      FoldReads formulas solver later headMemos final ∧
      SourceCurrentAllocatedClassPass.Receipt formulas solver phaseInventory
        (records.drop (index + 1)) values before memo phaseValues phaseState phaseMemo memos phaseMemos ∧
      SourceCurrentAllocatedClassEdits.Receipt formulas solver headInventory record
        phaseValues phaseState phaseMemo headValues headState headMemo phaseMemos headMemos ∧
      SourceCurrentAllocatedClassPass.Receipt formulas solver finalInventory
        (records.take index) headValues headState headMemo results after saved headMemos final ∧
      History phaseState ∧ History headState ∧ History after ∧
      Grows before.native.machine.heap phaseState.native.machine.heap ∧
      Grows phaseState.native.machine.heap after.native.machine.heap := by
  obtain ⟨phaseValues, phaseState, phaseMemo, phaseMemos, headValues, headState, headMemo, headMemos,
    tail, call, later, tailReads, callReads, laterReads⟩ := fold_indexed reads selected
  have recordMember : record ∈ records := List.mem_iff_getElem?.mpr ⟨index, selected⟩
  obtain ⟨phaseInventory, tailReceipt⟩ := SourceCurrentAllocatedClassPass.Fold.verified
    formulas solver inventory tailReads
    (fun own member => coherent own (List.mem_of_mem_drop member))
    (fun own member => active own (List.mem_of_mem_drop member)) ready admitted available
    (fun own member => domains own (List.mem_of_mem_drop member)) stored covered valid
  obtain ⟨headInventory, callReceipt⟩ := SourceCurrentAllocatedClassEdits.verified
    formulas solver phaseInventory record (coherent record recordMember) (active record recordMember) callReads
    tailReceipt.ready tailReceipt.admitted tailReceipt.available
    (fun path member => tailReceipt.domains _ (domains record recordMember path member))
    tailReceipt.stored tailReceipt.covered tailReceipt.globals.valid
  obtain ⟨finalInventory, laterReceipt⟩ := SourceCurrentAllocatedClassPass.Fold.verified
    formulas solver headInventory laterReads
    (fun own member => coherent own (List.mem_of_mem_take member))
    (fun own member => active own (List.mem_of_mem_take member)) callReceipt.ready callReceipt.admitted callReceipt.available
    (fun own member path found => callReceipt.domains _
      (tailReceipt.domains _ (domains own (List.mem_of_mem_take member) path found)))
    callReceipt.stored callReceipt.covered callReceipt.globals.valid
  have tailHistory := fold_history tailReads history ready
  have headFold : Fold [record] phaseValues phaseState phaseMemo headValues headState headMemo := .cons .nil call
  have headReads : FoldReads formulas solver headFold phaseMemos headMemos :=
    .cons (tail := .nil) (head := call) .nil callReads
  have headHistory := fold_history headReads tailHistory tailReceipt.ready
  have finalHistory := fold_history laterReads headHistory callReceipt.ready
  exact ⟨phaseValues, phaseState, phaseMemo, phaseMemos, headValues, headState, headMemo, headMemos,
    tail, call, later, phaseInventory, headInventory, finalInventory,
    tailReads, callReads, laterReads, tailReceipt, callReceipt, laterReceipt,
    tailHistory, headHistory, finalHistory, tailReceipt.effects.keeps.growth,
    (callReceipt.effects.trans laterReceipt.effects).keeps.growth⟩

end MicroCFTA.SourceCurrentClassPassPhaseLineage
