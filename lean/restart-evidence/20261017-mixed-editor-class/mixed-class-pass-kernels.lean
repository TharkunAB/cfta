import MicroCFTA.SourceCurrentConstrainedCapMixedClassPass

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace MicroCFTA.MixedClassPassKernels
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedClassPass (Fold FoldReads Pass PassReads Receipt Ranges)
open SourceEqualityProjectionPathDomain (ForestClosed)
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "Current" => SourceCurrentConstrainedCapCurrentNative.At Plain
local notation "MergeStored" => SourceCurrentConstrainedCapMemoMerge.Stored Plain
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "CacheCovers" => SourceCurrentMemoMergeLanguage.CacheCovers
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- Initial operational checks construct both classes and the final pass at their exact returns. -/
theorem constructed_two_class_pass
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (first second : SourceEqualityClassOrder.Record)
    (coherent : ∀ record ∈ [first, second], SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ [first, second], EqualityNormalize.Nontrivial record.paths)
    (values : List (Value Symbol Guard)) (before : Checked width) (memo : Memo)
    (ranges : Ranges [first, second] values before memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ record ∈ [first, second], ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (physical : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (current : Current before) (merged : MergeStored memo) (depth : Nat)
    (bounded : ∀ value ∈ values, Cap Plain depth value) :
    ∃ middle after saved next final,
      ∃ fold : Fold [first, second] values before memo middle after saved,
      ∃ pass : Pass [first, second] values before memo
          (EqualityLeafProjectionRuntimeEmpty.propagate middle) after saved,
        FoldReads formulas solver fold memos final ∧ PassReads formulas solver pass memos final ∧
        Receipt formulas solver next [first, second] values before memo
          (EqualityLeafProjectionRuntimeEmpty.propagate middle) after saved memos final ∧
        Current after ∧ MergeStored saved ∧
        (∀ value ∈ EqualityLeafProjectionRuntimeEmpty.propagate middle,
          Cap Plain (SourceCurrentConstrainedCapMixedClass.classDepth first
            (SourceCurrentConstrainedCapMixedClass.classDepth second depth)) value) := by
  obtain ⟨middle, after, saved, _inventory, final, actual, reads, _receipt⟩ :=
    SourceCurrentAllocatedClassPass.fold_complete formulas solver inventory ranges coherent active ready admitted
      available domains physical covered memos valid
  let pass : Pass [first, second] values before memo
      (EqualityLeafProjectionRuntimeEmpty.propagate middle) after saved := .done actual
  have passReads : PassReads formulas solver pass memos final := .done reads
  obtain ⟨next, receipt, currentAfter, mergedAfter, caps⟩ :=
    SourceCurrentConstrainedCapMixedClassPass.pass formulas solver inventory depth passReads coherent active ready admitted
      available domains physical covered valid current merged bounded
  exact ⟨middle, after, saved, next, final, actual, pass, reads, passReads, receipt, currentAfter, mergedAfter, caps⟩

/-- A supplied actual tail provides the next class capture, selected domains, stores, and depth. -/
theorem actual_tail_then_head
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (first second : SourceEqualityClassOrder.Record)
    (coherent : ∀ record ∈ [first, second], SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ [first, second], EqualityNormalize.Nontrivial record.paths)
    {values middle results : List (Value Symbol Guard)} {before step after : Checked width}
    {memo currentMemo saved : Memo} {memos stepMemos final : Memos}
    {tail : SourceCurrentAllocatedClassEdits.Class second values before memo middle step currentMemo}
    {head : SourceCurrentAllocatedClassEdits.Class first middle step currentMemo results after saved}
    (tailReads : SourceCurrentAllocatedClassEdits.ClassReads formulas solver tail memos stepMemos)
    (headReads : SourceCurrentAllocatedClassEdits.ClassReads formulas solver head stepMemos final)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ record ∈ [first, second], ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (physical : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (current : Current before) (merged : MergeStored memo) (depth : Nat)
    (bounded : ∀ value ∈ values, Cap Plain depth value) :
    ∃ tailInventory next,
      SourceCurrentAllocatedClassEdits.Receipt formulas solver tailInventory second values before memo middle step currentMemo memos stepMemos ∧
      SourceCurrentAllocatedClassEdits.Receipt formulas solver next first middle step currentMemo results after saved stepMemos final ∧
      Current step ∧ MergeStored currentMemo ∧ Current after ∧ MergeStored saved ∧
      ∀ value ∈ results, Cap Plain (SourceCurrentConstrainedCapMixedClass.classDepth first
        (SourceCurrentConstrainedCapMixedClass.classDepth second depth)) value := by
  obtain ⟨tailInventory, tailReceipt, tailCurrent, tailMerged, tailCaps⟩ :=
    SourceCurrentConstrainedCapMixedClass.verified formulas solver inventory second (coherent _ (by simp))
      (active _ (by simp)) tailReads ready admitted available (domains _ (by simp)) physical covered valid
      current merged depth bounded
  obtain ⟨next, headReceipt, headCurrent, headMerged, headCaps⟩ :=
    SourceCurrentConstrainedCapMixedClass.verified formulas solver tailInventory first (coherent _ (by simp))
      (active _ (by simp)) headReads tailReceipt.ready tailReceipt.admitted tailReceipt.available
      (fun path member => tailReceipt.domains _ (domains first List.mem_cons_self path member))
      tailReceipt.stored tailReceipt.covered tailReceipt.globals.valid tailCurrent tailMerged _ tailCaps
  exact ⟨tailInventory, next, tailReceipt, headReceipt, tailCurrent, tailMerged, headCurrent, headMerged, headCaps⟩

#print axioms constructed_two_class_pass
#check @constructed_two_class_pass
#print axioms actual_tail_then_head
#check @actual_tail_then_head
end MicroCFTA.MixedClassPassKernels
