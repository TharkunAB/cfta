import MicroCFTA.SourceCurrentConstrainedCapRichClassPassSupport

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200

namespace MicroCFTA.RichIndependentChecks
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedClassEdits (Class ClassReads)
open SourceCurrentAllocatedClassPass (Fold FoldReads Pass PassReads)
open SourceCurrentConstrainedCapPaths (ForestSupported)
open SourceCurrentConstrainedCapRequiredSupport (Preserves)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "Plain" => fun guard : Guard => SourceMemoGate.plain guard = true
local notation "NativeStored" => SourceCurrentHereditaryNativeUniversalStore.Stored Plain
local notation "MergeStored" => SourceCurrentHereditaryMerge.Stored Plain
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "CacheCovers" => SourceCurrentMemoMergeLanguage.CacheCovers
local notation "Cap" => SourceCurrentConstrainedCap.Cap Plain
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
variable [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- Overlapping classes use the actual preceding forest and warm stores; only initial masks are supplied. -/
theorem overlapping_classes
    (F : SourceGuards.Formulas FullSyntax.Formula) (S : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (firstRecord secondRecord : SourceEqualityClassOrder.Record) (depth : Nat)
    (common : EqualityNormalize.Path) (firstMember : common ∈ firstRecord.paths) (secondMember : common ∈ secondRecord.paths)
    (firstCoherent : SourceEqualityClassOrder.Coherent firstRecord) (secondCoherent : SourceEqualityClassOrder.Coherent secondRecord)
    (firstActive : EqualityNormalize.Nontrivial firstRecord.paths) (secondActive : EqualityNormalize.Nontrivial secondRecord.paths)
    {values middle results : List (Value Symbol Guard)} {before current after : Checked width}
    {memo currentMemo saved : Memo} {memos currentMemos final : Memos}
    {first : Class firstRecord values before memo middle current currentMemo}
    {second : Class secondRecord middle current currentMemo results after saved}
    (firstReads : ClassReads F S first memos currentMemos) (secondReads : ClassReads F S second currentMemos final)
    (ready : Ready before) (admitted : At F S inventory before)
    (available : Values before.native.machine.heap values) (closed : ClosedValues values)
    (physical : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds F S) ambient memo)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (native : NativeStored before) (merged : MergeStored memo)
    (bounded : ∀ value ∈ values, Cap depth value)
    (firstMasks : ∀ path ∈ firstRecord.paths, ForestSupported Plain (path.map Int.ofNat) values)
    (secondMasks : ∀ path ∈ secondRecord.paths, ForestSupported Plain (path.map Int.ofNat) values) :
    ∃ firstInventory next,
      SourceCurrentAllocatedClassEdits.Receipt F S firstInventory firstRecord values before memo middle current currentMemo memos currentMemos ∧
      SourceCurrentAllocatedClassEdits.Receipt F S next secondRecord middle current currentMemo results after saved currentMemos final ∧
      NativeStored after ∧ MergeStored saved ∧ All₂ (Preserves Plain) values results ∧
      (∀ value ∈ results, Cap depth value) ∧ ClosedValues results ∧
      ForestSupported Plain (common.map Int.ofNat) middle ∧ ForestSupported Plain (common.map Int.ofNat) results ∧
      ∃ fold : Fold [secondRecord, firstRecord] values before memo results after saved,
        FoldReads F S fold memos final ∧
        ∃ pass : Pass [secondRecord, firstRecord] values before memo (EqualityLeafProjectionRuntimeEmpty.propagate results) after saved,
          PassReads F S pass memos final := by
  obtain ⟨firstInventory, firstReceipt, firstNative, firstMerge, firstRelated, firstCaps, firstClosed⟩ :=
    SourceCurrentConstrainedCapRichClassSupport.verified F S inventory firstRecord depth firstCoherent firstActive firstReads
      ready admitted available closed physical covered valid native merged bounded firstMasks
  have reachedMasks := SourceCurrentConstrainedCapForestSupport.record_masks firstRelated secondRecord secondMasks
  obtain ⟨next, secondReceipt, secondNative, secondMerge, secondRelated, secondCaps, secondClosed⟩ :=
    SourceCurrentConstrainedCapRichClassSupport.verified F S firstInventory secondRecord depth secondCoherent secondActive secondReads
      firstReceipt.ready firstReceipt.admitted firstReceipt.available firstClosed firstReceipt.stored firstReceipt.covered
      firstReceipt.globals.valid firstNative firstMerge firstCaps reachedMasks
  have related := SourceCurrentConstrainedCapForestSupport.trans firstRelated secondRelated
  have commonMiddle := SourceCurrentConstrainedCapRequiredSupport.forest_supported Plain firstRelated _ (firstMasks common firstMember)
  have commonAfter := SourceCurrentConstrainedCapRequiredSupport.forest_supported Plain secondRelated _ (reachedMasks common secondMember)
  let fold : Fold [secondRecord, firstRecord] values before memo results after saved := .cons (.cons .nil first) second
  have foldReads : FoldReads F S fold memos final := .cons (.cons .nil firstReads) secondReads
  exact ⟨firstInventory, next, firstReceipt, secondReceipt, secondNative, secondMerge, related, secondCaps, secondClosed,
    commonMiddle, commonAfter, fold, foldReads, .done fold, .done foldReads⟩

#print axioms overlapping_classes
#check @overlapping_classes
end MicroCFTA.RichIndependentChecks
