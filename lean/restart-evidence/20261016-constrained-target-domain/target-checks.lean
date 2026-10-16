import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTarget

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.funBinderTypes true

#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTarget.forest_closed
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTarget.forest_closed
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTarget.operand
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTarget.operand
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTarget.fold
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTarget.fold
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTarget.target
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTarget.target
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTarget.finite
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTarget.finite

namespace FiniteOrdinaryTargetChecks
open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedTargetGraph SourceCurrentAllocatedTargetComplete
open SourceCurrentMemoMergeLanguage (CacheCovers)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "MergeStored" => SourceCurrentAllocatedFiniteOrdinaryMergeCache.Stored
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
variable (inventory : Inventory) (values : List (Value Symbol Guard)) (before : Checked width) (memo : Memo)
variable (ready : Ready before) (admitted : At formulas solver inventory before)
variable (available : InternedNestedProvenance.Values before.native.machine.heap values) (domain : DChildren values)
variable (physicalStored : PhysicalStored before.native.machine.heap memo) (mergeStored : MergeStored memo)
variable (nativeStored : NativeStored before.native)
variable (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
variable (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)

omit [DecidableEq Symbol] in
include ready available domain in
/-- Arbitrary signed paths need no separately supplied selected domain. -/
theorem support (path : List Int) : SourceEqualityProjectionPathDomain.ForestClosed path values :=
  SourceCurrentAllocatedFiniteOrdinaryTarget.forest_closed _ ready.semantic values available domain path

include inventory ready admitted available domain physicalStored mergeStored nativeStored covered valid

/-- An empty actual target preserves the exact checked state and both warm structural tables. -/
theorem empty_target :
    ∃ next final, TargetReads formulas solver (Target.nil (values := values) (before := before) (memo := memo)) memos final ∧
      Receipt formulas solver next values [] before memo .empty before memo memos final ∧
      MergeStored memo ∧ NativeStored before.native ∧ DNode (.empty : Value Symbol Guard) := by
  exact SourceCurrentAllocatedFiniteOrdinaryTarget.target formulas solver inventory Target.nil
    ready admitted available domain physicalStored mergeStored nativeStored covered trivial memos valid

/-- A root-only target completes without any native word-range check. -/
theorem root_singleton :
    ∃ result after saved next final, ∃ actual : Target values [[]] before memo result after saved,
      TargetReads formulas solver actual memos final ∧
      Receipt formulas solver next values [[]] before memo result after saved memos final ∧
      MergeStored saved ∧ NativeStored after.native ∧ DNode result := by
  exact SourceCurrentAllocatedFiniteOrdinaryTarget.finite formulas solver inventory values [[]] before memo
    ready admitted available domain physicalStored mergeStored nativeStored covered trivial memos valid

/-- The first target's generated result becomes the captured forest of a second actual target. -/
theorem generated_next (paths : List (List Int)) (ranges : TargetRanges values paths before memo) :
    ∃ result middle saved next current, ∃ actual : Target values paths before memo result middle saved,
      TargetReads formulas solver actual memos current ∧
      Receipt formulas solver next values paths before memo result middle saved memos current ∧
      ∃ output after finalMemo finalInventory finalGlobals,
      ∃ second : Target [result] [[]] middle saved output after finalMemo,
        TargetReads formulas solver second current finalGlobals ∧
        Receipt formulas solver finalInventory [result] [[]] middle saved output after finalMemo current finalGlobals ∧
        MergeStored finalMemo ∧ NativeStored after.native ∧ DNode output := by
  obtain ⟨result, middle, saved, next, current, actual, reads, receipt, retained, native, resultDomain⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryTarget.finite formulas solver inventory values paths before memo
      ready admitted available domain physicalStored mergeStored nativeStored covered ranges memos valid
  obtain ⟨output, after, finalMemo, finalInventory, finalGlobals, second, secondReads, secondReceipt, finalMerge, finalNative, outputDomain⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryTarget.finite formulas solver next [result] [[]] middle saved
      receipt.ready receipt.admitted (by intro value member; cases List.mem_singleton.mp member; exact receipt.available)
      (.cons resultDomain .nil) receipt.stored retained native receipt.covered trivial current receipt.globals.valid
  exact ⟨result, middle, saved, next, current, actual, reads, receipt,
    output, after, finalMemo, finalInventory, finalGlobals, second, secondReads, secondReceipt, finalMerge, finalNative, outputDomain⟩

end FiniteOrdinaryTargetChecks

#print axioms FiniteOrdinaryTargetChecks.support
#check @FiniteOrdinaryTargetChecks.support
#print axioms FiniteOrdinaryTargetChecks.empty_target
#check @FiniteOrdinaryTargetChecks.empty_target
#print axioms FiniteOrdinaryTargetChecks.root_singleton
#check @FiniteOrdinaryTargetChecks.root_singleton
#print axioms FiniteOrdinaryTargetChecks.generated_next
#check @FiniteOrdinaryTargetChecks.generated_next
