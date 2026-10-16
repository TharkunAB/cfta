import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryLocal

namespace FiniteOrdinaryLocalReviewChecks
open MicroCFTA Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConjunctionClassScan (Ready)
open SourceCurrentAllocatedLocalReduction (Reduction Receipt)
open SourceCurrentAllocatedLocalReductionActual (Reads)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "MergeStored" => SourceCurrentAllocatedFiniteOrdinaryMergeCache.Stored
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- The first actual local return supplies the second inventory, all caches, globals, loaded field, and inherited readiness. -/
theorem serial_actual_locals
    (inventory : Inventory) (original : Guard) {budget : Nat} {loaded : Allocated} {inherited : EqValue}
    {values middleValues results : List (Value Symbol Guard)} {before middle after : Checked width}
    {fourth currentFourth savedFourth : Fourth} {memo currentMemo saved : Memo} {memos current final : Memos}
    {first : Reduction budget loaded inherited values before fourth memo middleValues middle currentFourth currentMemo}
    {last : Reduction budget loaded inherited middleValues middle currentFourth currentMemo results after savedFourth saved}
    (firstReads : Reads formulas solver first memos current) (lastReads : Reads formulas solver last current final)
    (ready : Ready before) (admitted : SourceCurrentAllocatedNativeInventoryState.At formulas solver inventory before)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited)
    (available : Values before.native.machine.heap values) (domain : DChildren values)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physicalStored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (firstRanges : SourceCurrentAllocatedLocalReductionActual.Ranges budget loaded inherited values before fourth)
    (lastRanges : SourceCurrentAllocatedLocalReductionActual.Ranges budget loaded inherited middleValues middle currentFourth)
    (nativeStored : NativeStored before.native) (mergeStored : MergeStored memo)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    ∃ firstInventory next,
      Receipt formulas solver firstInventory original loaded inherited values middleValues before middle fourth currentFourth memo currentMemo current ∧
      Receipt formulas solver next original loaded inherited middleValues results middle after currentFourth savedFourth currentMemo saved final ∧
      NativeStored after.native ∧ MergeStored saved ∧ All₂ NodeNarrow values results := by
  obtain ⟨firstInventory, firstReceipt, firstNative, firstMerge, firstRelation⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryLocal.verified formulas solver inventory original firstReads ready admitted
      cached found inheritedReady available domain correct physicalStored covered firstRanges nativeStored mergeStored valid
  have loadedReady := SourceEqualityConstraintFieldLookup.load_ready original before.operations.constraints
    ready.good.operations.constraints cached loaded found
  have readback := SourceEqualityConstraintFieldLookup.load_constructor_receipt original before.operations.constraints cached loaded found
  have guardSame : loaded.guard = original.guard := congrArg SourceSymbolicIndex.Constraint.guard loadedReady.2
  have loadedSame : (⟨loaded.stored, original.guard⟩ : Allocated) = loaded := by
    cases loaded
    simp_all only
  have foundMiddle : SourceEqualityConstraintFieldLookup.load original middle.operations.constraints = .ok (some loaded) := by
    simpa only [loadedSame] using SourceEqualityConstraintFieldLookup.load_of_stored original middle.operations.constraints
      loaded.stored readback (loadedReady.1.grows firstReceipt.effects.grows.constraint_growth).1
  obtain ⟨next, lastReceipt, native, merged, lastRelation⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryLocal.verified formulas solver firstInventory original lastReads firstReceipt.ready firstReceipt.admitted
      cached foundMiddle (inheritedReady.grows firstReceipt.effects.grows.constraint_growth) firstReceipt.available
      (SourceCurrentAllocatedFiniteOrdinaryNarrow.forest_domain firstRelation) firstReceipt.correct firstReceipt.stored firstReceipt.covered
      lastRanges firstNative firstMerge firstReceipt.globals
  exact ⟨firstInventory, next, firstReceipt, lastReceipt, native, merged,
    SourceCurrentAllocatedFiniteOrdinaryNarrow.forest_trans firstRelation lastRelation⟩

/-- The actual erasure prefix requires no Scan, projection, merge, or native range premise. -/
theorem erasure_without_ranges
    (inventory : Inventory) (budget : Nat) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo) (memos : Memos)
    (branch : (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited before.operations).1 = .ok .emptyChildren)
    (ready : Ready before) (admitted : SourceCurrentAllocatedNativeInventoryState.At formulas solver inventory before)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited)
    (available : Values before.native.machine.heap values) (domain : DChildren values)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physicalStored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (nativeStored : NativeStored before.native) (mergeStored : MergeStored memo)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    ∃ next,
      Receipt formulas solver next original loaded inherited values (EqualityLeafProjectionRuntimeEmpty.erase values)
        before (SourceCurrentAllocatedPrecheck.state before loaded inherited) fourth fourth memo memo memos ∧
      NativeStored (SourceCurrentAllocatedPrecheck.state before loaded inherited).native ∧ MergeStored memo ∧
      All₂ NodeNarrow values (EqualityLeafProjectionRuntimeEmpty.erase values) := by
  let actual : Reduction budget loaded inherited values before fourth memo (EqualityLeafProjectionRuntimeEmpty.erase values)
      (SourceCurrentAllocatedPrecheck.state before loaded inherited) fourth memo := .emptyChildren branch
  have reads : Reads formulas solver actual memos memos := .emptyChildren (actual := branch)
  have ranges : SourceCurrentAllocatedLocalReductionActual.Ranges budget loaded inherited values before fourth := by
    intro records impossible
    rw [branch] at impossible
    cases impossible
  exact SourceCurrentAllocatedFiniteOrdinaryLocal.verified formulas solver inventory original reads ready admitted cached found
    inheritedReady available domain correct physicalStored covered ranges nativeStored mergeStored valid

#print axioms serial_actual_locals
#check @serial_actual_locals
#print axioms erasure_without_ranges
#check @erasure_without_ranges
end FiniteOrdinaryLocalReviewChecks
