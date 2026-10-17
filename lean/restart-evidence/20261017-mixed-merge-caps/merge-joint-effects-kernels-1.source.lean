import MicroCFTA.SourceCurrentConstrainedCapMergeJointEffects
import MicroCFTA.SourceMergedComparisonCompletion

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.MergeJointEffectsIntegration
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentConstrainedCapGuardHeap (Heap)
open SourceCurrentMemoMergeGraph (Memo empty)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- A constructed recursive comparison retains guards even when an actual operand is not hereditary. -/
theorem recursive_comparison [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (clear : Guard → Bool) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (guards : Heap annotation before)
    (recursiveEntry ordinaryEntry : Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Value Symbol Guard) (bad : EdgeValue Symbol Guard) (level : Nat)
    (badGuard : ¬ annotation bad.entry.key.constraint)
    (recursiveAvailable : Available before (.mu recursiveEntry body depth ordinary))
    (ordinaryAvailable : Available before (.node ordinaryEntry [bad] level []))
    (recursiveClosed : (Value.mu recursiveEntry body depth ordinary).free = []) :
    ∃ fuel answer after,
      MergedFreshOrdinaryComparison.check clear fuel [] (.mu recursiveEntry body depth ordinary)
        (.node ordinaryEntry [bad] level []) before = .done answer after ∧
      Heap annotation after ∧
      ¬ SourceEqualityAnnotationLanguage.Annotated annotation (.node ordinaryEntry [bad] level []) := by
  obtain ⟨fuel, answer, after, complete, _effects⟩ := SourceMergedComparisonCompletion.check_complete clear before
    semantic [] (.mu recursiveEntry body depth ordinary) (.node ordinaryEntry [bad] level [])
    recursiveAvailable ordinaryAvailable recursiveClosed rfl
  have done := complete fuel (Nat.le_refl _)
  have retained := SourceCurrentConstrainedCapMergeGuardEffects.check_effect annotation clear fuel []
    (.mu recursiveEntry body depth ordinary) (.node ordinaryEntry [bad] level []) before
    semantic costs recursiveAvailable ordinaryAvailable answer after done
  refine ⟨fuel, answer, after, done, retained.guards guards, ?_⟩
  intro annotated
  cases annotated with
  | node entry edges depth free own children => exact badGuard (own bad List.mem_cons_self)

section Allocated
open SourceRecursiveIntersectionKernel
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Inventory" => SourceCurrentAllocatedNativeInventoryState.Inventory
local notation "InventoryAt" => SourceCurrentAllocatedNativeInventoryState.At
local notation "Current" => SourceCurrentConstrainedCapCurrentNative.At
local notation "Receipt" => SourceCurrentAllocatedMerge.Receipt
local notation "literalClear" => SourceCurrentAllocatedMerge.literalClear
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Both Merge calls construct their own receipts and carry the first output into the second actual call. -/
theorem serial_generated_merge {width : Nat}
    (annotation : Guard → Prop)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Checked width) (ready : SourceCurrentConjunctionClassScan.Ready before)
    (admitted : InventoryAt formulas solver inventory before) (current : Current annotation before)
    (input : Value Symbol Guard) (available : Available before.native.machine.heap input)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    ∃ first middle memo firstFinal second after saved final,
      Receipt formulas solver inventory literalClear input before empty first middle memo memos firstFinal ∧
      Receipt formulas solver inventory literalClear first middle memo second after saved firstFinal final ∧
      Current annotation middle ∧ Current annotation after ∧ InventoryAt formulas solver inventory after := by
  have covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers
      (SourceEqualityPCSGuard.holds formulas solver) ambient (empty : Memo Symbol Guard) := by
    intro ambient key entry absent
    cases absent
  obtain ⟨first, middle, memo, firstFinal, firstReceipt⟩ := SourceCurrentAllocatedMerge.source_finite
    formulas solver inventory input before empty ready admitted (SourceCurrentMemoMergeEffects.stored_empty _)
    covered available memos valid
  have firstCurrent := SourceCurrentConstrainedCapMergeJointEffects.merge annotation formulas solver inventory
    firstReceipt.actual ready admitted (SourceCurrentMemoMergeEffects.stored_empty _) available current
  obtain ⟨second, after, saved, final, secondReceipt⟩ := SourceCurrentAllocatedMerge.source_finite
    formulas solver inventory first middle memo firstReceipt.ready firstCurrent.2 firstReceipt.stored
    firstReceipt.covered firstReceipt.available firstFinal firstReceipt.globals.valid
  have secondCurrent := SourceCurrentConstrainedCapMergeJointEffects.merge annotation formulas solver inventory
    secondReceipt.actual firstReceipt.ready firstCurrent.2 firstReceipt.stored firstReceipt.available firstCurrent.1
  exact ⟨first, middle, memo, firstFinal, second, after, saved, final, firstReceipt, secondReceipt,
    firstCurrent.1, secondCurrent⟩

end Allocated
end MicroCFTA.MergeJointEffectsIntegration

#print axioms MicroCFTA.MergeJointEffectsIntegration.recursive_comparison
#check @MicroCFTA.MergeJointEffectsIntegration.recursive_comparison
#print axioms MicroCFTA.MergeJointEffectsIntegration.serial_generated_merge
#check @MicroCFTA.MergeJointEffectsIntegration.serial_generated_merge
