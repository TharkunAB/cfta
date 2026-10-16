import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryClass
namespace FiniteOrdinaryClassKernels
open MicroCFTA Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedClassEdits (Class ClassReads ClassRanges Receipt)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow)
open SourceCurrentAllocatedFiniteOrdinaryNarrow (forest_domain forest_trans)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "Domain" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "MergeStored" => SourceCurrentAllocatedFiniteOrdinaryMergeCache.Stored
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "Covered" => SourceCurrentMemoMergeLanguage.CacheCovers
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory)

/-- A literal compiled empty-forest class makes no calls and retains the complete input state. -/
theorem empty_forest (record : SourceEqualityClassOrder.Record) (coherent : SourceEqualityClassOrder.Coherent record)
    (active : EqualityNormalize.Nontrivial record.paths) (before : Checked width) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (physical : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, Covered (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : NativeStored before.native) (merged : MergeStored memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    ∃ actual : Class record [] before memo [] before memo, ClassReads formulas solver actual memos memos ∧
      ∃ next, Receipt formulas solver next record [] before memo [] before memo memos memos ∧
        NativeStored before.native ∧ MergeStored memo ∧ All₂ NodeNarrow ([] : List (Value Symbol Guard)) [] := by
  let initial := SourceCurrentAllocatedSharedTargetState.initial before memo
  have lower (edits : SourceEqualityEdits.Edits EqualityNormalize.Path) :
      ∃ actual : SourceCurrentAllocatedSharedEditGraph.EditList record [] edits [] initial [] initial,
        SourceCurrentAllocatedSharedEditGraph.ListReads formulas solver before.native.machine.heap actual memos memos := by
    cases edits with
    | editAt target => exact ⟨.leaf, .leaf⟩
    | editBelow entries => exact ⟨.children .nil, .children .nil⟩
  obtain ⟨actualLower, lowerReads⟩ := lower (SourceCurrentAllocatedClassEditPlan.compiled record)
  have actual : Class record [] before memo [] before memo := .edit actualLower
  have reads : ClassReads formulas solver actual memos memos := .edit lowerReads
  obtain ⟨next, receipt, finalNative, finalMerge, related⟩ := SourceCurrentAllocatedFiniteOrdinaryClass.verified
    formulas solver inventory record coherent active reads ready admitted (fun _ absent => nomatch absent) .nil
    physical covered native merged valid
  exact ⟨actual, reads, next, receipt, finalNative, finalMerge, related⟩

/-- A second finite class captures the actual first result and composes original positional bounds. -/
theorem two_classes (first second : SourceEqualityClassOrder.Record)
    (firstCoherent : SourceEqualityClassOrder.Coherent first) (firstActive : EqualityNormalize.Nontrivial first.paths)
    (secondCoherent : SourceEqualityClassOrder.Coherent second) (secondActive : EqualityNormalize.Nontrivial second.paths)
    (values : List (Value Symbol Guard)) (before : Checked width) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (domain : Domain values)
    (physical : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, Covered (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : NativeStored before.native) (merged : MergeStored memo)
    (ranges : ClassRanges first values before memo)
    (laterRanges : ∀ middle step current, Class first values before memo middle step current → ClassRanges second middle step current)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    ∃ middle step current next stageMemos results after saved last final,
      Class first values before memo middle step current ∧ Class second middle step current results after saved ∧
      Receipt formulas solver next first values before memo middle step current memos stageMemos ∧
      Receipt formulas solver last second middle step current results after saved stageMemos final ∧
      NativeStored after.native ∧ MergeStored saved ∧ All₂ NodeNarrow values results := by
  obtain ⟨middle, step, current, next, stageMemos, firstActual, _, firstReceipt, firstNative, firstMerge, firstRelation⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryClass.finite formulas solver inventory first firstCoherent firstActive
      values before memo ready admitted available domain physical covered native merged ranges memos valid
  obtain ⟨results, after, saved, last, final, lastActual, _, lastReceipt, lastNative, lastMerge, lastRelation⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryClass.finite formulas solver next second secondCoherent secondActive
      middle step current firstReceipt.ready firstReceipt.admitted firstReceipt.available (forest_domain firstRelation)
      firstReceipt.stored firstReceipt.covered firstNative firstMerge (laterRanges middle step current firstActual)
      stageMemos firstReceipt.globals.valid
  exact ⟨middle, step, current, next, stageMemos, results, after, saved, last, final,
    firstActual, lastActual, firstReceipt, lastReceipt, lastNative, lastMerge, forest_trans firstRelation lastRelation⟩
end FiniteOrdinaryClassKernels
#print axioms FiniteOrdinaryClassKernels.empty_forest
#check @FiniteOrdinaryClassKernels.empty_forest
#print axioms FiniteOrdinaryClassKernels.two_classes
#check @FiniteOrdinaryClassKernels.two_classes
