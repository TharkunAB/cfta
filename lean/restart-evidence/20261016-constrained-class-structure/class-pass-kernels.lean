import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryClassPass
namespace FiniteOrdinaryClassPassKernels
open MicroCFTA Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedClassPass (Pass PassReads Ranges Receipt)
open SourceCurrentAllocatedClassEdits (Class ClassRanges)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow)
open SourceCurrentAllocatedFiniteOrdinaryNarrow (forest_domain forest_trans forest_height)
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

/-- Zero classes still run final Empty propagation with identical complete checked and memo state. -/
theorem nil_pass_erases (values : List (Value Symbol Guard)) (before : Checked width) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap (.empty :: values)) (domain : Domain (.empty :: values))
    (physical : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, Covered (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : NativeStored before.native) (merged : MergeStored memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    let results := EqualityLeafProjectionRuntimeEmpty.propagate (.empty :: values)
    ∃ actual : Pass [] (.empty :: values) before memo results before memo,
      PassReads formulas solver actual memos memos ∧
      ∃ next, Receipt formulas solver next [] (.empty :: values) before memo results before memo memos memos ∧
        NativeStored before.native ∧ MergeStored memo ∧ All₂ NodeNarrow (.empty :: values) results ∧
        results = EqualityLeafProjectionRuntimeEmpty.erase (.empty :: values) ∧ results.length = values.length + 1 := by
  let results := EqualityLeafProjectionRuntimeEmpty.propagate (.empty :: values)
  have actual : Pass [] (.empty :: values) before memo results before memo := .done .nil
  have reads : PassReads formulas solver actual memos memos := .done .nil
  obtain ⟨next, receipt, finalNative, finalMerge, related⟩ := SourceCurrentAllocatedFiniteOrdinaryClassPass.pass
    formulas solver inventory reads (fun _ absent => nomatch absent) (fun _ absent => nomatch absent)
    ready admitted available domain physical covered native merged valid
  have erased : results = EqualityLeafProjectionRuntimeEmpty.erase (.empty :: values) := by
    simp [results, EqualityLeafProjectionRuntimeEmpty.propagate, Value.referenceOf]
  exact ⟨actual, reads, next, receipt, finalNative, finalMerge, related, erased, related.length_eq.symm⟩

/-- A next finite class captures the full actual pass return, including final propagation. -/
theorem pass_then_class (records : List SourceEqualityClassOrder.Record) (nextRecord : SourceEqualityClassOrder.Record)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (nextCoherent : SourceEqualityClassOrder.Coherent nextRecord) (nextActive : EqualityNormalize.Nontrivial nextRecord.paths)
    (values : List (Value Symbol Guard)) (before : Checked width) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (domain : Domain values)
    (physical : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, Covered (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : NativeStored before.native) (merged : MergeStored memo) (ranges : Ranges records values before memo)
    (laterRanges : ∀ middle step current, Pass records values before memo middle step current → ClassRanges nextRecord middle step current)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    ∃ middle step current next stageMemos results after saved last final,
      Pass records values before memo middle step current ∧ Class nextRecord middle step current results after saved ∧
      Receipt formulas solver next records values before memo middle step current memos stageMemos ∧
      SourceCurrentAllocatedClassEdits.Receipt formulas solver last nextRecord middle step current results after saved stageMemos final ∧
      NativeStored after.native ∧ MergeStored saved ∧ All₂ NodeNarrow values results ∧
      Domain results ∧ MergedOrdinaryHeight.childrenHeight results ≤ MergedOrdinaryHeight.childrenHeight values ∧
      results.length = values.length := by
  obtain ⟨middle, step, current, next, stageMemos, firstActual, _, firstReceipt, firstNative, firstMerge, firstRelation⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryClassPass.finite formulas solver inventory ranges coherent active
      ready admitted available domain physical covered native merged memos valid
  obtain ⟨results, after, saved, last, final, lastActual, _, lastReceipt, lastNative, lastMerge, lastRelation⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryClass.finite formulas solver next nextRecord nextCoherent nextActive
      middle step current firstReceipt.ready firstReceipt.admitted firstReceipt.available (forest_domain firstRelation)
      firstReceipt.stored firstReceipt.covered firstNative firstMerge (laterRanges middle step current firstActual)
      stageMemos firstReceipt.globals.valid
  have related := forest_trans firstRelation lastRelation
  exact ⟨middle, step, current, next, stageMemos, results, after, saved, last, final,
    firstActual, lastActual, firstReceipt, lastReceipt, lastNative, lastMerge, related,
    forest_domain related, forest_height related, related.length_eq.symm⟩
end FiniteOrdinaryClassPassKernels
#print axioms FiniteOrdinaryClassPassKernels.nil_pass_erases
#check @FiniteOrdinaryClassPassKernels.nil_pass_erases
#print axioms FiniteOrdinaryClassPassKernels.pass_then_class
#check @FiniteOrdinaryClassPassKernels.pass_then_class
