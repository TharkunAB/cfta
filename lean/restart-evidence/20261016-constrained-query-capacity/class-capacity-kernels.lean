import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryClassCapacity
import MicroCFTA.SourceCurrentAllocatedClassWorkerCompletion

namespace MicroCFTA.ClassCapacityKernels
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedFiniteOrdinaryClassCapacity
open SourceCurrentAllocatedClassEdits (Class ClassReads Receipt)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "MergeStored" => SourceCurrentAllocatedFiniteOrdinaryMergeCache.Stored
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

theorem serial_classes (bits : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (first second : SourceEqualityClassOrder.Record)
    (firstCoherent : SourceEqualityClassOrder.Coherent first) (firstActive : EqualityNormalize.Nontrivial first.paths)
    (secondCoherent : SourceEqualityClassOrder.Coherent second) (secondActive : EqualityNormalize.Nontrivial second.paths)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (memo : Memo)
    (ready : SourceCurrentConjunctionClassScan.Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Children values)
    (physical : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : NativeStored before.native) (merged : MergeStored memo)
    (firstCapacity : ClassCapacity bits first values before memo)
    (secondCapacity : ∀ middle current saved, Class first values before memo middle current saved →
      ClassCapacity bits second middle current saved)
    (memos : EndpointMemoGateTrace.Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    ∃ results after saved next final, ∃ actual : SourceCurrentAllocatedClassPass.Fold [second, first] values before memo results after saved,
      SourceCurrentAllocatedClassPass.FoldReads formulas solver actual memos final ∧
      At formulas solver next after ∧ NativeStored after.native ∧ MergeStored saved ∧ All₂ NodeNarrow values results ∧
      SourceCurrentAllocatedClassWorkerCompletion.StableRun
        (fun e p h m s n => SourceCurrentAllocatedClassWorker.fold e p h m s n [second, first] values before memo)
        results after saved := by
  obtain ⟨middle, current, saved, next, currentMemos, one, oneReads, firstReceipt, native, merged, related⟩ :=
    finite bits formulas solver inventory first firstCoherent firstActive values before memo ready admitted available domain
      physical covered native merged firstCapacity memos valid
  obtain ⟨results, after, saved', next', final, two, twoReads, secondReceipt, native', merged', related'⟩ :=
    finite bits formulas solver next second secondCoherent secondActive middle current saved
      firstReceipt.ready firstReceipt.admitted firstReceipt.available
      (SourceCurrentAllocatedFiniteOrdinaryNarrow.forest_domain related) firstReceipt.stored firstReceipt.covered
      native merged (secondCapacity middle current saved one) currentMemos firstReceipt.globals.valid
  let actual := SourceCurrentAllocatedClassPass.Fold.cons (.cons .nil one) two
  exact ⟨results, after, saved', next', final, actual, .cons (.cons .nil oneReads) twoReads,
    secondReceipt.admitted, native', merged', SourceCurrentAllocatedFiniteOrdinaryNarrow.forest_trans related related',
    SourceCurrentAllocatedClassWorkerCompletion.fold_complete actual⟩

#check @serial_classes
#print axioms serial_classes
end MicroCFTA.ClassCapacityKernels
