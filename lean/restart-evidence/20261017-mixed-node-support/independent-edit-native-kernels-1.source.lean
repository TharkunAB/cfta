import MicroCFTA.SourceCurrentHereditaryTargetQuery

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.IndependentEditNativeKernels
open InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityAnnotationLanguage (Annotated)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "Stored" => SourceCurrentHereditaryNativeUniversalStore.Stored Plain
local notation "Receipt" => SourceCurrentAllocatedTargetQuery.Receipt
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- Two supplied actual receipts retain the first output as the next annotated operand at its new entry heap. -/
theorem serial_receipts
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (firstInventory secondInventory : SourceCurrentAllocatedNativeInventoryState.Inventory)
    (memos : EndpointMemoGateTrace.Memos) (left right first second : Node) (before middle after : Checked width)
    (ready : SourceCurrentConjunctionClassScan.Ready before)
    (leftAvailable : Available before.native.machine.heap left) (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (stored : Stored before) (leftAnnotated : Annotated Plain left) (rightAnnotated : Annotated Plain right)
    (one : Receipt formulas solver firstInventory left right before first middle memos)
    (two : Receipt formulas solver secondInventory first right middle second after memos) :
    Receipt formulas solver firstInventory left right before first middle memos ∧
      Receipt formulas solver secondInventory first right middle second after memos ∧
      SourceCurrentHereditaryNativeCache.Stored Plain middle.native.machine.heap middle.native ∧
      Stored after ∧ Annotated Plain first ∧ Annotated Plain second := by
  have firstLaw := SourceCurrentHereditaryTargetQuery.receipt formulas solver firstInventory memos one ready
    leftAvailable rightAvailable leftClosed rightClosed stored leftAnnotated rightAnnotated
  have nextRight := one.effects.keeps.available right rightAvailable
  have secondLaw := SourceCurrentHereditaryTargetQuery.receipt formulas solver secondInventory memos two one.ready
    one.available nextRight one.closed rightClosed firstLaw.2.1 firstLaw.2.2 rightAnnotated
  exact ⟨firstLaw.1, secondLaw.1, firstLaw.2.1.native middle.native.machine.heap,
    secondLaw.2.1, firstLaw.2.2, secondLaw.2.2⟩

end MicroCFTA.IndependentEditNativeKernels

#print axioms MicroCFTA.IndependentEditNativeKernels.serial_receipts
#check @MicroCFTA.IndependentEditNativeKernels.serial_receipts
