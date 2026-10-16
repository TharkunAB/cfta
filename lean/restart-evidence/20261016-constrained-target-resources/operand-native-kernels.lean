import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOperandNativeStores
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOperandResources

namespace OperandNativeKernels
open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "Idle" => SourceRecursiveIntersectionNative.Idle
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentAllocatedMergeGraph.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Receipt" => SourceCurrentAllocatedMergeOperand.Receipt
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}

/-- Two actual operands retain the original native tables and all three certificate families. -/
theorem serial_operands {firstPath secondPath : List Int} {values : List (Value Symbol Guard)}
    {before middle after : Checked width} {memo current saved : Memo} {firstValue lastValue : Value Symbol Guard}
    {memos currentGlobals final : Memos}
    (first : Receipt formulas solver inventory firstPath values before memo firstValue middle current memos currentGlobals)
    (last : Receipt formulas solver inventory secondPath values middle current lastValue after saved currentGlobals final)
    (physical : PhysicalStored before.native.machine.heap memo) (merged : Profiles memo)
    (stored : NativeStored before.native) (profiles : OutputStored before.native) (idle : Idle before.native) :
    Profiles saved ∧ NativeStored after.native ∧ OutputStored after.native ∧ Idle after.native ∧
      after.native.nodes = before.native.nodes ∧ after.native.edges = before.native.edges ∧
      after.native.machine.domains = before.native.machine.domains ∧ final.query = memos.query := by
  obtain ⟨firstProfiles, firstNative, firstOutput, firstIdle⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOperandNativeStores.receipt first physical merged stored profiles idle
  obtain ⟨lastProfiles, lastNative, lastOutput, lastIdle⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOperandNativeStores.receipt last first.stored firstProfiles firstNative firstOutput firstIdle
  exact ⟨lastProfiles, lastNative, lastOutput, lastIdle, last.nodes.trans first.nodes,
    last.edges.trans first.edges, last.domains.trans first.domains, last.query.trans first.query⟩

/-- Initial forest bounds construct the same resource receipt and retain the warm native certificates. -/
theorem constructed_operand (path : List Int) (values : List (Value Symbol Guard)) (before : Checked width) (memo : Memo)
    (ready : SourceCurrentConjunctionClassScan.Ready before)
    (admitted : SourceCurrentAllocatedNativeInventoryState.At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (physical : PhysicalStored before.native.machine.heap memo)
    (merged : Profiles memo) (stored : NativeStored before.native) (profiles : OutputStored before.native)
    (idle : Idle before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat)
    (profile : SourceCurrentAllocatedFiniteOrdinaryNativeProfile.ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count) (pathBound : path.length ≤ depth)
    (heightBound : MergedOrdinaryHeight.childrenHeight values ≤ bound) :
    ∃ output after saved final requests,
      Receipt formulas solver inventory path values before memo output after saved memos final ∧
      Profiles saved ∧ NativeStored after.native ∧ OutputStored after.native ∧ Idle after.native ∧
      SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace.Trace before.native.machine.heap after.native.machine.heap requests ∧
      SourceCurrentAllocatedFiniteOrdinaryReservations.nodeRequests requests ≤
        SourceCurrentAllocatedFiniteOrdinaryOperandResources.nodeBudget rows arity count depth bound ∧
      SourceCurrentAllocatedFiniteOrdinaryReservations.edgeRequests requests ≤
        SourceCurrentAllocatedFiniteOrdinaryOperandResources.edgeBudget rows arity count depth bound := by
  obtain ⟨output, after, saved, final, requests, receipt, finalProfiles, _profile, _height,
      trace, nodes, edges, _nodeSupply, _edgeSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOperandResources.complete formulas solver inventory path values before memo
      ready admitted available physical merged covered memos valid rows arity count depth bound
      profile lengthBound pathBound heightBound
  obtain ⟨finalNative, finalOutput, finalIdle⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOperandNativeStores.native receipt stored profiles idle
  exact ⟨output, after, saved, final, requests, receipt, finalProfiles, finalNative, finalOutput, finalIdle,
    trace, nodes, edges⟩

end OperandNativeKernels

#check @OperandNativeKernels.serial_operands
#print axioms OperandNativeKernels.serial_operands
#check @OperandNativeKernels.constructed_operand
#print axioms OperandNativeKernels.constructed_operand
