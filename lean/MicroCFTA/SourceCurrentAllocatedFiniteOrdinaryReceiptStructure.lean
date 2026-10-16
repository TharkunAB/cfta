import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTarget
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryShared

/-!
# Structural readback from current completed target receipts

The concrete receipts retain each reached physical query and its input
state. Their structural interpretation needs no uniform future range plan.
Force hits use the actual stored slot. Leaf queries retain the bound for
their second operand, which is the current edit input.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryReceiptStructure
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedTargetGraph SourceCurrentAllocatedTargetComplete
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "MergeStored" => SourceCurrentAllocatedFiniteOrdinaryMergeCache.Stored
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

private theorem operand_receipt
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {values : List (Value Symbol Guard)} {path : List Int}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard} {memos final : Memos}
    (receipt : SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory path values before memo result after saved memos final)
    (ready : Ready before) (available : Values before.native.machine.heap values) (domain : DChildren values)
    (physicalStored : PhysicalStored before.native.machine.heap memo) (mergeStored : MergeStored memo)
    (nativeStored : NativeStored before.native) : MergeStored saved ∧ NativeStored after.native ∧ DNode result := by
  obtain ⟨projected, middle, current, projection, merged⟩ := receipt.actual
  have projectedDomain := SourceCurrentAllocatedFiniteOrdinaryProjection.forest projection.graph ready.semantic available domain
  have middleNative : NativeStored middle.native := by
    rw [projection.advanced]
    exact SourceCurrentAllocatedFiniteOrdinaryStored.advance_stored _ _ nativeStored
  have checked := SourceCurrentAllocatedFiniteOrdinaryMerge.merge merged.actual projection.ready
    (physicalStored.grows projection.effects.keeps) mergeStored middleNative projection.available projectedDomain.2.2.2
  exact ⟨checked.2.2.1, checked.2.2.2.1, checked.2.2.2.2.2.1⟩

/-- Actual fold receipts derive structural certificates at their literal returns. -/
theorem fold
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {values : List (Value Symbol Guard)} {seed : List Int} {paths : List (List Int)}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard} {memos final : Memos}
    {actual : Fold values seed paths before memo result after saved} (reads : FoldReads formulas solver actual memos final) :
    Ready before → Values before.native.machine.heap values → DChildren values → PhysicalStored before.native.machine.heap memo →
      MergeStored memo → NativeStored before.native →
      Ready after ∧ Effects (physical before) (physical after) ∧ PhysicalStored after.native.machine.heap saved ∧
      MergeStored saved ∧ NativeStored after.native ∧ Available after.native.machine.heap result ∧ DNode result := by
  induction reads with
  | nil receipt =>
      intro ready available domain physicalStored mergeStored nativeStored
      have own := operand_receipt receipt ready available domain physicalStored mergeStored nativeStored
      exact ⟨receipt.ready, receipt.effects, receipt.stored, own.1, own.2.1, receipt.available, own.2.2⟩
  | cons receipt remaining query ih =>
      intro ready available domain physicalStored mergeStored nativeStored
      have head := operand_receipt receipt ready available domain physicalStored mergeStored nativeStored
      have tail := ih receipt.ready receipt.originals domain receipt.stored head.1 head.2.1
      cases query.actual with
      | run trace =>
          have checked := SourceCurrentAllocatedFiniteOrdinaryExecution.node_trace ⟨IntersectionEmptyDomain.emptyDomain, _, _⟩ _ _ _ _ trace
            tail.1.good tail.1.semantic tail.2.2.2.2.1 ⟨rfl, head.2.2, tail.2.2.2.2.2.2⟩
          exact ⟨query.ready, receipt.effects.trans (tail.2.1.trans query.effects),
            tail.2.2.1.grows query.effects.keeps, tail.2.2.2.1, checked.1, query.available, checked.2.1⟩

/-- Actual target reads preserve both structural caches and derive the result domain. -/
theorem target_reads
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {values : List (Value Symbol Guard)} {paths : List (List Int)}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard} {memos final : Memos}
    {actual : Target values paths before memo result after saved} (reads : TargetReads formulas solver actual memos final)
    (ready : Ready before) (available : Values before.native.machine.heap values) (domain : DChildren values)
    (physicalStored : PhysicalStored before.native.machine.heap memo) (mergeStored : MergeStored memo)
    (nativeStored : NativeStored before.native) : MergeStored saved ∧ NativeStored after.native ∧ DNode result := by
  cases reads with
  | nil => exact ⟨mergeStored, nativeStored, .empty⟩
  | cons reads =>
      have checked := fold reads ready available domain physicalStored mergeStored nativeStored
      exact ⟨checked.2.2.2.1, checked.2.2.2.2.1, checked.2.2.2.2.2.2⟩

local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "SharedReady" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "SharedStored" => SourceCurrentAllocatedFiniteOrdinaryShared.Stored

/-- A concrete force receipt derives structure without a future range premise. -/
theorem force_receipt
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory next : Inventory} {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {base receiptBase : InternedConstructorTemplates.State Symbol Guard} {path : EqualityNormalize.Path}
    {before after : Shared width} {value : Value Symbol Guard} {memos final : Memos}
    (receipt : SourceCurrentAllocatedSharedTargetForce.Receipt formulas solver next record values receiptBase path before value after memos final)
    (ready : SharedReady formulas solver inventory record values base before) (known : Values base values)
    (domain : DChildren values) (stored : SharedStored before) : SharedStored after ∧ DNode value := by
  cases receipt.reads with
  | hit present => exact ⟨stored, stored.slots path value present⟩
  | miss absent reads =>
      have checked := target_reads reads ready.checked
        (fun value member => ready.captured.available value (known value member)) domain ready.stored stored.merge stored.native
      exact ⟨SourceCurrentAllocatedFiniteOrdinaryShared.store_stored before path value _ _ stored
        checked.2.1 checked.1 checked.2.2, checked.2.2⟩

/-- The concrete leaf query derives domain and the height bound for its current input. -/
theorem leaf_receipt
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory next : Inventory} {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {base receiptBase : InternedConstructorTemplates.State Symbol Guard} {path : EqualityNormalize.Path}
    {before after : Shared width} {input result : Value Symbol Guard} {memos final : Memos}
    (receipt : SourceCurrentAllocatedSharedTargetLeaf.Receipt formulas solver next record values receiptBase path input before result after memos final)
    (ready : SharedReady formulas solver inventory record values base before) (known : Values base values)
    (domain : DChildren values) (stored : SharedStored before) (inputDomain : DNode input) :
    SharedStored after ∧ SourceCurrentAllocatedFiniteOrdinaryRequired.NodeNarrow input result := by
  cases receipt.reads with
  | apply first query =>
      have forced := force_receipt first ready known domain stored
      cases query.actual with
      | run trace =>
          have checked := SourceCurrentAllocatedFiniteOrdinaryExecution.node_trace
            ⟨IntersectionEmptyDomain.emptyDomain, _, _⟩ _ _ _ _ trace first.ready.checked.good
            first.ready.checked.semantic forced.1.native ⟨rfl, forced.2, inputDomain⟩
          exact ⟨SourceCurrentAllocatedFiniteOrdinaryShared.advance_stored _ _ forced.1 checked.1,
            checked.2.1, checked.2.2.2⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryReceiptStructure

