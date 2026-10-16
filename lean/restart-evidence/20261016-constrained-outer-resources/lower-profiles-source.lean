import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOperandNativeStores
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryReceiptStructure
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputExecution

/-!
# Lower profile stores through the same actual target reads

Every operand retains its actual projection and Merge winner.
Each checked query interprets its own physical trace at empty seen.
Force and Leaf use their literal receipts and causal slot domains.
No range, capacity, future profile, or completed callback law is an input.
These endpoints verify supplied reads. They do not construct executions.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryLowerProfiles
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedTargetGraph SourceCurrentAllocatedTargetComplete
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- The same operand receipt retains both lower profile stores and its result domain. -/
theorem operand_receipt
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {values : List (Value Symbol Guard)} {path : List Int}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard} {memos final : Memos}
    (receipt : SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory path values before memo result after saved memos final)
    (ready : Ready before) (available : Values before.native.machine.heap values) (domain : DChildren values)
    (physicalStored : PhysicalStored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native) :
    Profiles saved ∧ NativeStored after.native ∧ OutputStored after.native ∧ DNode result := by
  have retained := SourceCurrentAllocatedFiniteOrdinaryOperandNativeStores.receipt receipt
    physicalStored profiles native output ready.idle
  obtain ⟨projected, middle, current, projection, merged⟩ := receipt.actual
  have projectedDomain := SourceCurrentAllocatedFiniteOrdinaryProjection.forest projection.graph ready.semantic available domain
  have middleNative : NativeStored middle.native := by
    rw [projection.advanced]
    exact SourceCurrentAllocatedFiniteOrdinaryStored.advance_stored _ _ native
  have checked := SourceCurrentAllocatedFiniteOrdinaryMerge.merge merged.actual projection.ready
    (physicalStored.grows projection.effects.keeps) profiles.domain middleNative projection.available projectedDomain.2.2.2
  exact ⟨retained.1, retained.2.1, retained.2.2.1, checked.2.2.2.2.2.1⟩

private theorem query_output
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {left right result : Value Symbol Guard} {before after : Checked width} {memos : Memos}
    (receipt : SourceCurrentAllocatedTargetQuery.Receipt formulas solver inventory left right before result after memos)
    (ready : Ready before) (leftDomain : DNode left) (rightDomain : DNode right)
    (output : OutputStored before.native) : OutputStored after.native := by
  cases receipt.actual with
  | run trace =>
      let request : SourceRecursiveIntersectionThunks.NodeRequest Symbol Guard :=
        ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
      have checked := SourceCurrentAllocatedFiniteOrdinaryOutputExecution.verified _ _ _ _ _
        (fun _ result => SourceCurrentAllocatedFiniteOrdinaryOutputStored.NodeCertificate request result)
        trace ready.good ready.semantic (fun _ => trivial) output
        (SourceCurrentAllocatedFiniteOrdinaryOutputCode.request_node request _ ⟨rfl, leftDomain, rightDomain⟩)
      exact checked.1

/-- Ordered fold reads retain their exact returned stores, physical facts, and finite domain. -/
theorem fold
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {values : List (Value Symbol Guard)} {seed : List Int} {paths : List (List Int)}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard} {memos final : Memos}
    {actual : Fold values seed paths before memo result after saved} (reads : FoldReads formulas solver actual memos final) :
    Ready before → Values before.native.machine.heap values → DChildren values → PhysicalStored before.native.machine.heap memo →
      Profiles memo → NativeStored before.native → OutputStored before.native →
      Ready after ∧ Effects (physical before) (physical after) ∧ PhysicalStored after.native.machine.heap saved ∧
      Profiles saved ∧ NativeStored after.native ∧ OutputStored after.native ∧
      Available after.native.machine.heap result ∧ DNode result := by
  induction reads with
  | nil receipt =>
      intro ready available domain physicalStored profiles native output
      have own := operand_receipt receipt ready available domain physicalStored profiles native output
      exact ⟨receipt.ready, receipt.effects, receipt.stored, own.1, own.2.1, own.2.2.1, receipt.available, own.2.2.2⟩
  | cons receipt remaining query ih =>
      intro ready available domain physicalStored profiles native output
      have head := operand_receipt receipt ready available domain physicalStored profiles native output
      have tail := ih receipt.ready receipt.originals domain receipt.stored head.1 head.2.1 head.2.2.1
      have outputAfter := query_output query tail.1 head.2.2.2 tail.2.2.2.2.2.2.2 tail.2.2.2.2.2.1
      cases query.actual with
      | run trace =>
          have checked := SourceCurrentAllocatedFiniteOrdinaryExecution.node_trace
            ⟨IntersectionEmptyDomain.emptyDomain, _, _⟩ _ _ _ _ trace tail.1.good tail.1.semantic
            tail.2.2.2.2.1 ⟨rfl, head.2.2.2, tail.2.2.2.2.2.2.2⟩
          exact ⟨query.ready, receipt.effects.trans (tail.2.1.trans query.effects),
            tail.2.2.1.grows query.effects.keeps, tail.2.2.2.1, checked.1, outputAfter, query.available, checked.2.1⟩

/-- Supplied target reads retain strong native and Merge profiles without a capacity plan. -/
theorem target_reads
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {values : List (Value Symbol Guard)} {paths : List (List Int)}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard} {memos final : Memos}
    {actual : Target values paths before memo result after saved} (reads : TargetReads formulas solver actual memos final)
    (ready : Ready before) (available : Values before.native.machine.heap values) (domain : DChildren values)
    (physicalStored : PhysicalStored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native) :
    Profiles saved ∧ NativeStored after.native ∧ OutputStored after.native ∧ DNode result := by
  cases reads with
  | nil => exact ⟨profiles, native, output, .empty⟩
  | cons reads =>
      have checked := fold reads ready available domain physicalStored profiles native output
      exact ⟨checked.2.2.2.1, checked.2.2.2.2.1, checked.2.2.2.2.2.1, checked.2.2.2.2.2.2.2⟩

local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "SharedReady" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "SharedStored" => SourceCurrentAllocatedFiniteOrdinaryShared.Stored

/-- The concrete Force receipt retains strong stores through its actual hit or Target miss. -/
theorem force_receipt
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory next : Inventory} {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {base receiptBase : InternedConstructorTemplates.State Symbol Guard} {path : EqualityNormalize.Path}
    {before after : Shared width} {value : Value Symbol Guard} {memos final : Memos}
    (receipt : SourceCurrentAllocatedSharedTargetForce.Receipt formulas solver next record values receiptBase path before value after memos final)
    (ready : SharedReady formulas solver inventory record values base before) (known : Values base values)
    (domain : DChildren values) (stored : SharedStored before)
    (profiles : Profiles before.memo) (output : OutputStored before.checked.native) :
    SharedStored after ∧ Profiles after.memo ∧ OutputStored after.checked.native ∧ DNode value := by
  cases receipt.reads with
  | hit present => exact ⟨stored, profiles, output, stored.slots path value present⟩
  | miss absent reads =>
      obtain ⟨finalProfiles, finalNative, finalOutput, resultDomain⟩ := target_reads reads ready.checked
        (fun value member => ready.captured.available value (known value member)) domain ready.stored profiles stored.native output
      exact ⟨SourceCurrentAllocatedFiniteOrdinaryShared.store_stored before path value _ _ stored
        finalNative finalProfiles.domain resultDomain, finalProfiles, finalOutput, resultDomain⟩

/-- The concrete Leaf receipt retains both stores and narrows its exact current input. -/
theorem leaf_receipt
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory next : Inventory} {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {base receiptBase : InternedConstructorTemplates.State Symbol Guard} {path : EqualityNormalize.Path}
    {before after : Shared width} {input result : Value Symbol Guard} {memos final : Memos}
    (receipt : SourceCurrentAllocatedSharedTargetLeaf.Receipt formulas solver next record values receiptBase path input before result after memos final)
    (ready : SharedReady formulas solver inventory record values base before) (known : Values base values)
    (domain : DChildren values) (stored : SharedStored before) (inputDomain : DNode input)
    (profiles : Profiles before.memo) (output : OutputStored before.checked.native) :
    SharedStored after ∧ Profiles after.memo ∧ OutputStored after.checked.native ∧
      SourceCurrentAllocatedFiniteOrdinaryRequired.NodeNarrow input result := by
  cases receipt.reads with
  | apply first query =>
      have forced := force_receipt first ready known domain stored profiles output
      have outputAfter := query_output query first.ready.checked forced.2.2.2 inputDomain forced.2.2.1
      cases query.actual with
      | run trace =>
          have checked := SourceCurrentAllocatedFiniteOrdinaryExecution.node_trace
            ⟨IntersectionEmptyDomain.emptyDomain, _, _⟩ _ _ _ _ trace first.ready.checked.good
            first.ready.checked.semantic forced.1.native ⟨rfl, forced.2.2.2, inputDomain⟩
          exact ⟨SourceCurrentAllocatedFiniteOrdinaryShared.advance_stored _ _ forced.1 checked.1,
            forced.2.1, outputAfter, checked.2.1, checked.2.2.2⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryLowerProfiles
