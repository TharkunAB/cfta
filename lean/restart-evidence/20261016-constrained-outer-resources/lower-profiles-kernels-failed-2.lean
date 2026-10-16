import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryLowerProfiles

namespace MicroCFTA.LowerProfilesIndependent
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
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "SharedReady" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "SharedStored" => SourceCurrentAllocatedFiniteOrdinaryShared.Stored
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- Two actual operands and their exact returned query construct the target read graph. -/
theorem two_operand_target
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {oneInventory twoInventory queryInventory : Inventory}
    {values : List (Value Symbol Guard)} {seed path : List Int}
    {before middle later after : Checked width} {memo current saved : Memo}
    {head tail result : Value Symbol Guard} {memos nextMemos final : Memos}
    (one : SourceCurrentAllocatedMergeOperand.Receipt formulas solver oneInventory path values
      before memo head middle current memos nextMemos)
    (two : SourceCurrentAllocatedMergeOperand.Receipt formulas solver twoInventory seed values
      middle current tail later saved nextMemos final)
    (query : SourceCurrentAllocatedTargetQuery.Receipt formulas solver queryInventory head tail later result after final)
    (ready : Ready before) (available : Values before.native.machine.heap values) (domain : DChildren values)
    (physicalStored : PhysicalStored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native) :
    ∃ actual : Target values [seed, path] before memo result after saved,
      TargetReads formulas solver actual memos final ∧ Profiles saved ∧
      NativeStored after.native ∧ OutputStored after.native ∧ DNode result := by
  let actual : Target values [seed, path] before memo result after saved :=
    .nonempty (.cons (of_receipt one) (.nil (of_receipt two)) query.actual)
  have reads : TargetReads formulas solver actual memos final :=
    .cons (.cons (operand := of_receipt one) (rest := .nil (of_receipt two))
      (step := query.actual) one (.nil (operand := of_receipt two) two) query)
  exact ⟨actual, reads, SourceCurrentAllocatedFiniteOrdinaryLowerProfiles.target_reads reads ready available domain physicalStored profiles native output⟩

/-- A literal warm slot hit constructs its own receipt and retains the exact full state. -/
theorem warm_force
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {base : InternedConstructorTemplates.State Symbol Guard} {path : EqualityNormalize.Path}
    {before : Shared width} {value : Value Symbol Guard}
    (ready : SharedReady formulas solver inventory record values base before) (known : Values base values)
    (domain : DChildren values) (stored : SharedStored before)
    (profiles : Profiles before.memo) (output : OutputStored before.checked.native)
    (present : before.targets path = some value)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos) :
    ∃ receipt : SourceCurrentAllocatedSharedTargetForce.Receipt formulas solver inventory record values base path
      before value before memos memos,
      SharedStored before ∧ Profiles before.memo ∧ OutputStored before.checked.native ∧ DNode value := by
  have slot := ready.receipts path value present
  have available := slot.available
  have physicalReady : SourceCurrentConjunctionRowsAllocation.Ready (physical before.checked) :=
    ⟨ready.checked.semantic, ready.checked.costs, ready.checked.good.operations, ready.checked.good.fields⟩
  have effects := SourceCurrentConjunctionRowsAllocation.Effects.refl _ physicalReady
  let receipt : SourceCurrentAllocatedSharedTargetForce.Receipt formulas solver inventory record values base path
      before value before memos memos :=
    ⟨.hit present, .hit present memos, ready, effects, .refl _, available.1, available.2,
      present, SourceCurrentAllocatedSharedTargetForce.Retains.refl _, Cache.extends_refl _,
      ⟨effects.keeps, ready.checked.semantic, ready.checked.costs, valid, Cache.extends_refl _, rfl⟩,
      slot.included coherent active⟩
  exact ⟨receipt, SourceCurrentAllocatedFiniteOrdinaryLowerProfiles.force_receipt receipt ready known domain stored profiles output⟩

/-- A second actual leaf uses the first returned stores and result domain without a new oracle. -/
theorem serial_leaf
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory firstInventory secondInventory : Inventory} {record : SourceEqualityClassOrder.Record}
    {values : List (Value Symbol Guard)} {base : InternedConstructorTemplates.State Symbol Guard}
    {firstPath secondPath : EqualityNormalize.Path} {before middle after : Shared width}
    {input first second : Value Symbol Guard} {memos current final : Memos}
    (one : SourceCurrentAllocatedSharedTargetLeaf.Receipt formulas solver firstInventory record values base firstPath
      input before first middle memos current)
    (two : SourceCurrentAllocatedSharedTargetLeaf.Receipt formulas solver secondInventory record values base secondPath
      first middle second after current final)
    (ready : SharedReady formulas solver inventory record values base before) (known : Values base values)
    (domain : DChildren values) (stored : SharedStored before) (inputDomain : DNode input)
    (profiles : Profiles before.memo) (output : OutputStored before.checked.native) :
    SharedStored after ∧ Profiles after.memo ∧ OutputStored after.checked.native ∧
      SourceCurrentAllocatedFiniteOrdinaryRequired.NodeNarrow input second := by
  obtain ⟨firstStored, firstProfiles, firstOutput, firstNarrow⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryLowerProfiles.leaf_receipt one ready known domain stored inputDomain profiles output
  obtain ⟨lastStored, lastProfiles, lastOutput, lastNarrow⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryLowerProfiles.leaf_receipt two one.ready known domain firstStored firstNarrow.1 firstProfiles firstOutput
  exact ⟨lastStored, lastProfiles, lastOutput,
    SourceCurrentAllocatedFiniteOrdinaryNarrow.node_trans firstNarrow lastNarrow⟩

end MicroCFTA.LowerProfilesIndependent

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 10000000
#print axioms MicroCFTA.LowerProfilesIndependent.two_operand_target
#check @MicroCFTA.LowerProfilesIndependent.two_operand_target
#print axioms MicroCFTA.LowerProfilesIndependent.warm_force
#check @MicroCFTA.LowerProfilesIndependent.warm_force
#print axioms MicroCFTA.LowerProfilesIndependent.serial_leaf
#check @MicroCFTA.LowerProfilesIndependent.serial_leaf
