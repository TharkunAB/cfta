import MicroCFTA.SourceCurrentAllocatedFiniteOrdinarySharedProfileProducer
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardShared
import MicroCFTA.SourceCurrentAllocatedSharedTargetWorker

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option pp.fullNames true

namespace MicroCFTA.QuantitativePrefixChecks
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedSharedTargetState (State)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape ChildrenShape)
open MergedOrdinaryHeight (height childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "ForceReceipt" => SourceCurrentAllocatedSharedTargetForce.Receipt
local notation "LeafReceipt" => SourceCurrentAllocatedSharedTargetLeaf.Receipt
local notation "Stored" => SourceCurrentAllocatedFiniteOrdinarySharedProfiles.Stored
local notation "targetRows" => SourceCurrentAllocatedFiniteOrdinarySharedForceResources.targetRows
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory next last : Inventory}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {base : InternedConstructorTemplates.State Symbol Guard} {path : EqualityNormalize.Path}
    {before middle after : State width} {input target result : Value Symbol Guard} {memos current final : Memos}

-- The actual miss produces a target before store. Its warm replay uses no work.
-- The later leaf retains that slot while it changes the native result tables.
theorem miss_warm_leaf
    (first : ForceReceipt formulas solver next record values base path before target middle memos current)
    (absent : before.targets path = none)
    (second : LeafReceipt formulas solver last record values base path input middle result after current final)
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (coherent : SourceEqualityClassOrder.Coherent record) (member : path ∈ record.paths)
    (rows arity count depth bound : Nat)
    (stored : Stored (targetRows record rows count depth bound) (max arity 1) bound before)
    (profile : ChildrenShape rows arity values) (lengthBound : values.length ≤ count)
    (pathsBound : ∀ path ∈ record.paths, path.length ≤ depth) (heightBound : childrenHeight values ≤ bound)
    (inputRows inputArity inputBound : Nat) (inputProfile : NodeShape inputRows inputArity input)
    (inputHeight : height input ≤ inputBound) :
    (∃ checked saved,
      SourceCurrentAllocatedTargetGraph.Target values (SourceEqualityClassTarget.operandPaths record.paths path)
        before.checked before.memo target checked saved ∧
      middle = SourceCurrentAllocatedSharedTargetState.store before path target checked saved) ∧
    SourceCurrentAllocatedSharedTargetWorker.force 0 0 0 0 0 record values path middle = .done target middle ∧
    Stored (targetRows record rows count depth bound) (max arity 1) bound after ∧
    after.targets path = some target ∧
    NodeShape (targetRows record rows count depth bound) (max arity 1) target ∧
    height target ≤ bound ∧
    NodeShape (max (targetRows record rows count depth bound) inputRows *
      max (targetRows record rows count depth bound) inputRows) (max (max (max arity 1) inputArity) 1) result ∧
    SourceCurrentAllocatedFiniteOrdinaryRequired.NodeNarrow input result ∧ height result ≤ inputBound := by
  have miss : ∃ checked saved,
      SourceCurrentAllocatedTargetGraph.Target values (SourceEqualityClassTarget.operandPaths record.paths path)
        before.checked before.memo target checked saved ∧
      middle = SourceCurrentAllocatedSharedTargetState.store before path target checked saved := by
    cases first.actual with
    | hit present => rw [absent] at present; cases present
    | miss _ actual => exact ⟨_, _, actual, rfl⟩
  obtain ⟨middleStored, _, _⟩ := SourceCurrentAllocatedFiniteOrdinarySharedProfileProducer.force_receipt
    first ready known coherent member rows arity count depth bound stored profile lengthBound pathsBound heightBound
  obtain ⟨afterStored, outputProfile, narrow, outputHeight⟩ :=
    SourceCurrentAllocatedFiniteOrdinarySharedProfileProducer.leaf_receipt second first.ready known coherent member
      rows arity count depth bound middleStored profile lengthBound pathsBound heightBound
      inputRows inputArity inputBound inputProfile inputHeight
  have present := second.slots path target first.present
  have oldProfile := afterStored.slots path target present
  exact ⟨miss, SourceCurrentAllocatedSharedTargetWorker.force_hit 0 0 0 0 0 record values path middle target first.present,
    afterStored, present, oldProfile.1, oldProfile.2, outputProfile, narrow, outputHeight⟩

-- Independent guard and quantitative producers inspect the same actual leaf.
-- The result has both certificates without a resource headroom condition.
theorem same_leaf_guard_and_shape
    (receipt : LeafReceipt formulas solver next record values base path input before result after memos final)
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (coherent : SourceEqualityClassOrder.Coherent record) (member : path ∈ record.paths)
    (rows arity count depth bound : Nat)
    (stored : Stored (targetRows record rows count depth bound) (max arity 1) bound before)
    (profile : ChildrenShape rows arity values) (lengthBound : values.length ≤ count)
    (pathsBound : ∀ path ∈ record.paths, path.length ≤ depth) (heightBound : childrenHeight values ≤ bound)
    (inputRows inputArity inputBound : Nat) (inputProfile : NodeShape inputRows inputArity input)
    (inputHeight : height input ≤ inputBound)
    (guards : SourceCurrentAllocatedFiniteOrdinaryGuardShared.Stored record values before)
    (capturedGuards inputGuards : SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Limits)
    (capturedGuardProfile : SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Children capturedGuards values)
    (inputGuardProfile : SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node inputGuards input) :
    Stored (targetRows record rows count depth bound) (max arity 1) bound after ∧
    SourceCurrentAllocatedFiniteOrdinaryGuardShared.Stored record values after ∧
    NodeShape (max (targetRows record rows count depth bound) inputRows *
      max (targetRows record rows count depth bound) inputRows) (max (max (max arity 1) inputArity) 1) result ∧
    SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node
      (SourceCurrentAllocatedFiniteOrdinaryGuardIteration.leafLimit record capturedGuards inputGuards) result ∧
    SourceCurrentAllocatedFiniteOrdinaryRequired.NodeNarrow input result ∧ height result ≤ inputBound := by
  have quantitative := SourceCurrentAllocatedFiniteOrdinarySharedProfileProducer.leaf_receipt receipt ready known coherent member
    rows arity count depth bound stored profile lengthBound pathsBound heightBound inputRows inputArity inputBound inputProfile inputHeight
  have raw := SourceCurrentAllocatedFiniteOrdinaryGuardShared.leaf_receipt receipt ready known guards
    capturedGuards capturedGuardProfile inputGuards inputGuardProfile
  exact ⟨quantitative.1, raw.1, quantitative.2.1, raw.2, quantitative.2.2⟩

-- A stored warm target can force at all zero bounds from the same state.
-- Its three native/Merge laws remain separate from its fixed slot profile.
theorem warm_slot_all_zero
    (rows arity bound : Nat) (state : State width) (stored : Stored rows arity bound state)
    (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (path : EqualityNormalize.Path) (target : Value Symbol Guard) (present : state.targets path = some target) :
    SourceCurrentAllocatedSharedTargetWorker.force 0 0 0 0 0 record values path state = .done target state ∧
    SourceCurrentAllocatedFiniteOrdinaryStored.Stored state.checked.native ∧
    SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored state.checked.native ∧
    SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored state.memo ∧
    NodeShape rows arity target ∧ height target ≤ bound :=
  ⟨SourceCurrentAllocatedSharedTargetWorker.force_hit 0 0 0 0 0 record values path state target present,
    stored.native, stored.output, stored.merge, stored.slots path target present⟩

#print axioms miss_warm_leaf
#check @miss_warm_leaf
#print axioms same_leaf_guard_and_shape
#check @same_leaf_guard_and_shape
#print axioms warm_slot_all_zero
#check @warm_slot_all_zero
end MicroCFTA.QuantitativePrefixChecks
