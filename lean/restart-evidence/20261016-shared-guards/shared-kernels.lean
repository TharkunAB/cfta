import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardSharedFinite

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option pp.fullNames true

namespace MicroCFTA.SharedGuardChecks
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedSharedTargetState (State store)
open SourceCurrentAllocatedFiniteOrdinaryGuardShared
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Limits" => SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Limits
local notation "GNode" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node
local notation "GChildren" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Children
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Force" => SourceCurrentAllocatedSharedTargetForce.Force
local notation "ForceReceipt" => SourceCurrentAllocatedSharedTargetForce.Receipt
local notation "LeafReceipt" => SourceCurrentAllocatedSharedTargetLeaf.Receipt
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory next lastInventory : Inventory}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {base : InternedConstructorTemplates.State Symbol Guard} {path : EqualityNormalize.Path}
    {before after last : State width} {input value result : Value Symbol Guard} {memos current final : Memos}

/-- An actual first miss produces the universal captured law and the exact stored target graph. -/
theorem miss_universal
    (receipt : ForceReceipt formulas solver next record values base path before value after memos current)
    (absent : before.targets path = none)
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (guards : Stored record values before) (limits : Limits) (profile : GChildren limits values) :
    Stored record values after ∧ Certificate record values path value ∧
      ∃ checked saved, after = store before path value checked saved ∧
        SourceCurrentAllocatedTargetGraph.Target values (SourceEqualityClassTarget.operandPaths record.paths path)
          before.checked before.memo value checked saved := by
  have produced := force_receipt receipt ready known guards limits profile
  refine ⟨produced.1, produced.1.slots path value receipt.present, ?_⟩
  cases receipt.actual with
  | hit present => rw [absent] at present; cases present
  | miss _ actual => exact ⟨_, _, rfl, actual⟩

/-- Every raw force after the actual first return reuses the full state and same slot value. -/
theorem warm_identity
    (receipt : ForceReceipt formulas solver next record values base path before value after memos current)
    {target : Value Symbol Guard} {middle : State width} (warm : Force record values path after target middle) :
    target = value ∧ middle = after := by
  cases warm with
  | hit present => exact ⟨Option.some.inj (present.symm.trans receipt.present), rfl⟩
  | miss absent _ => rw [receipt.present] at absent; cases absent

/-- A first miss then a warm leaf retains that captured slot and all guard tables. -/
theorem miss_warm_leaf
    (first : ForceReceipt formulas solver next record values base path before value after memos current)
    (absent : before.targets path = none)
    (second : LeafReceipt formulas solver lastInventory record values base path input after result last current final)
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (guards : Stored record values before) (captured : Limits) (profile : GChildren captured values)
    (inputLimits : Limits) (inputProfile : GNode inputLimits input) :
    Stored record values last ∧
      GNode (SourceCurrentAllocatedFiniteOrdinaryGuardIteration.leafLimit record captured inputLimits) result ∧
      last.targets path = some value ∧ Certificate record values path value ∧
      ∀ target middle, Force record values path after target middle → target = value ∧ middle = after := by
  have firstGuards := miss_universal first absent ready known guards captured profile
  have secondGuards := leaf_receipt second first.ready known firstGuards.1 captured profile inputLimits inputProfile
  exact ⟨secondGuards.1, secondGuards.2, second.slots path value first.present, firstGuards.2.1,
    fun _ _ warm => warm_identity first warm⟩

/-- Immutable original positions share one class envelope regardless of earlier edited outputs. -/
theorem same_original_class
    (receipt : LeafReceipt formulas solver next record values base path input before result after memos final)
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (guards : Stored record values before) (limits : Limits)
    (captured : GChildren limits values) (original : GNode limits input) :
    Stored record values after ∧
      GNode (SourceCurrentAllocatedFiniteOrdinaryGuardTarget.foldLimit limits (record.paths.length + 1)) result := by
  have produced := leaf_receipt receipt ready known guards limits captured limits original
  exact ⟨produced.1, SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node.mono result produced.2
    (SourceCurrentAllocatedFiniteOrdinaryGuardIteration.leafLimit_same record limits)⟩

end MicroCFTA.SharedGuardChecks

#print axioms MicroCFTA.SharedGuardChecks.miss_universal
#check @MicroCFTA.SharedGuardChecks.miss_universal
#print axioms MicroCFTA.SharedGuardChecks.warm_identity
#check @MicroCFTA.SharedGuardChecks.warm_identity
#print axioms MicroCFTA.SharedGuardChecks.miss_warm_leaf
#check @MicroCFTA.SharedGuardChecks.miss_warm_leaf
#print axioms MicroCFTA.SharedGuardChecks.same_original_class
#check @MicroCFTA.SharedGuardChecks.same_original_class
