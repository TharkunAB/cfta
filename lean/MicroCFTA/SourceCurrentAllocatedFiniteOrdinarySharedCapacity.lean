import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTargetCapacity
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryShared

/-!
# Numeric query-entry plans for shared targets and leaves

A miss enters the target plan at the current shared state.
A leaf checks capacity after the actual earlier force returns.
Readiness and operand domains follow from initial invariants and that force.
The numeric plan supplies no current query completion or result property.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinarySharedCapacity
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinaryCapacity (Capacity)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
local notation "Stored" => SourceCurrentAllocatedFiniteOrdinaryShared.Stored
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Force" => SourceCurrentAllocatedSharedTargetForce.Force
local notation "ForceRanges" => SourceCurrentAllocatedSharedTargetForce.ForceRanges
local notation "LeafRanges" => SourceCurrentAllocatedSharedTargetLeaf.Ranges
local notation "ForceReceipt" => SourceCurrentAllocatedSharedTargetForce.Receipt
local notation "LeafReceipt" => SourceCurrentAllocatedSharedTargetLeaf.Receipt
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Only an absent slot enters its actual first-seeded target capacity plan. -/
def ForceCapacity (bits : Nat) (record : SourceEqualityClassOrder.Record)
    (values : List (Value Symbol Guard)) (path : EqualityNormalize.Path) (before : Shared (bits + 2)) : Prop :=
  before.targets path = none → SourceCurrentAllocatedFiniteOrdinaryTargetCapacity.TargetCapacity
    bits values (SourceEqualityClassTarget.operandPaths record.paths path) before.checked before.memo

/-- Current leaf capacity is required at the exact return of its earlier target force. -/
def LeafCapacity (bits : Nat) (record : SourceEqualityClassOrder.Record)
    (values : List (Value Symbol Guard)) (path : EqualityNormalize.Path)
    (_input : Value Symbol Guard) (before : Shared (bits + 2)) : Prop :=
  ForceCapacity bits record values path before ∧
    ∀ target middle, Force record values path before target middle → Capacity bits middle.checked

variable (bits : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
variable {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
variable {base : Heap} {path : EqualityNormalize.Path} {input : Value Symbol Guard}
variable {before : Shared (bits + 2)}

/-- Numeric target entries derive all existing force checks from the initial captured forest. -/
theorem force_ranges
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (domain : DChildren values) (stored : Stored before)
    (capacity : ForceCapacity bits record values path before)
    (memos : Memos) (valid : Valid before.checked.native.machine.heap memos) :
    ForceRanges record values path before := by
  intro absent
  exact SourceCurrentAllocatedFiniteOrdinaryTargetCapacity.target_ranges formulas solver inventory bits values
    (SourceEqualityClassTarget.operandPaths record.paths path) before.checked before.memo ready.checked ready.admitted
    (fun value member => ready.captured.available value (known value member)) domain
    ready.stored stored.merge stored.native ready.covered (capacity absent) memos valid

/-- Earlier force receipts derive the exact resident operands before the current leaf query. -/
theorem leaf_ranges
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (domain : DChildren values) (stored : Stored before)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (member : path ∈ record.paths) (available : Available before.checked.native.machine.heap input)
    (inputDomain : DNode input) (capacity : LeafCapacity bits record values path input before)
    (memos : Memos) (valid : Valid before.checked.native.machine.heap memos) :
    LeafRanges record values path input before := by
  have forcedRanges := force_ranges bits formulas solver inventory ready known domain stored capacity.1 memos valid
  refine ⟨forcedRanges, ?_⟩
  intro target middle actual
  obtain ⟨_, _, receipt, _retained, targetDomain⟩ := SourceCurrentAllocatedFiniteOrdinaryShared.force
    formulas solver inventory actual ready known domain stored coherent active member forcedRanges memos valid
  exact SourceCurrentAllocatedFiniteOrdinaryCapacity.node_words bits middle.checked receipt.ready.checked.good
    target input receipt.available (receipt.extension.available input available) targetDomain inputDomain
    (capacity.2 target middle actual)

/-- Initial facts and numeric target entries construct the actual force and its structural return. -/
theorem force_finite
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (domain : DChildren values) (stored : Stored before)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (member : path ∈ record.paths) (capacity : ForceCapacity bits record values path before)
    (memos : Memos) (valid : Valid before.checked.native.machine.heap memos) :
    ∃ value after next final, ForceReceipt formulas solver next record values base path before value after memos final ∧
      Stored after ∧ DNode value :=
  SourceCurrentAllocatedFiniteOrdinaryShared.force_finite formulas solver inventory ready known domain stored
    coherent active member (force_ranges bits formulas solver inventory ready known domain stored capacity memos valid) memos valid

/-- Numeric entries construct a finite leaf with its full receipt and original-input height bound. -/
theorem leaf_finite
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (domain : DChildren values) (stored : Stored before)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (member : path ∈ record.paths) (available : Available before.checked.native.machine.heap input)
    (inputDomain : DNode input) (capacity : LeafCapacity bits record values path input before)
    (memos : Memos) (valid : Valid before.checked.native.machine.heap memos) :
    ∃ result after next final, LeafReceipt formulas solver next record values base path input before result after memos final ∧
      Stored after ∧ SourceCurrentAllocatedFiniteOrdinaryRequired.NodeNarrow input result :=
  SourceCurrentAllocatedFiniteOrdinaryShared.leaf_finite formulas solver inventory ready known domain stored
    coherent active member available inputDomain
    (leaf_ranges bits formulas solver inventory ready known domain stored coherent active member available inputDomain capacity memos valid)
    memos valid

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinarySharedCapacity
