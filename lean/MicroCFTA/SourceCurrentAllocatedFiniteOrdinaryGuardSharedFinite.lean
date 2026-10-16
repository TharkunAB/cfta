import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardShared
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinarySharedLeafResources

/-!
# Constructed shared returns with hereditary guard bounds

Initial constructor headroom constructs the actual force or leaf receipt.
The guard producer verifies that same return before its certificate is stored.
Every earlier resource conclusion refers to the identical returned state.
No completed target, reached range plan, or future guard bound is an input.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardSharedFinite
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests)
open MergedOrdinaryHeight (height childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Path" => EqualityNormalize.Path
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Stored" => SourceCurrentAllocatedFiniteOrdinarySharedProfiles.Stored
local notation "Capacity" => SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity
local notation "Limits" => SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Limits
local notation "GNode" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node
local notation "GChildren" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Children
local notation "GuardStored" => SourceCurrentAllocatedFiniteOrdinaryGuardShared.Stored
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

namespace Force
open SourceCurrentAllocatedFiniteOrdinarySharedForceResources (targetRows nodeBudget edgeBudget)
local notation "Receipt" => SourceCurrentAllocatedSharedTargetForce.Receipt

/-- Initial force resources retain every old conclusion and derive the actual slot guard law. -/
theorem complete (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits : Nat) (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (base : InternedConstructorTemplates.State Symbol Guard) (before : Shared (bits + 2))
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (path : EqualityNormalize.Path) (member : path ∈ record.paths)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count) (pathsBound : ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound)
    (stored : Stored (targetRows record rows count depth bound) (max arity 1) bound before)
    (nodes : before.checked.native.machine.heap.nodes.next + nodeBudget record rows arity count depth bound before path ≤ 2 ^ bits)
    (edges : before.checked.native.machine.heap.edges.next + edgeBudget record rows arity count depth bound before path ≤ 2 ^ (bits + 2))
    (memos : Memos) (valid : Valid before.checked.native.machine.heap memos)
    (guards : GuardStored record values before) (captured : Limits) (guardProfile : GChildren captured values) :
    ∃ value after next final requests,
      (Receipt formulas solver next record values base path before value after memos final ∧
      Stored (targetRows record rows count depth bound) (max arity 1) bound after ∧
      NodeShape (targetRows record rows count depth bound) (max arity 1) value ∧ height value ≤ bound ∧
      Trace before.checked.native.machine.heap after.checked.native.machine.heap requests ∧
      nodeRequests requests ≤ nodeBudget record rows arity count depth bound before path ∧
      edgeRequests requests ≤ edgeBudget record rows arity count depth bound before path ∧ Capacity bits after.checked ∧
      after.checked.native.machine.heap.nodes.next ≤ before.checked.native.machine.heap.nodes.next + nodeBudget record rows arity count depth bound before path ∧
      after.checked.native.machine.heap.edges.next ≤ before.checked.native.machine.heap.edges.next + edgeBudget record rows arity count depth bound before path) ∧
      GuardStored record values after ∧
      GNode (SourceCurrentAllocatedFiniteOrdinaryGuardTarget.targetLimit captured
        (SourceEqualityClassTarget.operandPaths record.paths path)) value := by
  obtain ⟨value, after, next, final, requests, produced⟩ :=
    SourceCurrentAllocatedFiniteOrdinarySharedForceResources.complete formulas solver inventory bits record values base before
      ready known coherent active path member rows arity count depth bound profile lengthBound pathsBound heightBound
      stored nodes edges memos valid
  have finalGuards := SourceCurrentAllocatedFiniteOrdinaryGuardShared.force_receipt produced.1
    ready known guards captured guardProfile
  exact ⟨value, after, next, final, requests, produced, finalGuards⟩

end Force

namespace Leaf
open SourceCurrentAllocatedFiniteOrdinarySharedLeafResources (nodeBudget edgeBudget)
local notation "TargetRows" => SourceCurrentAllocatedFiniteOrdinarySharedForceResources.targetRows
local notation "Receipt" => SourceCurrentAllocatedSharedTargetLeaf.Receipt

/-- Initial total leaf resources retain every old conclusion and derive the same returned guard bound. -/
theorem complete (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits : Nat) (record : Record) (values : List (Value Symbol Guard))
    (base : InternedConstructorTemplates.State Symbol Guard) (before : Shared (bits + 2))
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (path : Path) (member : path ∈ record.paths)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count) (pathsBound : ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound)
    (stored : Stored (TargetRows record rows count depth bound) (max arity 1) bound before)
    (input : Value Symbol Guard) (inputRows inputArity inputBound : Nat)
    (available : Available before.checked.native.machine.heap input)
    (inputProfile : NodeShape inputRows inputArity input) (inputHeight : height input ≤ inputBound)
    (nodes : before.checked.native.machine.heap.nodes.next +
      nodeBudget record rows arity count depth bound inputRows inputArity inputBound before path ≤ 2 ^ bits)
    (edges : before.checked.native.machine.heap.edges.next +
      edgeBudget record rows arity count depth bound inputRows inputArity inputBound before path ≤ 2 ^ (bits + 2))
    (memos : Memos) (valid : Valid before.checked.native.machine.heap memos)
    (guards : GuardStored record values before) (captured : Limits) (guardProfile : GChildren captured values)
    (inputLimits : Limits) (inputGuardProfile : GNode inputLimits input) :
    ∃ result after next final requests,
      (Receipt formulas solver next record values base path input before result after memos final ∧
      Stored (TargetRows record rows count depth bound) (max arity 1) bound after ∧
      NodeShape ((max (TargetRows record rows count depth bound) inputRows) *
        (max (TargetRows record rows count depth bound) inputRows)) (max (max (max arity 1) inputArity) 1) result ∧
      SourceCurrentAllocatedFiniteOrdinaryRequired.NodeNarrow input result ∧ height result ≤ inputBound ∧
      Trace before.checked.native.machine.heap after.checked.native.machine.heap requests ∧
      nodeRequests requests ≤ nodeBudget record rows arity count depth bound inputRows inputArity inputBound before path ∧
      edgeRequests requests ≤ edgeBudget record rows arity count depth bound inputRows inputArity inputBound before path ∧
      Capacity bits after.checked ∧
      after.checked.native.machine.heap.nodes.next ≤ before.checked.native.machine.heap.nodes.next +
        nodeBudget record rows arity count depth bound inputRows inputArity inputBound before path ∧
      after.checked.native.machine.heap.edges.next ≤ before.checked.native.machine.heap.edges.next +
        edgeBudget record rows arity count depth bound inputRows inputArity inputBound before path) ∧
      GuardStored record values after ∧
      GNode (SourceCurrentAllocatedFiniteOrdinaryGuardIteration.leafLimit record captured inputLimits) result := by
  obtain ⟨result, after, next, final, requests, produced⟩ :=
    SourceCurrentAllocatedFiniteOrdinarySharedLeafResources.complete formulas solver inventory bits record values base before
      ready known coherent active path member rows arity count depth bound profile lengthBound pathsBound heightBound
      stored input inputRows inputArity inputBound available inputProfile inputHeight nodes edges memos valid
  have finalGuards := SourceCurrentAllocatedFiniteOrdinaryGuardShared.leaf_receipt produced.1
    ready known guards captured guardProfile inputLimits inputGuardProfile
  exact ⟨result, after, next, final, requests, produced, finalGuards⟩

end Leaf
end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardSharedFinite
