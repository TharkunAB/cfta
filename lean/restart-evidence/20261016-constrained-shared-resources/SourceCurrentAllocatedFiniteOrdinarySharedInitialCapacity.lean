import MicroCFTA.SourceCurrentAllocatedFiniteOrdinarySharedForceResources
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTargetInitialCapacity
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinarySharedCapacity
import MicroCFTA.SourceCurrentAllocatedSharedTargetWorkerCompletion

/-!
# Shared capacity plans from initial force headroom

Original captured profiles derive the existing force capacity plan.
Stable literal force executions identify every completed raw force return.
Constructed resource receipts then derive capacity at each leaf query entry.
No reached capacity or completed force is an input to the plan producers.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinarySharedInitialCapacity
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedSharedTargetForce (Force)
open SourceEqualityClassTarget (operandPaths)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinarySharedCapacity (ForceCapacity LeafCapacity)
open MergedOrdinaryHeight (childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Stored" => SourceCurrentAllocatedFiniteOrdinarySharedProfiles.Stored
local notation "targetRows" => SourceCurrentAllocatedFiniteOrdinarySharedForceResources.targetRows
local notation "nodeBudget" => SourceCurrentAllocatedFiniteOrdinarySharedForceResources.nodeBudget
local notation "edgeBudget" => SourceCurrentAllocatedFiniteOrdinarySharedForceResources.edgeBudget
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- Two raw force returns have the same value and complete shared state. -/
theorem force_unique {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {path : EqualityNormalize.Path} {before after later : Shared width} {first second : Value Symbol Guard}
    (one : Force record values path before first after) (two : Force record values path before second later) :
    first = second ∧ after = later := by
  obtain ⟨p, h, m, s, n, firstDone⟩ := SourceCurrentAllocatedSharedTargetWorkerCompletion.force_complete one
  obtain ⟨q, i, k, t, o, secondDone⟩ := SourceCurrentAllocatedSharedTargetWorkerCompletion.force_complete two
  have firstStable := firstDone (max p q) (max h i) (max m k) (max s t) (max n o)
    (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have secondStable := secondDone (max p q) (max h i) (max m k) (max s t) (max n o)
    (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  exact SourceCurrentAllocatedSharedTargetWorker.Outcome.done.inj (firstStable.symm.trans secondStable)

/-- Initial slot-sensitive resources derive every reached force capacity check. -/
theorem force_capacity (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits : Nat) (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (base : InternedConstructorTemplates.State Symbol Guard) (before : Shared (bits + 2))
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (coherent : SourceEqualityClassOrder.Coherent record) (path : EqualityNormalize.Path) (member : path ∈ record.paths)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count) (pathsBound : ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound)
    (stored : Stored (targetRows record rows count depth bound) (max arity 1) bound before)
    (nodes : before.checked.native.machine.heap.nodes.next + nodeBudget record rows arity count depth bound before path ≤ 2 ^ bits)
    (edges : before.checked.native.machine.heap.edges.next + edgeBudget record rows arity count depth bound before path ≤ 2 ^ (bits + 2))
    (memos : Memos) (valid : Valid before.checked.native.machine.heap memos) :
    ForceCapacity bits record values path before := by
  intro absent
  have operandCount := SourceCurrentAllocatedFiniteOrdinarySharedProfileBounds.record_operand_paths_length
    record coherent path member
  exact SourceCurrentAllocatedFiniteOrdinaryTargetInitialCapacity.target_capacity formulas solver inventory bits
    values (operandPaths record.paths path) before.checked before.memo ready.checked ready.admitted
    (fun value member => ready.captured.available value (known value member))
    ready.stored stored.merge stored.native stored.output ready.covered memos valid
    rows arity count depth bound profile lengthBound
    (SourceCurrentAllocatedFiniteOrdinarySharedProfileBounds.operand_paths_depth record.paths path depth pathsBound)
    heightBound (by simpa only [SourceCurrentAllocatedFiniteOrdinarySharedForceResources.nodeBudget, absent, operandCount] using nodes)
    (by simpa only [SourceCurrentAllocatedFiniteOrdinarySharedForceResources.edgeBudget, absent, operandCount] using edges)

/-- Initial force headroom derives capacity after every actual earlier force in a leaf. -/
theorem leaf_capacity (formulas : SourceGuards.Formulas FullSyntax.Formula)
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
    (memos : Memos) (valid : Valid before.checked.native.machine.heap memos) (input : Value Symbol Guard) :
    LeafCapacity bits record values path input before := by
  have forcePlan := force_capacity formulas solver inventory bits record values base before ready known coherent path member
    rows arity count depth bound profile lengthBound pathsBound heightBound stored nodes edges memos valid
  obtain ⟨value, after, _next, _final, _requests, receipt, _stored, _profile, _height,
    _trace, _nodeCount, _edgeCount, capacity, _nodeSupply, _edgeSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinarySharedForceResources.complete formulas solver inventory bits record values
      base before ready known coherent active path member rows arity count depth bound profile lengthBound pathsBound
      heightBound stored nodes edges memos valid
  refine ⟨forcePlan, ?_⟩
  intro target middle actual
  have same := (force_unique actual receipt.actual).2
  exact same ▸ capacity

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinarySharedInitialCapacity
