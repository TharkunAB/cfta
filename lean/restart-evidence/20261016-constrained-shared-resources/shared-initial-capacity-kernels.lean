import MicroCFTA.SourceCurrentAllocatedFiniteOrdinarySharedInitialCapacity

namespace MicroCFTA.SharedInitialCapacityChecks
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedSharedTargetForce (Force ForceRanges)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinarySharedInitialCapacity
open MergedOrdinaryHeight (childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Stored" => SourceCurrentAllocatedFiniteOrdinarySharedProfiles.Stored
local notation "targetRows" => SourceCurrentAllocatedFiniteOrdinarySharedForceResources.targetRows
local notation "nodeBudget" => SourceCurrentAllocatedFiniteOrdinarySharedForceResources.nodeBudget
local notation "edgeBudget" => SourceCurrentAllocatedFiniteOrdinarySharedForceResources.edgeBudget
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- Every raw hit has the same value, checked state, slots, and Merge memo. -/
theorem raw_hit_identity (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (path : EqualityNormalize.Path) (before after : Shared width) (cached result : Value Symbol Guard)
    (present : before.targets path = some cached) (actual : Force record values path before result after) :
    result = cached ∧ after = before := force_unique actual (.hit present)

section OriginalResources
variable (formulas : SourceGuards.Formulas FullSyntax.Formula)
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
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos)
include formulas solver inventory bits record values base before ready known coherent active path member
  rows arity count depth bound profile lengthBound pathsBound heightBound stored nodes edges memos valid

/-- Original resources discharge both existing range predicates without an old numeric plan. -/
theorem initial_ranges (input : Value Symbol Guard) (available : Available before.checked.native.machine.heap input)
    (domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Node input) :
    ForceRanges record values path before ∧ SourceCurrentAllocatedSharedTargetLeaf.Ranges record values path input before := by
  have plan := leaf_capacity formulas solver inventory bits record values base before ready known coherent active
    path member rows arity count depth bound profile lengthBound pathsBound heightBound stored nodes edges memos valid input
  exact ⟨SourceCurrentAllocatedFiniteOrdinarySharedCapacity.force_ranges bits formulas solver inventory ready known
      (ChildrenShape.domain values profile) stored.domain plan.1 memos valid,
    SourceCurrentAllocatedFiniteOrdinarySharedCapacity.leaf_ranges bits formulas solver inventory ready known
      (ChildrenShape.domain values profile) stored.domain coherent active member available domain plan memos valid⟩

/-- Initial force resources construct a real leaf and its same complete stable worker return. -/
theorem literal_leaf (input : Value Symbol Guard) (available : Available before.checked.native.machine.heap input)
    (domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Node input) :
    ∃ result after next final,
      SourceCurrentAllocatedSharedTargetLeaf.Receipt formulas solver next record values base path input before result after memos final ∧
      SourceCurrentAllocatedSharedTargetWorkerCompletion.StableRun
        (fun p h m s n => SourceCurrentAllocatedSharedTargetWorker.leaf p h m s n record values path input before) result after ∧
      SourceCurrentAllocatedFiniteOrdinaryShared.Stored after ∧ SourceCurrentAllocatedFiniteOrdinaryRequired.NodeNarrow input result := by
  have plan := leaf_capacity formulas solver inventory bits record values base before ready known coherent active
    path member rows arity count depth bound profile lengthBound pathsBound heightBound stored nodes edges memos valid input
  obtain ⟨result, after, next, final, receipt, finalStored, narrowed⟩ :=
    SourceCurrentAllocatedFiniteOrdinarySharedCapacity.leaf_finite bits formulas solver inventory ready known
      (ChildrenShape.domain values profile) stored.domain coherent active member available domain plan memos valid
  exact ⟨result, after, next, final, receipt,
    SourceCurrentAllocatedSharedTargetWorkerCompletion.leaf_complete receipt.actual, finalStored, narrowed⟩
end OriginalResources

#print axioms raw_hit_identity
#check @raw_hit_identity
#print axioms initial_ranges
#check @initial_ranges
#print axioms literal_leaf
#check @literal_leaf
end MicroCFTA.SharedInitialCapacityChecks
