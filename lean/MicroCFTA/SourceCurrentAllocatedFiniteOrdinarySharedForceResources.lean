import MicroCFTA.SourceCurrentAllocatedFiniteOrdinarySharedProfiles
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinarySharedProfileBounds
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTargetResources

/-!
# Initial constructor resources for shared target forcing

A hit returns its stored target and exact original state with zero Work.
A miss constructs the actual Target from the captured forest bounds.
The produced profile certifies the exact target stored in the class slot.
Neither branch takes reached ranges or a completed target as an input.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinarySharedForceResources
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedSharedTargetState (store)
open SourceCurrentAllocatedSharedTargetForce (Force Reads Retains)
open SourceEqualityClassTarget (operandPaths)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests)
open MergedOrdinaryHeight (height childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Receipt" => SourceCurrentAllocatedSharedTargetForce.Receipt
local notation "Stored" => SourceCurrentAllocatedFiniteOrdinarySharedProfiles.Stored
local notation "Capacity" => SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity
local notation "TargetN" => SourceCurrentAllocatedFiniteOrdinaryTargetResources.nodeBudget
local notation "TargetE" => SourceCurrentAllocatedFiniteOrdinaryTargetResources.edgeBudget
variable {width : Nat}

/-- The fixed captured forest and original class size bound every shared target. -/
def targetRows (record : SourceEqualityClassOrder.Record) (rows count depth bound : Nat) : Nat :=
  SourceCurrentAllocatedFiniteOrdinaryTargetResources.outputRows rows count depth bound (record.paths.length - 1)

/-- Only an initially absent slot needs the complete first-target node budget. -/
def nodeBudget (record : SourceEqualityClassOrder.Record) (rows arity count depth bound : Nat)
    (before : Shared width) (path : EqualityNormalize.Path) : Nat :=
  match before.targets path with
  | none => TargetN rows arity count depth bound (record.paths.length - 1)
  | some _ => 0

/-- A present slot makes no constructor requests of either kind. -/
def edgeBudget (record : SourceEqualityClassOrder.Record) (rows arity count depth bound : Nat)
    (before : Shared width) (path : EqualityNormalize.Path) : Nat :=
  match before.targets path with
  | none => TargetE rows arity count depth bound (record.paths.length - 1)
  | some _ => 0

private theorem miss_receipt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory next : Inventory} {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {base : InternedConstructorTemplates.State Symbol Guard} {path : EqualityNormalize.Path}
    {before : Shared width} {value : Value Symbol Guard} {checked : Checked width} {saved : Memo} {memos final : Memos}
    (ready : Ready formulas solver inventory record values base before) (member : path ∈ record.paths)
    (absent : before.targets path = none)
    (actual : SourceCurrentAllocatedTargetGraph.Target values (operandPaths record.paths path)
      before.checked before.memo value checked saved)
    (reads : SourceCurrentAllocatedTargetComplete.TargetReads formulas solver actual memos final)
    (receipt : SourceCurrentAllocatedTargetComplete.Receipt formulas solver next values (operandPaths record.paths path)
      before.checked before.memo value checked saved memos final)
    (included : SourceCurrentAllocatedClassTarget.SelectedIncludes formulas solver record values path value) :
    Receipt formulas solver next record values base path before value (store before path value checked saved) memos final := by
  refine ⟨.miss absent actual, .miss absent reads, ready.store path member actual reads receipt,
    receipt.effects, receipt.extension, receipt.available, receipt.closed, ?_, ?_, receipt.retained,
    receipt.globals, included⟩
  · simp only [store, put, ite_true]
  · intro other target present
    by_cases same : other = path
    · subst other
      rw [absent] at present
      cases present
    · simpa only [store, put, same, ite_false] using present

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial captured profiles and slot-sensitive headroom construct the complete force receipt. -/
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
    (memos : Memos) (valid : Valid before.checked.native.machine.heap memos) :
    ∃ value after next final requests,
      Receipt formulas solver next record values base path before value after memos final ∧
      Stored (targetRows record rows count depth bound) (max arity 1) bound after ∧
      NodeShape (targetRows record rows count depth bound) (max arity 1) value ∧ height value ≤ bound ∧
      Trace before.checked.native.machine.heap after.checked.native.machine.heap requests ∧
      nodeRequests requests ≤ nodeBudget record rows arity count depth bound before path ∧
      edgeRequests requests ≤ edgeBudget record rows arity count depth bound before path ∧ Capacity bits after.checked ∧
      after.checked.native.machine.heap.nodes.next ≤ before.checked.native.machine.heap.nodes.next + nodeBudget record rows arity count depth bound before path ∧
      after.checked.native.machine.heap.edges.next ≤ before.checked.native.machine.heap.edges.next + edgeBudget record rows arity count depth bound before path := by
  cases present : before.targets path with
  | some value =>
      have slot := ready.receipts path value present
      have available := slot.available
      have physicalReady : SourceCurrentConjunctionRowsAllocation.Ready (physical before.checked) :=
        ⟨ready.checked.semantic, ready.checked.costs, ready.checked.good.operations, ready.checked.good.fields⟩
      have effects := SourceCurrentConjunctionRowsAllocation.Effects.refl _ physicalReady
      have receipt : Receipt formulas solver inventory record values base path before value before memos memos :=
        ⟨.hit present, .hit present memos, ready, effects, .refl _, available.1, available.2, present,
          Retains.refl _, extends_refl _,
          ⟨effects.keeps, ready.checked.semantic, ready.checked.costs, valid, extends_refl _, rfl⟩,
          slot.included coherent active⟩
      have produced := stored.slots path value present
      simp only [nodeBudget, edgeBudget, present, Nat.add_zero] at nodes edges ⊢
      exact ⟨value, before, inventory, memos, [], receipt, stored, produced.1, produced.2, .refl _,
        Nat.zero_le _, Nat.zero_le _, ⟨nodes, edges⟩, Nat.le_refl _, Nat.le_refl _⟩
  | none =>
      have operandCount := SourceCurrentAllocatedFiniteOrdinarySharedProfileBounds.record_operand_paths_length record coherent path member
      have available : Values before.checked.native.machine.heap values :=
        fun value member => ready.captured.available value (known value member)
      have targetNodes : before.checked.native.machine.heap.nodes.next + TargetN rows arity count depth bound
          (operandPaths record.paths path).length ≤ 2 ^ bits := by
        simpa only [nodeBudget, present, operandCount] using nodes
      have targetEdges : before.checked.native.machine.heap.edges.next + TargetE rows arity count depth bound
          (operandPaths record.paths path).length ≤ 2 ^ (bits + 2) := by
        simpa only [edgeBudget, present, operandCount] using edges
      obtain ⟨value, checked, saved, next, final, requests, actual, _stable, reads, receipt,
        finalMerge, finalNative, finalOutput, produced, producedHeight, trace, nodeCount, edgeCount,
        capacity, nodeSupply, edgeSupply⟩ :=
        SourceCurrentAllocatedFiniteOrdinaryTargetResources.target_complete formulas solver inventory bits values
          (operandPaths record.paths path) before.checked before.memo ready.checked ready.admitted available
          ready.stored stored.merge stored.native stored.output ready.covered memos valid rows arity count depth bound
          profile lengthBound
          (SourceCurrentAllocatedFiniteOrdinarySharedProfileBounds.operand_paths_depth record.paths path depth pathsBound)
          heightBound targetNodes targetEdges
      have produced' : NodeShape (targetRows record rows count depth bound) (max arity 1) value := by
        simpa only [targetRows, operandCount] using produced
      have included := SourceCurrentAllocatedClassTarget.receipt_included receipt coherent active member
      have forced := miss_receipt ready member present actual reads receipt included
      have storedAfter := SourceCurrentAllocatedFiniteOrdinarySharedProfiles.store_stored before path value checked saved
        stored finalNative finalOutput finalMerge produced' producedHeight
      refine ⟨value, store before path value checked saved, next, final, requests, forced, storedAfter,
        produced', producedHeight, trace, ?_, ?_, capacity, ?_, ?_⟩
      · simpa only [nodeBudget, present, operandCount] using nodeCount
      · simpa only [edgeBudget, present, operandCount] using edgeCount
      · simpa only [store, nodeBudget, present, operandCount] using nodeSupply
      · simpa only [store, edgeBudget, present, operandCount] using edgeSupply

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinarySharedForceResources
