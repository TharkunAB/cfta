import MicroCFTA.SourceCurrentAllocatedFiniteOrdinarySharedForceResources
import MicroCFTA.SourceCurrentAllocatedSharedTargetWorkerCompletion

namespace MicroCFTA.SharedForceResourcesIndependentIntegration
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedSharedTargetState (initial store)
open SourceCurrentAllocatedSharedTargetForce (Retains)
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
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Receipt" => SourceCurrentAllocatedSharedTargetForce.Receipt
local notation "Stored" => SourceCurrentAllocatedFiniteOrdinarySharedProfiles.Stored
local notation "R" => SourceCurrentAllocatedFiniteOrdinarySharedForceResources.targetRows
local notation "N" => SourceCurrentAllocatedFiniteOrdinarySharedForceResources.nodeBudget
local notation "E" => SourceCurrentAllocatedFiniteOrdinarySharedForceResources.edgeBudget
local notation "Capacity" => SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

-- The first constructed receipt supplies the exact ready slot for every second force.
theorem first_force_then_exact_hit (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits : Nat) (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (base : InternedConstructorTemplates.State Symbol Guard) (before : Shared (bits + 2))
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (path : EqualityNormalize.Path) (member : path ∈ record.paths)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count) (pathsBound : ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound)
    (stored : Stored (R record rows count depth bound) (max arity 1) bound before)
    (nodes : before.checked.native.machine.heap.nodes.next + N record rows arity count depth bound before path ≤ 2 ^ bits)
    (edges : before.checked.native.machine.heap.edges.next + E record rows arity count depth bound before path ≤ 2 ^ (bits + 2))
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos) :
    ∃ value after next final requests,
      Receipt formulas solver next record values base path before value after memos final ∧
      Receipt formulas solver next record values base path after value after final final ∧
      Stored (R record rows count depth bound) (max arity 1) bound after ∧
      NodeShape (R record rows count depth bound) (max arity 1) value ∧ height value ≤ bound ∧
      SourceEqualityRequiredCache.Keeps base after.checked.native.machine.heap ∧
      final.query = memos.query ∧ Extends memos.unfolding final.unfolding ∧
      Trace before.checked.native.machine.heap after.checked.native.machine.heap requests ∧
      nodeRequests requests ≤ N record rows arity count depth bound before path ∧
      edgeRequests requests ≤ E record rows arity count depth bound before path ∧
      Capacity bits after.checked ∧
      (∀ p h m s n, SourceCurrentAllocatedSharedTargetWorker.force p h m s n record values path after = .done value after) ∧
      Trace after.checked.native.machine.heap after.checked.native.machine.heap [] ∧
      N record rows arity count depth bound after path = 0 ∧
      E record rows arity count depth bound after path = 0 := by
  obtain ⟨value, after, next, final, requests, first, finalStored, produced, producedHeight,
    trace, countedNodes, countedEdges, capacity, _nodes, _edges⟩ :=
    SourceCurrentAllocatedFiniteOrdinarySharedForceResources.complete formulas solver inventory bits
      record values base before ready known coherent active path member rows arity count depth bound
      profile lengthBound pathsBound heightBound stored nodes edges memos valid
  have physicalReady : SourceCurrentConjunctionRowsAllocation.Ready (physical after.checked) :=
    ⟨first.ready.checked.semantic, first.ready.checked.costs,
      first.ready.checked.good.operations, first.ready.checked.good.fields⟩
  have effects := SourceCurrentConjunctionRowsAllocation.Effects.refl _ physicalReady
  have second : Receipt formulas solver next record values base path after value after final final :=
    ⟨.hit first.present, .hit first.present final, first.ready, effects, .refl _,
      first.available, first.closed, first.present, Retains.refl _, extends_refl _,
      ⟨effects.keeps, first.ready.checked.semantic, first.ready.checked.costs,
        first.globals.valid, extends_refl _, rfl⟩, first.included⟩
  refine ⟨value, after, next, final, requests, first, second, finalStored, produced, producedHeight,
    first.ready.captured, first.globals.query, first.globals.retained, trace, countedNodes, countedEdges,
    capacity, ?_, .refl _, ?_, ?_⟩
  · intro p h m s n
    exact SourceCurrentAllocatedSharedTargetWorker.force_hit p h m s n record values path after value first.present
  · simp only [SourceCurrentAllocatedFiniteOrdinarySharedForceResources.nodeBudget, first.present]
  · simp only [SourceCurrentAllocatedFiniteOrdinarySharedForceResources.edgeBudget, first.present]

-- Empty slots derive both semantic capture and arbitrary uniform profile bounds.
theorem fresh_class_admission (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (base : InternedConstructorTemplates.State Symbol Guard) (checked : Checked width) (memo : Memo)
    (ready : SourceCurrentConjunctionClassScan.Ready checked) (admitted : At formulas solver inventory checked)
    (captured : SourceEqualityRequiredCache.Keeps base checked.native.machine.heap)
    (physical : SourceCurrentMemoMergeEffects.Stored checked.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : SourceCurrentAllocatedFiniteOrdinaryStored.Stored checked.native)
    (output : SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored checked.native)
    (merged : SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored memo)
    (rows arity bound : Nat) :
    Ready formulas solver inventory record values base (initial checked memo) ∧
      Stored rows arity bound (initial checked memo) ∧
      ∀ path, (initial checked memo).targets path = none := by
  exact ⟨SourceCurrentAllocatedSharedTargetState.initial_ready formulas solver inventory record values base
      checked memo ready admitted captured physical covered,
    SourceCurrentAllocatedFiniteOrdinarySharedProfiles.initial_stored checked memo native output merged,
    fun _ => rfl⟩

-- A fresh class constructs its own first miss and then reuses that exact return.
theorem fresh_miss_then_hit (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits : Nat) (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (base : InternedConstructorTemplates.State Symbol Guard) (checked : Checked (bits + 2)) (memo : Memo)
    (ready : SourceCurrentConjunctionClassScan.Ready checked) (admitted : At formulas solver inventory checked)
    (captured : SourceEqualityRequiredCache.Keeps base checked.native.machine.heap)
    (physical : SourceCurrentMemoMergeEffects.Stored checked.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : SourceCurrentAllocatedFiniteOrdinaryStored.Stored checked.native)
    (output : SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored checked.native)
    (merged : SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored memo) (known : Values base values)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (path : EqualityNormalize.Path) (member : path ∈ record.paths)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count) (pathsBound : ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound)
    (nodes : checked.native.machine.heap.nodes.next + SourceCurrentAllocatedFiniteOrdinaryTargetResources.nodeBudget
      rows arity count depth bound (record.paths.length - 1) ≤ 2 ^ bits)
    (edges : checked.native.machine.heap.edges.next + SourceCurrentAllocatedFiniteOrdinaryTargetResources.edgeBudget
      rows arity count depth bound (record.paths.length - 1) ≤ 2 ^ (bits + 2))
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid checked.native.machine.heap memos) :
    ∃ value after next final,
      Receipt formulas solver next record values base path (initial checked memo) value after memos final ∧
      Receipt formulas solver next record values base path after value after final final ∧
      Stored (R record rows count depth bound) (max arity 1) bound after ∧
      NodeShape (R record rows count depth bound) (max arity 1) value ∧ height value ≤ bound ∧
      (∃ actualChecked saved,
        after = store (initial checked memo) path value actualChecked saved ∧
        SourceCurrentAllocatedTargetGraph.Target values (SourceEqualityClassTarget.operandPaths record.paths path)
          checked memo value actualChecked saved) ∧
      (∀ p h m s n, SourceCurrentAllocatedSharedTargetWorker.force p h m s n record values path after = .done value after) ∧
      N record rows arity count depth bound after path = 0 ∧ E record rows arity count depth bound after path = 0 := by
  have initialFacts := fresh_class_admission formulas solver inventory record values base checked memo ready
    admitted captured physical covered native output merged (R record rows count depth bound) (max arity 1) bound
  obtain ⟨value, after, next, final, requests, first, second, finalStored, produced, producedHeight,
    _captured, _query, _unfolding, _trace, _nodes, _edges, _capacity, hit, _noWork, zeroNodes, zeroEdges⟩ :=
    first_force_then_exact_hit formulas solver inventory bits record values base (initial checked memo)
      initialFacts.1 known coherent active path member rows arity count depth bound profile lengthBound
      pathsBound heightBound initialFacts.2.1 (by exact nodes) (by exact edges) memos valid
  have actualMiss : ∃ actualChecked saved,
      after = store (initial checked memo) path value actualChecked saved ∧
      SourceCurrentAllocatedTargetGraph.Target values (SourceEqualityClassTarget.operandPaths record.paths path)
        checked memo value actualChecked saved := by
    cases first.actual with
    | hit present => cases present
    | miss absent target => exact ⟨_, _, rfl, target⟩
  exact ⟨value, after, next, final, first, second, finalStored, produced, producedHeight, actualMiss, hit, zeroNodes, zeroEdges⟩

set_option pp.explicit true
set_option pp.universes true
set_option pp.deepTerms true
set_option format.width 200
#print axioms first_force_then_exact_hit
#check @first_force_then_exact_hit
#print axioms fresh_class_admission
#check @fresh_class_admission
#print axioms fresh_miss_then_hit
#check @fresh_miss_then_hit
end MicroCFTA.SharedForceResourcesIndependentIntegration
