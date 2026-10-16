import MicroCFTA.SourceCurrentAllocatedFiniteOrdinarySharedLeafResources
import MicroCFTA.SourceCurrentAllocatedSharedTargetWorkerCompletion

set_option linter.all true
set_option pp.universes true

namespace MicroCFTA.SharedLeafResourceChecks
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace)
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
local notation "Receipt" => SourceCurrentAllocatedSharedTargetLeaf.Receipt
local notation "TargetRows" => SourceCurrentAllocatedFiniteOrdinarySharedForceResources.targetRows
local notation "LeafN" => SourceCurrentAllocatedFiniteOrdinarySharedLeafResources.nodeBudget
local notation "LeafE" => SourceCurrentAllocatedFiniteOrdinarySharedLeafResources.edgeBudget
local notation "QueryN" => SourceCurrentAllocatedFiniteOrdinarySharedLeafResources.queryBudget
local notation "ForceN" => SourceCurrentAllocatedFiniteOrdinarySharedForceResources.nodeBudget
local notation "ForceE" => SourceCurrentAllocatedFiniteOrdinarySharedForceResources.edgeBudget
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

private theorem force_present {record : Record} {values : List (Value Symbol Guard)} {path : Path}
    {before after : Shared width} {target : Value Symbol Guard}
    (actual : SourceCurrentAllocatedSharedTargetForce.Force record values path before target after) :
    after.targets path = some target := by
  cases actual with
  | hit present => exact present
  | miss absent actual => simp [SourceCurrentAllocatedSharedTargetState.store, put]

/-- The completed leaf retains the actual forced target in its class slot. -/
theorem leaf_present {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {record : Record} {values : List (Value Symbol Guard)} {base : InternedConstructorTemplates.State Symbol Guard}
    {path : Path} {input result : Value Symbol Guard} {before after : Shared width} {memos final : Memos}
    (receipt : Receipt formulas solver inventory record values base path input before result after memos final) :
    ∃ target, after.targets path = some target := by
  cases receipt.actual with
  | apply forced _ => exact ⟨_, force_present forced⟩

/-- Two constructed leaves retain their literal intermediate state and pay for the second query after a slot hit. -/
theorem two_leaves (formulas : SourceGuards.Formulas FullSyntax.Formula)
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
      LeafN record rows arity count depth bound inputRows inputArity inputBound before path +
      QueryN record rows arity count depth bound
        ((max (TargetRows record rows count depth bound) inputRows) * (max (TargetRows record rows count depth bound) inputRows))
        (max (max (max arity 1) inputArity) 1) inputBound ≤ 2 ^ bits)
    (edges : before.checked.native.machine.heap.edges.next +
      LeafE record rows arity count depth bound inputRows inputArity inputBound before path +
      QueryN record rows arity count depth bound
        ((max (TargetRows record rows count depth bound) inputRows) * (max (TargetRows record rows count depth bound) inputRows))
        (max (max (max arity 1) inputArity) 1) inputBound ≤ 2 ^ (bits + 2))
    (memos : Memos) (valid : Valid before.checked.native.machine.heap memos) :
    ∃ first middle firstInventory current result after next final firstRequests lastRequests,
      Receipt formulas solver firstInventory record values base path input before first middle memos current ∧
      Receipt formulas solver next record values base path first middle result after current final ∧
      ForceN record rows arity count depth bound middle path = 0 ∧
      ForceE record rows arity count depth bound middle path = 0 ∧
      Trace before.checked.native.machine.heap middle.checked.native.machine.heap firstRequests ∧
      Trace middle.checked.native.machine.heap after.checked.native.machine.heap lastRequests ∧
      Trace before.checked.native.machine.heap after.checked.native.machine.heap (firstRequests ++ lastRequests) ∧
      Stored (TargetRows record rows count depth bound) (max arity 1) bound after ∧
      height result ≤ height first ∧ height first ≤ height input ∧
      SourceCurrentAllocatedSharedTargetWorkerCompletion.StableRun
        (fun p h m s n => SourceCurrentAllocatedSharedTargetWorker.leaf p h m s n record values path first middle) result after ∧
      after.checked.native.machine.heap.nodes.next ≤ before.checked.native.machine.heap.nodes.next +
        LeafN record rows arity count depth bound inputRows inputArity inputBound before path +
        QueryN record rows arity count depth bound
          ((max (TargetRows record rows count depth bound) inputRows) * (max (TargetRows record rows count depth bound) inputRows))
          (max (max (max arity 1) inputArity) 1) inputBound ∧
      after.checked.native.machine.heap.edges.next ≤ before.checked.native.machine.heap.edges.next +
        LeafE record rows arity count depth bound inputRows inputArity inputBound before path +
        QueryN record rows arity count depth bound
          ((max (TargetRows record rows count depth bound) inputRows) * (max (TargetRows record rows count depth bound) inputRows))
          (max (max (max arity 1) inputArity) 1) inputBound := by
  obtain ⟨first, middle, firstInventory, current, firstRequests, firstReceipt, middleStored, firstProfile,
    firstNarrow, firstHeight, firstTrace, _firstNodes, _firstEdges, _middleCapacity, firstNodeSupply, firstEdgeSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinarySharedLeafResources.complete formulas solver inventory bits record values base before
      ready known coherent active path member rows arity count depth bound profile lengthBound pathsBound heightBound stored
      input inputRows inputArity inputBound available inputProfile inputHeight (by omega) (by omega) memos valid
  obtain ⟨target, present⟩ := leaf_present firstReceipt
  have noNodes : ForceN record rows arity count depth bound middle path = 0 := by
    simp only [SourceCurrentAllocatedFiniteOrdinarySharedForceResources.nodeBudget, present]
  have noEdges : ForceE record rows arity count depth bound middle path = 0 := by
    simp only [SourceCurrentAllocatedFiniteOrdinarySharedForceResources.edgeBudget, present]
  have nextNodes : middle.checked.native.machine.heap.nodes.next +
      LeafN record rows arity count depth bound
        ((max (TargetRows record rows count depth bound) inputRows) * (max (TargetRows record rows count depth bound) inputRows))
        (max (max (max arity 1) inputArity) 1) inputBound middle path ≤ 2 ^ bits := by
    simp only [SourceCurrentAllocatedFiniteOrdinarySharedLeafResources.nodeBudget, noNodes, Nat.zero_add]
    omega
  have nextEdges : middle.checked.native.machine.heap.edges.next +
      LeafE record rows arity count depth bound
        ((max (TargetRows record rows count depth bound) inputRows) * (max (TargetRows record rows count depth bound) inputRows))
        (max (max (max arity 1) inputArity) 1) inputBound middle path ≤ 2 ^ (bits + 2) := by
    simp only [SourceCurrentAllocatedFiniteOrdinarySharedLeafResources.edgeBudget, noEdges, Nat.zero_add]
    omega
  obtain ⟨result, after, next, final, lastRequests, lastReceipt, finalStored, _lastProfile,
    lastNarrow, _lastHeight, lastTrace, _lastNodes, _lastEdges, _finalCapacity, lastNodeSupply, lastEdgeSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinarySharedLeafResources.complete formulas solver firstInventory bits record values base middle
      firstReceipt.ready known coherent active path member rows arity count depth bound profile lengthBound pathsBound heightBound middleStored
      first _ _ inputBound firstReceipt.available firstProfile firstHeight nextNodes nextEdges current firstReceipt.globals.valid
  refine ⟨first, middle, firstInventory, current, result, after, next, final, firstRequests, lastRequests,
    firstReceipt, lastReceipt, noNodes, noEdges, firstTrace, lastTrace, firstTrace.trans lastTrace, finalStored,
    lastNarrow.2, firstNarrow.2, SourceCurrentAllocatedSharedTargetWorkerCompletion.leaf_complete lastReceipt.actual, ?_, ?_⟩
  · simp only [SourceCurrentAllocatedFiniteOrdinarySharedLeafResources.nodeBudget, noNodes, Nat.zero_add] at lastNodeSupply
    omega
  · simp only [SourceCurrentAllocatedFiniteOrdinarySharedLeafResources.edgeBudget, noEdges, Nat.zero_add] at lastEdgeSupply
    omega

#print axioms leaf_present
#check @leaf_present
#print axioms two_leaves
#check @two_leaves
end MicroCFTA.SharedLeafResourceChecks
