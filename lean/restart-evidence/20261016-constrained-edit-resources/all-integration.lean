import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEditCallbackCounts
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEditResources
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryClassResources
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryPassResources

set_option linter.all true
set_option pp.universes true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option format.width 180


namespace MicroCFTA.EditBudgetNumberChecks
open Cache InternedBinderProtocol InternedConstructorTemplates
open SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape ChildrenShape RowsShape EdgeShape)
open MergedOrdinaryHeight (height childrenHeight edgesHeight edgeHeight)

/-- Repeated literal children and rows contribute separately even when all records share identities. -/
theorem repeated_literal_cost (nodes edgeCost : Nat) (nodeEntry : Interned NodeKey)
    (edgeEntry : Interned (EdgeKey Symbol Guard)) :
    let row : EdgeValue Symbol Guard := .mk edgeEntry [.empty, .empty]
    let value : Value Symbol Guard := .node nodeEntry [row, row] 0 []
    nodeNodes nodes value = 5 * nodes + 1 ∧ nodeEdges edgeCost value = 5 * edgeCost + 2 := by
  constructor <;> rfl

/-- Smaller current input limits in any slot state fit the original edit's fixed leaf budget. -/
theorem descendant_leaf_cost (record : SourceEqualityClassOrder.Record) (rows arity count depth bound : Nat)
    (before : SourceCurrentAllocatedSharedTargetState.State width) (path : EqualityNormalize.Path)
    {localRows wholeRows localArity wholeArity localHeight wholeHeight : Nat}
    (rowBound : localRows ≤ wholeRows) (arityBound : localArity ≤ wholeArity) (heightBound : localHeight ≤ wholeHeight) :
    SourceCurrentAllocatedFiniteOrdinarySharedLeafResources.nodeBudget record rows arity count depth bound
      localRows localArity localHeight before path ≤ leafNodes record rows arity count depth bound wholeRows wholeArity wholeHeight ∧
    SourceCurrentAllocatedFiniteOrdinarySharedLeafResources.edgeBudget record rows arity count depth bound
      localRows localArity localHeight before path ≤ leafEdges record rows arity count depth bound wholeRows wholeArity wholeHeight :=
  ⟨Nat.le_trans (leaf_nodes_bound record rows arity count depth bound localRows localArity localHeight before path)
      (leafNodes_mono record rows arity count depth bound rowBound arityBound heightBound),
    Nat.le_trans (leaf_edges_bound record rows arity count depth bound localRows localArity localHeight before path)
      (leafEdges_mono record rows arity count depth bound rowBound arityBound heightBound)⟩

/-- Original row, arity, height, and root limits bound the full repeated forest before any edit. -/
theorem profiled_repeated_forest (nodes edgeCost : Nat) (nodeEntry : Interned NodeKey)
    (edgeEntry : Interned (EdgeKey Symbol Guard)) :
    let row : EdgeValue Symbol Guard := .mk edgeEntry [.empty, .empty]
    let value : Value Symbol Guard := .node nodeEntry [row, row] 0 []
    childrenNodes nodes [value, value] ≤ 10 * nodes + 2 ∧ childrenEdges edgeCost [value, value] ≤ 10 * edgeCost + 4 := by
  let row : EdgeValue Symbol Guard := .mk edgeEntry [.empty, .empty]
  let value : Value Symbol Guard := .node nodeEntry [row, row] 0 []
  have profile : ChildrenShape 2 2 [value, value] := by
    simp [value, row, ChildrenShape, NodeShape, RowsShape, EdgeShape]
  have bounded : childrenHeight [value, value] ≤ 1 := by
    simp [value, row, childrenHeight, height, edgesHeight, edgeHeight]
  have result := forest_profile nodes edgeCost [value, value] profile 2 1 (by simp) bounded
  simpa only [Counts.nodeCount, Counts.edgeCount] using result

#print axioms repeated_literal_cost
#check @repeated_literal_cost
#print axioms descendant_leaf_cost
#check @descendant_leaf_cost
#print axioms profiled_repeated_forest
#check @profiled_repeated_forest
end MicroCFTA.EditBudgetNumberChecks


namespace MicroCFTA.EditCallbackCountKernels
open Cache InternedConstructorTemplates SourceEqualityEdits
open SourceCurrentAllocatedSharedEditGraph
open SourceCurrentAllocatedFiniteOrdinaryEditCallbackCounts
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Leaf" => SourceCurrentAllocatedSharedTargetLeaf.Leaf
local notation "EdgeCount" => SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds.edgeCount
local notation "Positions" => SourceCurrentAllocatedFiniteOrdinaryValuePositions.node
local notation "RowPositions" => SourceCurrentAllocatedFiniteOrdinaryValuePositions.rows
local notation "ChildPositions" => SourceCurrentAllocatedFiniteOrdinaryValuePositions.children
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

theorem ignored_branches (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
    (entries : List (Int × Edits EqualityNormalize.Path)) (path : EqualityNormalize.Path) (state : SharedState width) :
    NodeCount (.empty (record := record) (originals := originals) (entries := entries) (state := state)) 0 ∧
      0 ≤ Positions (.empty : Value Symbol Guard) ∧
      ListCount (.leaf (record := record) (originals := originals) (target := path)
        (values := [.empty, .empty]) (state := state)) 0 ∧
      0 ≤ ChildPositions ([.empty, .empty] : List (Value Symbol Guard)) := by
  have first : NodeCount (.empty (record := record) (originals := originals) (entries := entries) (state := state)) 0 := .empty
  have last : ListCount (.leaf (record := record) (originals := originals) (target := path)
      (values := [.empty, .empty]) (state := state)) 0 := .leaf
  exact ⟨first, first.bound .empty, last, last.bound (.cons .empty (.cons .empty .nil))⟩

theorem empty_leaf {record originals path result} {before after : SharedState width}
    (actual : Leaf record originals path .empty before result after) :
    NodeCount (.leaf actual) 1 ∧ 1 ≤ 1 + 0 * EdgeCount 0 0 0 := by
  have own : NodeCount (.leaf actual) 1 := .leaf actual
  exact ⟨own, own.profile 0 0 0 (by trivial) (Nat.le_refl _)⟩

theorem repeated_empty_positions {record originals path firstResult lastResult}
    {before middle after : SharedState width}
    (first : Leaf record originals path .empty before firstResult middle)
    (last : Leaf record originals path .empty middle lastResult after) :
    let entries : List (Int × Edits EqualityNormalize.Path) := [(0, Edits.editAt path), (1, Edits.editAt path)]
    ∃ actual : EditList record originals (.editBelow entries) [.empty, .empty] before [firstResult, lastResult] after,
      ListCount actual 2 ∧ 2 ≤ 2 * (1 + 0 * EdgeCount 0 0 0) := by
  intro entries
  have foundFirst : SourceEqualityNeededMap.lookup (0 : Int) entries = some (Edits.editAt path) := rfl
  have foundLast : SourceEqualityNeededMap.lookup (1 : Int) entries = some (Edits.editAt path) := rfl
  let tail : EditChildren record originals entries 1 [.empty] middle [lastResult] after :=
    .selected 1 foundLast (.leaf last) .nil
  let actual : EditList record originals (.editBelow entries) [.empty, .empty] before [firstResult, lastResult] after :=
    .children (.selected 0 foundFirst (.leaf first) tail)
  have tailCount : ChildrenCount tail 1 := .selected (found := foundLast) (.leaf last) .nil
  have own : ListCount actual 2 := .children (.selected (found := foundFirst) (.leaf first) tailCount)
  have profile : ChildrenShape 0 0 ([.empty, .empty] : List (Value Symbol Guard)) := by
    simp [ChildrenShape, NodeShape]
  exact ⟨actual, own, own.profile 0 0 2 0 profile (Nat.le_refl _)
    (by simp [MergedOrdinaryHeight.childrenHeight, MergedOrdinaryHeight.height])⟩

theorem repeated_rows {record originals path firstResult lastResult}
    (rowEntry : Interned (EdgeKey Symbol Guard)) {before middle afterLeaf : SharedState width}
    (first : Leaf record originals path .empty before firstResult middle)
    (last : Leaf record originals path .empty
      (advanceHeap middle (run (makeEdge rowEntry.key.symbol rowEntry.key.constraint [firstResult])
        middle.checked.native.machine.heap).2) lastResult afterLeaf) :
    let row : EdgeValue Symbol Guard := .mk rowEntry [.empty]
    let firstBuilt := run (makeEdge rowEntry.key.symbol rowEntry.key.constraint [firstResult]) middle.checked.native.machine.heap
    let lastBuilt := run (makeEdge rowEntry.key.symbol rowEntry.key.constraint [lastResult]) afterLeaf.checked.native.machine.heap
    let after := advanceHeap afterLeaf lastBuilt.2
    ∃ actual : EditRows record originals [(0, Edits.editAt path)] [row, row] before [firstBuilt.1, lastBuilt.1] after,
      RowsCount actual 2 ∧ 2 ≤ RowPositions [row, row] := by
  intro row firstBuilt lastBuilt after
  let next : SharedState width := advanceHeap middle firstBuilt.2
  have found : SourceEqualityNeededMap.lookup (0 : Int) [(0, Edits.editAt path)] = some (Edits.editAt path) := rfl
  let headChildren : EditChildren record originals [(0, Edits.editAt path)] 0 [.empty] before [firstResult] middle :=
    .selected 0 found (.leaf first) .nil
  let tailChildren : EditChildren record originals [(0, Edits.editAt path)] 0 [.empty] next [lastResult] afterLeaf :=
    .selected 0 found (.leaf last) .nil
  let tailRows : EditRows record originals [(0, Edits.editAt path)] [row] next [lastBuilt.1] after :=
    .cons tailChildren rfl .nil
  let actual : EditRows record originals [(0, Edits.editAt path)] [row, row] before [firstBuilt.1, lastBuilt.1] after :=
    .cons headChildren rfl tailRows
  have headCount : ChildrenCount headChildren 1 := .selected (found := found) (.leaf first) .nil
  have tailCount : ChildrenCount tailChildren 1 := .selected (found := found) (.leaf last) .nil
  have restCount : RowsCount tailRows 1 := .cons (rebuilt := rfl) tailCount .nil
  have own : RowsCount actual 2 := .cons (firstCalls := 1) (restCalls := 1) (rebuilt := rfl) headCount restCount
  exact ⟨actual, own, own.bound (.cons (.cons .empty .nil) (.cons (.cons .empty .nil) .nil))⟩

#check @ignored_branches
#print axioms ignored_branches
#check @empty_leaf
#print axioms empty_leaf
#check @repeated_empty_positions
#print axioms repeated_empty_positions
#check @repeated_rows
#print axioms repeated_rows

end MicroCFTA.EditCallbackCountKernels


set_option linter.all true
set_option pp.universes true

namespace MicroCFTA.EditResourceIntegrationChecks
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityEdits SourceEqualityEditLeafPaths
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentEditDomains SourceCurrentAllocatedSharedEditGraph
open SourceCurrentAllocatedFiniteOrdinaryEditCallbackCounts
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests)
open MergedOrdinaryHeight (childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Stored" => SourceCurrentAllocatedFiniteOrdinarySharedProfiles.Stored
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- Two selected source positions each execute one actual leaf callback. -/
theorem two_selected_count {record originals path first second before results after}
    (actual : EditChildren (width := width) record originals [(0, .editAt path), (1, .editAt path)] 0 [first, second] before results after) :
    ChildrenCount actual 2 := by
  cases actual with
  | unselected _ absent _ => simp [SourceEqualityNeededMap.lookup] at absent
  | selected _ found first rest =>
      simp [SourceEqualityNeededMap.lookup] at found
      cases found
      cases first with
      | leaf one =>
          cases rest with
          | unselected _ absent _ => simp [SourceEqualityNeededMap.lookup] at absent
          | selected _ found second rest =>
              simp [SourceEqualityNeededMap.lookup] at found
              cases found
              cases second with
              | leaf two =>
                  cases rest with
                  | nil => exact .selected (found := rfl) (.leaf one) (.selected (found := rfl) (.leaf two) .nil)

section Initial
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
variable (bits : Nat) (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
variable (base : InternedConstructorTemplates.State Symbol Guard) (before : Shared (bits + 2))
variable (rows arity count depth bound inputRows inputArity inputBound : Nat)
variable (known : Values base originals) (coherent : SourceEqualityClassOrder.Coherent record)
variable (active : EqualityNormalize.Nontrivial record.paths) (captured : ChildrenShape rows arity originals)
variable (lengthBound : originals.length ≤ count) (pathsBound : ∀ path ∈ record.paths, path.length ≤ depth)
variable (capturedHeight : childrenHeight originals ≤ bound) (inventory : Inventory)
variable (ready : Ready formulas solver inventory record originals base before)
local notation "TargetR" => SourceCurrentAllocatedFiniteOrdinarySharedForceResources.targetRows record rows count depth bound
local notation "LeafN" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.leafNodes record rows arity count depth bound inputRows inputArity inputBound
local notation "LeafE" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.leafEdges record rows arity count depth bound inputRows inputArity inputBound
local notation "NN" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.nodeNodes LeafN
local notation "NE" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.nodeEdges LeafE
local notation "CN" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.childrenNodes LeafN
local notation "CE" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.childrenEdges LeafE
variable (stored : Stored (SourceCurrentAllocatedFiniteOrdinarySharedForceResources.targetRows record rows count depth bound) (max arity 1) bound before)
variable (path : EqualityNormalize.Path) (member : path ∈ record.paths)
variable (memos : Memos) (valid : Valid before.checked.native.machine.heap memos)
include known coherent active captured lengthBound pathsBound capturedHeight ready stored member valid

/-- Empty still invokes a node callback in the constructed resource execution. -/
theorem constructed_empty_leaf
    (nodes : before.checked.native.machine.heap.nodes.next + LeafN ≤ 2 ^ bits)
    (edges : before.checked.native.machine.heap.edges.next + LeafE ≤ 2 ^ (bits + 2)) :
    ∃ result after next final requests, ∃ actual : EditNode record originals (.editAt path) .empty before result after,
      NodeReads formulas solver base actual memos final ∧ NodeCount actual 1 ∧
      SourceCurrentAllocatedSharedEditEffects.NodeReceipt formulas solver next record originals base .empty before result after memos final ∧
      Stored TargetR (max arity 1) bound after ∧
      Trace before.checked.native.machine.heap after.checked.native.machine.heap requests ∧
      nodeRequests requests ≤ LeafN ∧ edgeRequests requests ≤ LeafE := by
  have safe : Safe (.editAt path) (.empty : Value Symbol Guard) :=
    closed_safe _ _ _ ready.checked.semantic (empty_available _) rfl
  have nodeCost : NN (.empty : Value Symbol Guard) = LeafN ∧ NE (.empty : Value Symbol Guard) = LeafE :=
    SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.node_empty LeafN LeafE
  obtain ⟨result, after, next, final, requests, actual, reads, receipt, retained, _produced, _narrow, _height,
    _stable, trace, nodeCount, edgeCount, _capacity, _nodeSupply, _edgeSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryEditResources.node formulas solver bits record originals base rows arity count depth bound
      inputRows inputArity inputBound known coherent active captured lengthBound pathsBound capturedHeight
      inventory (.editAt path) .empty before ready stored (empty_available _) trivial (Nat.zero_le _)
      (by simp only [Populated]) (by exact ⟨[], path, by simp [leaves]⟩) (by simpa only [Allowed, All] using member) safe memos valid
      (by simpa only [nodeCost.1] using nodes) (by simpa only [nodeCost.2] using edges)
  have counted : NodeCount actual 1 := by cases actual with | leaf leaf => exact .leaf leaf
  exact ⟨result, after, next, final, requests, actual, reads, counted, receipt, retained, trace,
    by simpa only [nodeCost.1] using nodeCount, by simpa only [nodeCost.2] using edgeCount⟩

/-- The concrete producer edits two repeated Empty positions, retaining the exact two-callback certificate. -/
theorem constructed_two_empty_leaves
    (nodes : before.checked.native.machine.heap.nodes.next + CN ([.empty, .empty] : List (Value Symbol Guard)) ≤ 2 ^ bits)
    (edges : before.checked.native.machine.heap.edges.next + CE ([.empty, .empty] : List (Value Symbol Guard)) ≤ 2 ^ (bits + 2)) :
    ∃ results after next final requests,
      ∃ actual : EditChildren record originals [(0, .editAt path), (1, .editAt path)] 0 ([.empty, .empty] : List (Value Symbol Guard)) before results after,
        ChildrenReads formulas solver base actual memos final ∧ ChildrenCount actual 2 ∧
        SourceCurrentAllocatedSharedEditEffects.ChildrenReceipt formulas solver next record originals base ([.empty, .empty] : List (Value Symbol Guard)) before results after memos final ∧
        Stored TargetR (max arity 1) bound after ∧ results.length = 2 ∧
        SourceCurrentAllocatedSharedEditWorkerCompletion.StableRun
          (fun e p h m s n => SourceCurrentAllocatedSharedEditWorker.children
            (SourceCurrentAllocatedSharedEditWorker.edit record originals e p h m s n)
            [(0, .editAt path), (1, .editAt path)] 0 ([.empty, .empty] : List (Value Symbol Guard)) before) results after ∧
        Trace before.checked.native.machine.heap after.checked.native.machine.heap requests ∧
        nodeRequests requests ≤ CN ([.empty, .empty] : List (Value Symbol Guard)) ∧ edgeRequests requests ≤ CE ([.empty, .empty] : List (Value Symbol Guard)) := by
  have populated : Populated (.editBelow [(0, .editAt path), (1, .editAt path)]) := by
    rw [Populated]
    intro index child included
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at included
    rcases included with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by simp only [Populated], [], path, by simp [leaves]⟩
  have allowed : Allowed record (.editBelow [(0, .editAt path), (1, .editAt path)]) := by
    rw [Allowed, All]
    intro index child included
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at included
    rcases included with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simpa only [All] using member
  have available : Values before.checked.native.machine.heap ([.empty, .empty] : List (Value Symbol Guard)) := by
    intro value selected
    have same : value = .empty := by simpa using selected
    exact same ▸ empty_available _
  have safe : ChildrenSafe [(0, .editAt path), (1, .editAt path)] 0 ([.empty, .empty] : List (Value Symbol Guard)) := by
    intro query child found value selected
    have same : value = .empty := by
      have present := List.mem_of_getElem? selected
      simpa using present
    subst value
    exact closed_safe _ _ _ ready.checked.semantic (empty_available _) rfl
  obtain ⟨results, after, next, final, requests, actual, reads, receipt, retained, _produced, _narrow, sameLength,
    stable, trace, nodeCount, edgeCount, _capacity, _nodeSupply, _edgeSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryEditResources.children formulas solver bits record originals base rows arity count depth bound
      inputRows inputArity inputBound known coherent active captured lengthBound pathsBound capturedHeight
      inventory [(0, .editAt path), (1, .editAt path)] 0 ([.empty, .empty] : List (Value Symbol Guard)) before ready stored available
      ⟨trivial, trivial, trivial⟩ (Nat.zero_le _) populated allowed safe memos valid nodes edges
  exact ⟨results, after, next, final, requests, actual, reads, two_selected_count actual, receipt, retained,
    sameLength, stable, trace, nodeCount, edgeCount⟩
end Initial

#print axioms two_selected_count
#check @two_selected_count
#print axioms constructed_empty_leaf
#check @constructed_empty_leaf
#print axioms constructed_two_empty_leaves
#check @constructed_two_empty_leaves
end MicroCFTA.EditResourceIntegrationChecks


namespace MicroCFTA.ClassResourceChecks
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedClassEdits (Class ClassReads Receipt)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace)
open SourceCurrentAllocatedFiniteOrdinaryClassResources
open MergedOrdinaryHeight (childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "StableRun" => SourceCurrentAllocatedClassWorkerCompletion.StableRun
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- An empty forest uses no bound or request and retains the whole checked state and Merge memo. -/
theorem empty_class_identity (record : SourceEqualityClassOrder.Record) (rows arity depth bound : Nat)
    (e p h m s n : Nat) (before : Checked width) (memo : Memo) :
    nodeBudget record rows arity 0 depth bound = 0 ∧ edgeBudget record rows arity 0 depth bound = 0 ∧
    SourceCurrentAllocatedClassWorker.runClass e p h m s n record [] before memo = .done [] before memo := by
  refine ⟨by simp [nodeBudget], by simp [edgeBudget], ?_⟩
  unfold SourceCurrentAllocatedClassWorker.runClass
  cases SourceCurrentAllocatedClassEditPlan.compiled record <;> rfl

/-- A second class captures the first actual output and uses its computed inventory and warm certificates. -/
theorem two_actual_classes (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits : Nat) (first second : SourceEqualityClassOrder.Record)
    (firstCoherent : SourceEqualityClassOrder.Coherent first) (firstActive : EqualityNormalize.Nontrivial first.paths)
    (secondCoherent : SourceEqualityClassOrder.Coherent second) (secondActive : EqualityNormalize.Nontrivial second.paths)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (memo : Memo) (ready : Ready before)
    (admitted : At formulas solver inventory before) (available : Values before.native.machine.heap values)
    (physical : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (rows arity count firstDepth secondDepth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count) (firstPaths : ∀ path ∈ first.paths, path.length ≤ firstDepth)
    (secondPaths : ∀ path ∈ second.paths, path.length ≤ secondDepth) (heightBound : childrenHeight values ≤ bound)
    (nodes : before.native.machine.heap.nodes.next + nodeBudget first rows arity count firstDepth bound +
      nodeBudget second (outputRows first rows count firstDepth bound) (outputArity arity) count secondDepth bound ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + edgeBudget first rows arity count firstDepth bound +
      edgeBudget second (outputRows first rows count firstDepth bound) (outputArity arity) count secondDepth bound ≤ 2 ^ (bits + 2)) :
    ∃ middleValues middle current next currentMemos results after saved last final requests,
      ∃ firstActual : Class first values before memo middleValues middle current,
      ∃ secondActual : Class second middleValues middle current results after saved,
        ClassReads formulas solver firstActual memos currentMemos ∧
        Receipt formulas solver next first values before memo middleValues middle current memos currentMemos ∧
        ClassReads formulas solver secondActual currentMemos final ∧
        Receipt formulas solver last second middleValues middle current results after saved currentMemos final ∧
        StableRun (fun e p h m s n => SourceCurrentAllocatedClassWorker.runClass e p h m s n
          first values before memo) middleValues middle current ∧
        StableRun (fun e p h m s n => SourceCurrentAllocatedClassWorker.runClass e p h m s n
          second middleValues middle current) results after saved ∧
        NativeStored after.native ∧ OutputStored after.native ∧ Profiles saved ∧
        ChildrenShape (outputRows second (outputRows first rows count firstDepth bound) count secondDepth bound)
          (outputArity (outputArity arity)) results ∧
        results.length = values.length ∧ childrenHeight results ≤ bound ∧
        Trace before.native.machine.heap after.native.machine.heap requests ∧
        SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity bits after ∧
        after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + nodeBudget first rows arity count firstDepth bound +
          nodeBudget second (outputRows first rows count firstDepth bound) (outputArity arity) count secondDepth bound ∧
        after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + edgeBudget first rows arity count firstDepth bound +
          edgeBudget second (outputRows first rows count firstDepth bound) (outputArity arity) count secondDepth bound := by
  obtain ⟨middleValues, middle, current, next, currentMemos, firstRequests, firstActual, firstReads, firstReceipt,
    firstStable, firstNative, firstOutput, firstProfiles, middleProfile, _firstNarrow, firstLength, middleHeight,
    firstTrace, _firstNodes, _firstEdges, _middleCapacity, firstNodeSupply, firstEdgeSupply⟩ :=
    complete formulas solver inventory bits first firstCoherent firstActive values before memo ready admitted available
      physical profiles native output covered memos valid rows arity count firstDepth bound profile lengthBound firstPaths heightBound
      (by omega) (by omega)
  obtain ⟨results, after, saved, last, final, secondRequests, secondActual, secondReads, secondReceipt,
    secondStable, lastNative, lastOutput, lastProfiles, resultProfile, _secondNarrow, secondLength, resultHeight,
    secondTrace, _secondNodes, _secondEdges, finalCapacity, secondNodeSupply, secondEdgeSupply⟩ :=
    complete formulas solver next bits second secondCoherent secondActive middleValues middle current firstReceipt.ready
      firstReceipt.admitted firstReceipt.available firstReceipt.stored firstProfiles firstNative firstOutput firstReceipt.covered
      currentMemos firstReceipt.globals.valid (outputRows first rows count firstDepth bound) (outputArity arity) count secondDepth bound
      middleProfile (by omega) secondPaths middleHeight (by omega) (by omega)
  exact ⟨middleValues, middle, current, next, currentMemos, results, after, saved, last, final,
    firstRequests ++ secondRequests, firstActual, secondActual, firstReads, firstReceipt, secondReads, secondReceipt,
    firstStable, secondStable, lastNative, lastOutput, lastProfiles, resultProfile,
    by omega, resultHeight, firstTrace.trans secondTrace, finalCapacity, by omega, by omega⟩

#print axioms empty_class_identity
#check @empty_class_identity
#print axioms two_actual_classes
#check @two_actual_classes
end MicroCFTA.ClassResourceChecks


namespace PassResourceIntegration
open MicroCFTA Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedClassPass (Fold FoldReads Pass PassReads Receipt)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests)
open SourceCurrentAllocatedFiniteOrdinaryPassResources
open MergedOrdinaryHeight (childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "Class" => SourceCurrentAllocatedClassEdits.Class
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem two_order {bits : Nat} {first second : Record} {values results : List (Value Symbol Guard)}
    {before after : Checked (bits + 2)} {memo saved : Memo}
    (actual : Fold [first, second] values before memo results after saved) :
    ∃ middle step current, Class second values before memo middle step current ∧
      Class first middle step current results after saved := by
  cases actual with
  | cons tail head =>
      cases tail with
      | cons initial secondActual =>
          cases initial
          exact ⟨_, _, _, secondActual, head⟩

private theorem empty_memos {bits : Nat} {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {values results : List (Value Symbol Guard)}
    {before after : Checked (bits + 2)} {memo saved : Memo} {memos final : Memos}
    {actual : Pass [] values before memo results after saved}
    (reads : PassReads formulas solver actual memos final) : final = memos := by
  cases reads with
  | done remaining =>
      cases remaining
      rfl

/-- Both classes are constructed from one initial budget and share the actual tail state. -/
theorem two_classes (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits : Nat) (first second : Record)
    (coherent : ∀ record ∈ [first, second], SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ [first, second], EqualityNormalize.Nontrivial record.paths)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (physical : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count)
    (pathsBound : ∀ record ∈ [first, second], ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound)
    (nodes : before.native.machine.heap.nodes.next + nodeBudget [first, second] rows arity count depth bound ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + edgeBudget [first, second] rows arity count depth bound ≤ 2 ^ (bits + 2)) :
    ∃ middle step current results after saved next final requests,
    ∃ actual : Fold [first, second] values before memo results after saved,
      FoldReads formulas solver actual memos final ∧
      Class second values before memo middle step current ∧ Class first middle step current results after saved ∧
      Receipt formulas solver next [first, second] values before memo results after saved memos final ∧
      SourceCurrentAllocatedClassWorkerCompletion.StableRun
        (fun e p h m s n => SourceCurrentAllocatedClassWorker.fold e p h m s n [first, second] values before memo) results after saved ∧
      NativeStored after.native ∧ OutputStored after.native ∧ Profiles saved ∧
      ChildrenShape (outputRows [first, second] rows count depth bound) (outputArity [first, second] arity) results ∧
      All₂ NodeNarrow values results ∧ results.length = values.length ∧ childrenHeight results ≤ bound ∧
      Trace before.native.machine.heap after.native.machine.heap requests ∧
      nodeRequests requests ≤ nodeBudget [first, second] rows arity count depth bound ∧
      edgeRequests requests ≤ edgeBudget [first, second] rows arity count depth bound ∧
      SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity bits after := by
  obtain ⟨results, after, saved, next, final, requests, actual, reads, receipt, stable,
    nativeAfter, outputAfter, profilesAfter, produced, related, sameLength, finalHeight,
    trace, nodeCount, edgeCount, capacity, _nodeSupply, _edgeSupply⟩ :=
    fold_complete formulas solver inventory bits [first, second] coherent active values before memo ready admitted available
      physical profiles native output covered memos valid rows arity count depth bound profile lengthBound pathsBound heightBound nodes edges
  obtain ⟨middle, step, current, secondActual, firstActual⟩ := two_order actual
  exact ⟨middle, step, current, results, after, saved, next, final, requests, actual, reads,
    secondActual, firstActual, receipt, stable, nativeAfter, outputAfter, profilesAfter, produced,
    related, sameLength, finalHeight, trace, nodeCount, edgeCount, capacity⟩

/-- An empty class list can erase an Empty-containing forest with no Work or table change. -/
theorem empty_pass (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits : Nat) (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (physical : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count) (heightBound : childrenHeight values ≤ bound)
    (nodes : before.native.machine.heap.nodes.next ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next ≤ 2 ^ (bits + 2)) :
    ∃ next, Receipt formulas solver next [] values before memo (EqualityLeafProjectionRuntimeEmpty.propagate values)
      before memo memos memos ∧
      ChildrenShape rows arity (EqualityLeafProjectionRuntimeEmpty.propagate values) ∧
      All₂ NodeNarrow values (EqualityLeafProjectionRuntimeEmpty.propagate values) ∧
      SourceCurrentAllocatedClassWorker.pass 0 0 0 0 0 0 [] values before memo =
        .done (EqualityLeafProjectionRuntimeEmpty.propagate values) before memo ∧
      Trace before.native.machine.heap before.native.machine.heap [] ∧ nodeRequests ([] : List (SourceCurrentAllocatedFiniteOrdinaryReservations.Request Symbol Guard)) = 0 ∧
      edgeRequests ([] : List (SourceCurrentAllocatedFiniteOrdinaryReservations.Request Symbol Guard)) = 0 ∧
      (∀ ambient (_symbol : Symbol) terms,
        All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient)
          (EqualityLeafProjectionRuntimeEmpty.propagate values) terms ↔
        All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms) := by
  obtain ⟨results, after, saved, next, final, _requests, actual, reads, receipt, _stable,
    _nativeAfter, _outputAfter, _profilesAfter, produced, related, _sameLength, _finalHeight,
    _trace, _nodeCount, _edgeCount, _capacity, _nodeSupply, _edgeSupply⟩ :=
    complete formulas solver inventory bits [] (by simp) (by simp) values before memo ready admitted available
      physical profiles native output covered memos valid rows arity count depth bound profile lengthBound (by simp) heightBound
      (by simpa only [nodeBudget, Nat.add_zero] using nodes) (by simpa only [edgeBudget, Nat.add_zero] using edges)
  have sameMemos := empty_memos reads
  subst final
  cases actual with
  | done fold =>
      cases fold
      refine ⟨next, receipt, produced, related, rfl, .refl _, rfl, rfl, ?_⟩
      intro ambient symbol terms
      exact (receipt.language ambient symbol terms).2 (by simp)

set_option pp.explicit true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 100000
set_option format.width 200
#print axioms two_classes
#check @two_classes
#print axioms empty_pass
#check @empty_pass
end PassResourceIntegration
