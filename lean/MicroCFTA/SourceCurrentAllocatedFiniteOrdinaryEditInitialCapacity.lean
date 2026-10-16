import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEditResources
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEditCapacity
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinarySharedInitialCapacity

/-!
# Existing edit capacity plans from initial resources

Initial profiles and total headroom derive the numeric edit plans.
Each later plan uses a constructed earlier resource prefix.
Literal worker uniqueness identifies every raw earlier return.
No completed edit or future returned-state fact is an initial premise.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEditInitialCapacity
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityEdits SourceEqualityEditLeafPaths
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentEditDomains SourceCurrentAllocatedSharedEditGraph
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape RowsShape ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace nodeRequests_append edgeRequests_append)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests observe makeEdge_observe)
open MergedOrdinaryHeight (height edgesHeight childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Stored" => SourceCurrentAllocatedFiniteOrdinarySharedProfiles.Stored
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
open SourceCurrentAllocatedFiniteOrdinaryEditCapacity
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}


private theorem node_unique {record originals edits value before first after second later}
    (one : EditNode (width := width) record originals edits value before first after)
    (two : EditNode record originals edits value before second later) : first = second ∧ after = later := by
  obtain ⟨a, ha⟩ := SourceCurrentAllocatedSharedEditWorkerCompletion.stable_uniform
    (SourceCurrentAllocatedSharedEditWorkerCompletion.node_complete one)
  obtain ⟨b, hb⟩ := SourceCurrentAllocatedSharedEditWorkerCompletion.stable_uniform
    (SourceCurrentAllocatedSharedEditWorkerCompletion.node_complete two)
  exact SourceCurrentAllocatedSharedEditWorker.Outcome.done.inj
    ((ha (max a b) (Nat.le_max_left _ _)).symm.trans (hb (max a b) (Nat.le_max_right _ _)))

private theorem children_unique {record originals entries index values before first after second later}
    (one : EditChildren (width := width) record originals entries index values before first after)
    (two : EditChildren record originals entries index values before second later) : first = second ∧ after = later := by
  obtain ⟨a, ha⟩ := SourceCurrentAllocatedSharedEditWorkerCompletion.stable_uniform
    (SourceCurrentAllocatedSharedEditWorkerCompletion.children_complete one)
  obtain ⟨b, hb⟩ := SourceCurrentAllocatedSharedEditWorkerCompletion.stable_uniform
    (SourceCurrentAllocatedSharedEditWorkerCompletion.children_complete two)
  exact SourceCurrentAllocatedSharedEditWorker.Outcome.done.inj
    ((ha (max a b) (Nat.le_max_left _ _)).symm.trans (hb (max a b) (Nat.le_max_right _ _)))

variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
variable (bits : Nat) (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) (base : Heap)
variable (rowLimit arity count depth bound inputRows inputArity inputBound : Nat)
local notation "TargetR" => SourceCurrentAllocatedFiniteOrdinarySharedForceResources.targetRows record rowLimit count depth bound
local notation "OutR" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.outputRows record rowLimit count depth bound inputRows
local notation "OutA" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.outputArity arity inputArity
local notation "LeafN" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.leafNodes record rowLimit arity count depth bound inputRows inputArity inputBound
local notation "LeafE" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.leafEdges record rowLimit arity count depth bound inputRows inputArity inputBound
local notation "NN" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.nodeNodes LeafN
local notation "NE" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.nodeEdges LeafE
local notation "CN" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.childrenNodes LeafN
local notation "CE" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.childrenEdges LeafE
local notation "RN" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.rowsNodes LeafN
local notation "RE" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.rowsEdges LeafE


private def NodeLaw (edits : Edits EqualityNormalize.Path) (value : Value Symbol Guard) : Prop :=
  ∀ (before : Shared (bits + 2)) (inventory : Inventory),
    Ready formulas solver inventory record originals base before → Stored TargetR (max arity 1) bound before →
    Available before.checked.native.machine.heap value → NodeShape inputRows inputArity value → height value ≤ inputBound →
    Populated edits → HasLeaf edits → Allowed record edits → Safe edits value →
    ∀ memos, Valid before.checked.native.machine.heap memos →
      before.checked.native.machine.heap.nodes.next + NN value ≤ 2 ^ bits →
      before.checked.native.machine.heap.edges.next + NE value ≤ 2 ^ (bits + 2) →
      NodeCapacity bits record originals edits value before

private def ChildrenLaw (entries : List (Int × Edits EqualityNormalize.Path)) (offset : Nat)
    (values : List (Value Symbol Guard)) : Prop :=
  ∀ (before : Shared (bits + 2)) (inventory : Inventory),
    Ready formulas solver inventory record originals base before → Stored TargetR (max arity 1) bound before →
    Values before.checked.native.machine.heap values → ChildrenShape inputRows inputArity values → childrenHeight values ≤ inputBound →
    Populated (.editBelow entries) → Allowed record (.editBelow entries) → ChildrenSafe entries offset values →
    ∀ memos, Valid before.checked.native.machine.heap memos →
      before.checked.native.machine.heap.nodes.next + CN values ≤ 2 ^ bits →
      before.checked.native.machine.heap.edges.next + CE values ≤ 2 ^ (bits + 2) →
      ChildrenCapacity bits record originals entries offset values before

private def RowsLaw (entries : List (Int × Edits EqualityNormalize.Path)) (edges : List (EdgeValue Symbol Guard)) : Prop :=
  ∀ (before : Shared (bits + 2)) (inventory : Inventory),
    Ready formulas solver inventory record originals base before → Stored TargetR (max arity 1) bound before →
    Edges before.checked.native.machine.heap edges → RowsShape inputRows inputArity edges → edgesHeight edges ≤ inputBound →
    Populated (.editBelow entries) → Allowed record (.editBelow entries) → RowsSafe entries edges →
    ∀ memos, Valid before.checked.native.machine.heap memos →
      before.checked.native.machine.heap.nodes.next + RN edges ≤ 2 ^ bits →
      before.checked.native.machine.heap.edges.next + RE edges ≤ 2 ^ (bits + 2) →
      RowsCapacity bits record originals entries edges before

local notation "NL" => NodeLaw formulas solver bits record originals base rowLimit arity count depth bound inputRows inputArity inputBound
local notation "CL" => ChildrenLaw formulas solver bits record originals base rowLimit arity count depth bound inputRows inputArity inputBound
local notation "RL" => RowsLaw formulas solver bits record originals base rowLimit arity count depth bound inputRows inputArity inputBound
variable (known : Values base originals) (coherent : SourceEqualityClassOrder.Coherent record)
variable (active : EqualityNormalize.Nontrivial record.paths) (captured : ChildrenShape rowLimit arity originals)
variable (lengthBound : originals.length ≤ count) (pathsBound : ∀ path ∈ record.paths, path.length ≤ depth)
variable (capturedHeight : childrenHeight originals ≤ bound)
include known coherent active captured lengthBound pathsBound capturedHeight


set_option maxHeartbeats 2400000 in
private theorem derive (limit : Nat) :
    (∀ edits (value : Value Symbol Guard), sizeOf value ≤ limit → NL edits value) ∧
    (∀ entries offset (values : List (Value Symbol Guard)), sizeOf values ≤ limit → CL entries offset values) ∧
    (∀ entries (edges : List (EdgeValue Symbol Guard)), sizeOf edges ≤ limit → RL entries edges) := by
  induction limit using Nat.strongRecOn with
  | ind limit ih =>
    refine ⟨?_, ?_, ?_⟩
    · intro edits value sizeBound before inventory ready stored available profile heightBound populated nonempty allowed safe memos valid nodes edges
      cases edits with
      | editAt path =>
          have member : path ∈ record.paths := by simpa only [Allowed, All] using allowed
          have nodeCost := SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.leaf_nodes_bound record rowLimit arity count depth bound inputRows inputArity inputBound before path
          have edgeCost := SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.leaf_edges_bound record rowLimit arity count depth bound inputRows inputArity inputBound before path
          have positive := SourceCurrentAllocatedFiniteOrdinaryValuePositions.node_pos value
          have enoughNodes : LeafN ≤ NN value := by
            unfold SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.nodeNodes
            exact Nat.le_trans (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right LeafN positive) (Nat.le_add_right _ _)
          have enoughEdges : LeafE ≤ NE value := by
            unfold SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.nodeEdges
            exact Nat.le_trans (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right LeafE positive) (Nat.le_add_right _ _)
          unfold SourceCurrentAllocatedFiniteOrdinarySharedLeafResources.nodeBudget at nodeCost
          unfold SourceCurrentAllocatedFiniteOrdinarySharedLeafResources.edgeBudget at edgeCost
          exact .leaf (SourceCurrentAllocatedFiniteOrdinarySharedInitialCapacity.leaf_capacity
            formulas solver inventory bits record originals base before ready known coherent active path member
            rowLimit arity count depth bound captured lengthBound pathsBound capturedHeight stored
            (by omega) (by omega) memos valid value)
      | editBelow entries =>
          cases value with
          | empty => exact .empty
          | reference | mu | union => cases profile
          | node entry originalRows cachedDepth free =>
              have smaller : sizeOf originalRows < limit := by
                simp only [Value.node.sizeOf_spec] at sizeBound
                omega
              have costs := SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.node_ordinary LeafN LeafE entry originalRows cachedDepth free
              have resident := InternedEdgeResidency.resident_edges _ ready.checked.semantic.ready.semantic.1.normal.facts.linked _ available.resident
              exact .ordinary ((ih (sizeOf originalRows) smaller).2.2 entries originalRows (Nat.le_refl _)
                before inventory ready stored resident profile.2
                (by change edgesHeight originalRows + 1 ≤ inputBound at heightBound; omega)
                populated allowed (ordinary_rows safe) memos valid (by omega) (by omega))
    · intro entries offset values sizeBound before inventory ready stored available profile heightBound populated allowed safe memos valid nodes edges
      cases values with
      | nil => exact .nil
      | cons value values =>
          have firstSmaller : sizeOf value < limit := by simp only [List.cons.sizeOf_spec] at sizeBound; omega
          have restSmaller : sizeOf values < limit := by simp only [List.cons.sizeOf_spec] at sizeBound; omega
          have costs := SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.children_cons LeafN LeafE value values
          have childHeight : height value ≤ inputBound := Nat.le_trans (Nat.le_max_left _ _) heightBound
          have restHeight : childrenHeight values ≤ inputBound := Nat.le_trans (Nat.le_max_right _ _) heightBound
          have tailAvailable : Values before.checked.native.machine.heap values :=
            fun child member => available child (List.mem_cons_of_mem _ member)
          cases found : SourceEqualityNeededMap.lookup (offset : Int) entries with
          | none =>
              exact .unselected offset found ((ih (sizeOf values) restSmaller).2.1 entries (offset + 1) values
                (Nat.le_refl _) before inventory ready stored tailAvailable profile.2 restHeight
                populated allowed (children_tail safe) memos valid (by omega) (by omega))
          | some edits =>
              have member := SourceEqualityNeededMap.lookup_mem _ _ _ found
              have childPopulated := (show ∀ index child, (index, child) ∈ entries → Populated child ∧ HasLeaf child from
                by simpa only [Populated] using populated) _ _ member
              have childAllowed : Allowed record edits := by rw [Allowed, All] at allowed; exact allowed _ _ member
              have firstSafe := safe 0 _ (by simpa using found) value rfl
              have firstPlan := (ih (sizeOf value) firstSmaller).1 edits value (Nat.le_refl _) before inventory ready stored
                (available _ List.mem_cons_self) profile.1 childHeight childPopulated.1 childPopulated.2 childAllowed firstSafe
                memos valid (by omega) (by omega)
              refine .selected offset found firstPlan ?_
              intro result middle actual
              obtain ⟨chosenResult, chosenMiddle, next, current, _requests, chosen, _reads, receipt, middleStored,
                _produced, _narrow, _height, _stable, _trace, _nodeCount, _edgeCount, _capacity, nodeSupply, edgeSupply⟩ :=
                SourceCurrentAllocatedFiniteOrdinaryEditResources.node formulas solver bits record originals base
                  rowLimit arity count depth bound inputRows inputArity inputBound known coherent active captured lengthBound pathsBound capturedHeight
                  inventory edits value before ready stored (available _ List.mem_cons_self) profile.1 childHeight
                  childPopulated.1 childPopulated.2 childAllowed firstSafe memos valid (by omega) (by omega)
              obtain ⟨rfl, rfl⟩ := node_unique actual chosen
              exact (ih (sizeOf values) restSmaller).2.1 entries (offset + 1) values (Nat.le_refl _) middle next receipt.ready middleStored
                (fun child member => receipt.effects.keeps.available child (tailAvailable child member)) profile.2 restHeight
                populated allowed (children_tail safe) current receipt.globals.valid (by omega) (by omega)
    · intro entries originalRows sizeBound before inventory ready stored resident profile heightBound populated allowed safe memos valid nodes edges
      cases originalRows with
      | nil => exact .nil
      | cons edge originalRows =>
          have childrenSmaller : sizeOf edge.children < limit := by
            cases edge with
            | mk entry values => simp only [List.cons.sizeOf_spec, EdgeValue.mk.sizeOf_spec, EdgeValue.children] at *; omega
          have restSmaller : sizeOf originalRows < limit := by simp only [List.cons.sizeOf_spec] at sizeBound; omega
          have costs := SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.rows_cons LeafN LeafE edge originalRows
          have original := resident edge List.mem_cons_self
          have available := ready.checked.semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge original
          have childHeight : childrenHeight edge.children ≤ inputBound := by
            have firstHeight := Nat.le_trans (Nat.le_max_left _ _) heightBound
            cases edge with
            | mk entry values => exact firstHeight
          have firstPlan := (ih (sizeOf edge.children) childrenSmaller).2.1 entries 0 edge.children (Nat.le_refl _)
            before inventory ready stored available (SourceCurrentAllocatedFiniteOrdinaryNativeProfile.EdgeShape.children edge profile.1)
            childHeight populated allowed (safe _ List.mem_cons_self) memos valid (by omega) (by omega)
          refine .cons firstPlan ?_
          intro values middle actual
          obtain ⟨chosenValues, chosenMiddle, next, current, _requests, chosen, _reads, receipt, middleStored,
            _produced, _narrow, _length, _stable, _trace, _nodeCount, _edgeCount, _capacity, nodeSupply, edgeSupply⟩ :=
            SourceCurrentAllocatedFiniteOrdinaryEditResources.children formulas solver bits record originals base
              rowLimit arity count depth bound inputRows inputArity inputBound known coherent active captured lengthBound pathsBound capturedHeight
              inventory entries 0 edge.children before ready stored available
              (SourceCurrentAllocatedFiniteOrdinaryNativeProfile.EdgeShape.children edge profile.1) childHeight populated allowed
              (safe _ List.mem_cons_self) memos valid (by omega) (by omega)
          obtain ⟨rfl, rfl⟩ := children_unique actual chosen
          have field := (ready.checked.good.fields edge.entry.key edge original).grows receipt.effects.grows
          have built := SourceCurrentAllocatedSharedEditEffects.edge_physical receipt.ready
            edge.entry.key.symbol edge.entry.key.constraint values field receipt.available
          have globalValid := SourceQueryUnfoldMemo.valid_grows middle.checked.native.machine.heap _ receipt.ready.checked.semantic
            built.2.1.keeps current receipt.globals.valid
          have kept := receipt.effects.keeps.trans built.2.1.keeps
          have allocation := (Trace.work middle.checked.native.machine.heap
            (makeEdge edge.entry.key.symbol edge.entry.key.constraint values)).next_le
          simp only [makeEdge_observe, nodeRequests, edgeRequests] at allocation
          exact (ih (sizeOf originalRows) restSmaller).2.2 entries originalRows (Nat.le_refl _) _ next built.1
            (SourceCurrentAllocatedFiniteOrdinarySharedProfiles.physical_stored middle _ middleStored)
            (fun original member => InternedEdgeResidency.edge_grows _ _ kept.growth original (resident original (List.mem_cons_of_mem _ member)))
            profile.2 (Nat.le_trans (Nat.le_max_right _ _) heightBound) populated allowed
            (fun original member => safe original (List.mem_cons_of_mem _ member)) current globalValid
            (by change (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values)
                  middle.checked.native.machine.heap).2.nodes.next + RN originalRows ≤ 2 ^ bits
                omega)
            (by change (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values)
                  middle.checked.native.machine.heap).2.edges.next + RE originalRows ≤ 2 ^ (bits + 2)
                omega)

/-- Initial total headroom derives every reached node capacity check. -/
theorem node (inventory : Inventory) (edits : Edits EqualityNormalize.Path) (value : Value Symbol Guard)
    (before : Shared (bits + 2))
    (ready : Ready formulas solver inventory record originals base before)
    (stored : Stored TargetR (max arity 1) bound before)
    (available : Available before.checked.native.machine.heap value)
    (profile : NodeShape inputRows inputArity value) (heightBound : height value ≤ inputBound)
    (populated : Populated edits) (nonempty : HasLeaf edits) (allowed : Allowed record edits) (safe : Safe edits value)
    (memos : Memos) (valid : Valid before.checked.native.machine.heap memos)
    (nodes : before.checked.native.machine.heap.nodes.next + NN value ≤ 2 ^ bits)
    (edges : before.checked.native.machine.heap.edges.next + NE value ≤ 2 ^ (bits + 2)) :
    NodeCapacity bits record originals edits value before :=
  (derive formulas solver bits record originals base rowLimit arity count depth bound inputRows inputArity inputBound
    known coherent active captured lengthBound pathsBound capturedHeight (sizeOf value)).1 edits value (Nat.le_refl _)
    before inventory ready stored available profile heightBound populated nonempty allowed safe memos valid nodes edges

/-- Initial total headroom derives every reached children capacity check. -/
theorem children (inventory : Inventory) (entries : List (Int × Edits EqualityNormalize.Path)) (offset : Nat)
    (values : List (Value Symbol Guard)) (before : Shared (bits + 2))
    (ready : Ready formulas solver inventory record originals base before)
    (stored : Stored TargetR (max arity 1) bound before)
    (available : Values before.checked.native.machine.heap values)
    (profile : ChildrenShape inputRows inputArity values) (heightBound : childrenHeight values ≤ inputBound)
    (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (safe : ChildrenSafe entries offset values) (memos : Memos) (valid : Valid before.checked.native.machine.heap memos)
    (nodes : before.checked.native.machine.heap.nodes.next + CN values ≤ 2 ^ bits)
    (edges : before.checked.native.machine.heap.edges.next + CE values ≤ 2 ^ (bits + 2)) :
    ChildrenCapacity bits record originals entries offset values before :=
  (derive formulas solver bits record originals base rowLimit arity count depth bound inputRows inputArity inputBound
    known coherent active captured lengthBound pathsBound capturedHeight (sizeOf values)).2.1 entries offset values (Nat.le_refl _)
    before inventory ready stored available profile heightBound populated allowed safe memos valid nodes edges

/-- Initial total headroom derives every reached rows capacity check. -/
theorem rows (inventory : Inventory) (entries : List (Int × Edits EqualityNormalize.Path))
    (originalRows : List (EdgeValue Symbol Guard)) (before : Shared (bits + 2))
    (ready : Ready formulas solver inventory record originals base before)
    (stored : Stored TargetR (max arity 1) bound before)
    (resident : Edges before.checked.native.machine.heap originalRows)
    (profile : RowsShape inputRows inputArity originalRows) (heightBound : edgesHeight originalRows ≤ inputBound)
    (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (safe : RowsSafe entries originalRows) (memos : Memos) (valid : Valid before.checked.native.machine.heap memos)
    (nodes : before.checked.native.machine.heap.nodes.next + RN originalRows ≤ 2 ^ bits)
    (edges : before.checked.native.machine.heap.edges.next + RE originalRows ≤ 2 ^ (bits + 2)) :
    RowsCapacity bits record originals entries originalRows before :=
  (derive formulas solver bits record originals base rowLimit arity count depth bound inputRows inputArity inputBound
    known coherent active captured lengthBound pathsBound capturedHeight (sizeOf originalRows)).2.2 entries originalRows (Nat.le_refl _)
    before inventory ready stored resident profile heightBound populated allowed safe memos valid nodes edges

/-- The ignored list-root leaf needs no query capacity. -/
theorem list (inventory : Inventory) (edits : Edits EqualityNormalize.Path)
    (values : List (Value Symbol Guard)) (before : Shared (bits + 2))
    (ready : Ready formulas solver inventory record originals base before)
    (stored : Stored TargetR (max arity 1) bound before)
    (available : Values before.checked.native.machine.heap values)
    (profile : ChildrenShape inputRows inputArity values) (heightBound : childrenHeight values ≤ inputBound)
    (populated : Populated edits) (allowed : Allowed record edits)
    (safe : SourceCurrentAllocatedSharedEditEffects.ListSafe edits values)
    (memos : Memos) (valid : Valid before.checked.native.machine.heap memos)
    (nodes : before.checked.native.machine.heap.nodes.next + CN values ≤ 2 ^ bits)
    (edges : before.checked.native.machine.heap.edges.next + CE values ≤ 2 ^ (bits + 2)) :
    ListCapacity bits record originals edits values before := by
  cases edits with
  | editAt _ => trivial
  | editBelow entries =>
      exact children formulas solver bits record originals base rowLimit arity count depth bound inputRows inputArity inputBound
        known coherent active captured lengthBound pathsBound capturedHeight inventory entries 0 values before ready stored
        available profile heightBound populated allowed safe memos valid nodes edges

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEditInitialCapacity
