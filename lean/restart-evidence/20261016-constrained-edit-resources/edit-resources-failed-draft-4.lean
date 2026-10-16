import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEdits
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputConstructors
import MicroCFTA.SourceCurrentAllocatedSharedEditWorkerCompletion

/-!
# Constructed simultaneous edits from initial resources

Each recursive call visits the original immutable input positions.
A selected leaf constructs its own shared target and native query.
Reconstruction retains the source guard and actual constructor heap.
Initial cumulative headroom derives every later call's headroom.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEditResources
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityEdits SourceEqualityEditLeafPaths
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentEditDomains SourceCurrentAllocatedSharedEditGraph
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape RowsShape ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace nodeRequests_append edgeRequests_append)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests observe makeNode_requests makeEdge_observe)
open MergedOrdinaryHeight (height edgesHeight childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Stored" => SourceCurrentAllocatedFiniteOrdinarySharedProfiles.Stored
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
variable [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

private def Budget (before after : Shared width) (nodes edges : Nat) : Prop :=
  ∃ requests, Trace before.checked.native.machine.heap after.checked.native.machine.heap requests ∧
    nodeRequests requests ≤ nodes ∧ edgeRequests requests ≤ edges

private theorem budget_refl (state : Shared width) (nodes edges : Nat) : Budget state state nodes edges :=
  ⟨[], .refl _, Nat.zero_le _, Nat.zero_le _⟩

private theorem budget_next {before after : Shared width} {nodes edges : Nat}
    (budget : Budget before after nodes edges) :
    after.checked.native.machine.heap.nodes.next ≤ before.checked.native.machine.heap.nodes.next + nodes ∧
    after.checked.native.machine.heap.edges.next ≤ before.checked.native.machine.heap.edges.next + edges := by
  obtain ⟨requests, actual, nodeCount, edgeCount⟩ := budget
  have exactSupply := actual.next_le
  constructor <;> omega

private theorem budget_mono {before after : Shared width} {nodes edges largerNodes largerEdges : Nat}
    (budget : Budget before after nodes edges) (nodeBound : nodes ≤ largerNodes) (edgeBound : edges ≤ largerEdges) :
    Budget before after largerNodes largerEdges := by
  obtain ⟨requests, actual, nodeCount, edgeCount⟩ := budget
  exact ⟨requests, actual, Nat.le_trans nodeCount nodeBound, Nat.le_trans edgeCount edgeBound⟩

private theorem budget_trans {before middle after : Shared width} {firstNodes firstEdges lastNodes lastEdges nodes edges : Nat}
    (first : Budget before middle firstNodes firstEdges) (last : Budget middle after lastNodes lastEdges)
    (nodeBound : firstNodes + lastNodes ≤ nodes) (edgeBound : firstEdges + lastEdges ≤ edges) :
    Budget before after nodes edges := by
  obtain ⟨one, firstTrace, firstNodeCount, firstEdgeCount⟩ := first
  obtain ⟨two, lastTrace, lastNodeCount, lastEdgeCount⟩ := last
  refine ⟨one ++ two, firstTrace.trans lastTrace, ?_, ?_⟩
  · rw [nodeRequests_append]; omega
  · rw [edgeRequests_append]; omega

private theorem node_work (before : Shared width) (rows : List (EdgeValue Symbol Guard)) :
    Budget before (advanceHeap before (run (makeNode rows) before.checked.native.machine.heap).2) 1 0 := by
  refine ⟨observe (makeNode rows) before.checked.native.machine.heap, .work _ _, ?_, ?_⟩
  · have counts := (makeNode_requests rows before.checked.native.machine.heap).1
    split at counts <;> omega
  · exact Nat.le_of_eq (makeNode_requests rows before.checked.native.machine.heap).2

private theorem edge_work (before : Shared width) (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard)) :
    Budget before (advanceHeap before (run (makeEdge symbol guard values) before.checked.native.machine.heap).2) 0 1 := by
  refine ⟨observe (makeEdge symbol guard values) before.checked.native.machine.heap, .work _ _, ?_, ?_⟩
  · simp [makeEdge_observe, nodeRequests]
  · simp [makeEdge_observe, edgeRequests]

omit [DecidableEq (EdgeKey Symbol Guard)] in
private theorem heap_stored (before : Shared width) (heap : Heap) {rows arity bound : Nat}
    (stored : Stored rows arity bound before) : Stored rows arity bound (advanceHeap before heap) :=
  SourceCurrentAllocatedFiniteOrdinarySharedProfiles.physical_stored before ⟨heap, before.checked.operations⟩ stored

variable [DecidableEq Symbol]

section Construction
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
variable (bits : Nat) (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) (base : Heap)
variable (rows arity count depth bound inputRows inputArity inputBound : Nat)
local notation "TargetR" => SourceCurrentAllocatedFiniteOrdinarySharedForceResources.targetRows record rows count depth bound
local notation "OutR" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.outputRows record rows count depth bound inputRows
local notation "OutA" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.outputArity arity inputArity
local notation "LeafN" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.leafNodes record rows arity count depth bound inputRows inputArity inputBound
local notation "LeafE" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.leafEdges record rows arity count depth bound inputRows inputArity inputBound
local notation "NN" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.nodeNodes LeafN
local notation "NE" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.nodeEdges LeafE
local notation "CN" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.childrenNodes LeafN
local notation "CE" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.childrenEdges LeafE
local notation "RN" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.rowsNodes LeafN
local notation "RE" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.rowsEdges LeafE

private def NodeComplete (edits : Edits EqualityNormalize.Path) (value : Value Symbol Guard) : Prop :=
  ∀ (before : Shared (bits + 2)) (inventory : Inventory),
    Ready formulas solver inventory record originals base before → Stored TargetR (max arity 1) bound before →
    Available before.checked.native.machine.heap value → NodeShape inputRows inputArity value → height value ≤ inputBound →
    Populated edits → HasLeaf edits → Allowed record edits → Safe edits value →
    ∀ memos, Valid before.checked.native.machine.heap memos →
      before.checked.native.machine.heap.nodes.next + NN value ≤ 2 ^ bits →
      before.checked.native.machine.heap.edges.next + NE value ≤ 2 ^ (bits + 2) →
      ∃ result after final, ∃ actual : EditNode record originals edits value before result after,
        NodeReads formulas solver base actual memos final ∧ Stored TargetR (max arity 1) bound after ∧
        NodeShape OutR OutA result ∧ Budget before after (NN value) (NE value)

private def ChildrenComplete (entries : List (Int × Edits EqualityNormalize.Path)) (offset : Nat)
    (values : List (Value Symbol Guard)) : Prop :=
  ∀ (before : Shared (bits + 2)) (inventory : Inventory),
    Ready formulas solver inventory record originals base before → Stored TargetR (max arity 1) bound before →
    Values before.checked.native.machine.heap values → ChildrenShape inputRows inputArity values → childrenHeight values ≤ inputBound →
    Populated (.editBelow entries) → Allowed record (.editBelow entries) → ChildrenSafe entries offset values →
    ∀ memos, Valid before.checked.native.machine.heap memos →
      before.checked.native.machine.heap.nodes.next + CN values ≤ 2 ^ bits →
      before.checked.native.machine.heap.edges.next + CE values ≤ 2 ^ (bits + 2) →
      ∃ results after final, ∃ actual : EditChildren record originals entries offset values before results after,
        ChildrenReads formulas solver base actual memos final ∧ Stored TargetR (max arity 1) bound after ∧
        ChildrenShape OutR OutA results ∧ Budget before after (CN values) (CE values)

private def RowsComplete (entries : List (Int × Edits EqualityNormalize.Path)) (edges : List (EdgeValue Symbol Guard)) : Prop :=
  ∀ (before : Shared (bits + 2)) (inventory : Inventory),
    Ready formulas solver inventory record originals base before → Stored TargetR (max arity 1) bound before →
    Edges before.checked.native.machine.heap edges → RowsShape inputRows inputArity edges → edgesHeight edges ≤ inputBound →
    Populated (.editBelow entries) → Allowed record (.editBelow entries) → RowsSafe entries edges →
    ∀ memos, Valid before.checked.native.machine.heap memos →
      before.checked.native.machine.heap.nodes.next + RN edges ≤ 2 ^ bits →
      before.checked.native.machine.heap.edges.next + RE edges ≤ 2 ^ (bits + 2) →
      ∃ results after final, ∃ actual : EditRows record originals entries edges before results after,
        RowsReads formulas solver base actual memos final ∧ Stored TargetR (max arity 1) bound after ∧
        RowsShape OutR OutA results ∧ Budget before after (RN edges) (RE edges)

local notation "NodeLaw" => NodeComplete formulas solver bits record originals base rows arity count depth bound inputRows inputArity inputBound
local notation "ChildrenLaw" => ChildrenComplete formulas solver bits record originals base rows arity count depth bound inputRows inputArity inputBound
local notation "RowsLaw" => RowsComplete formulas solver bits record originals base rows arity count depth bound inputRows inputArity inputBound
variable (known : Values base originals) (coherent : SourceEqualityClassOrder.Coherent record)
variable (active : EqualityNormalize.Nontrivial record.paths) (captured : ChildrenShape rows arity originals)
variable (lengthBound : originals.length ≤ count) (pathsBound : ∀ path ∈ record.paths, path.length ≤ depth)
variable (capturedHeight : childrenHeight originals ≤ bound)
include known coherent active captured lengthBound pathsBound capturedHeight

set_option maxHeartbeats 2400000 in
private theorem complete (limit : Nat) :
    (∀ edits (value : Value Symbol Guard), sizeOf value ≤ limit → NodeLaw edits value) ∧
    (∀ entries offset (values : List (Value Symbol Guard)), sizeOf values ≤ limit → ChildrenLaw entries offset values) ∧
    (∀ entries (edges : List (EdgeValue Symbol Guard)), sizeOf edges ≤ limit → RowsLaw entries edges) := by
  induction limit using Nat.strongRecOn with
  | ind limit ih =>
    refine ⟨?_, ?_, ?_⟩
    · intro edits value sizeBound before inventory ready stored available profile heightBound populated nonempty allowed safe memos valid nodes edges
      cases edits with
      | editAt path =>
          have member : path ∈ record.paths := by simpa only [Allowed, All] using allowed
          have nodeCost := SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.leaf_nodes_bound record rows arity count depth bound inputRows inputArity inputBound before path
          have edgeCost := SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.leaf_edges_bound record rows arity count depth bound inputRows inputArity inputBound before path
          have positive := SourceCurrentAllocatedFiniteOrdinaryValuePositions.node_pos value
          have enoughNodes : LeafN ≤ NN value := by
            unfold SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.nodeNodes
            exact Nat.le_trans (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right LeafN positive) (Nat.le_add_right _ _)
          have enoughEdges : LeafE ≤ NE value := by
            unfold SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.nodeEdges
            exact Nat.le_trans (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right LeafE positive) (Nat.le_add_right _ _)
          obtain ⟨result, after, _next, final, requests, receipt, retained, produced, _narrow, _height,
            trace, nodeCount, edgeCount, _capacity, _nodeSupply, _edgeSupply⟩ :=
            SourceCurrentAllocatedFiniteOrdinarySharedLeafResources.complete formulas solver inventory bits record originals base before
              ready known coherent active path member rows arity count depth bound captured lengthBound pathsBound capturedHeight stored
              value inputRows inputArity inputBound available profile heightBound (by omega) (by omega) memos valid
          exact ⟨result, after, final, .leaf receipt.actual, .leaf receipt, retained, produced,
            requests, trace, by omega, by omega⟩
      | editBelow entries =>
          cases value with
          | empty => exact ⟨.empty, before, memos, .empty, .empty, stored, trivial, budget_refl _ _ _⟩
          | reference | mu | union => cases profile
          | node entry originalRows cachedDepth free =>
              have smaller : sizeOf originalRows < limit := by
                simp only [Value.node.sizeOf_spec] at sizeBound
                omega
              have ordinaryCosts := SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.node_ordinary LeafN LeafE entry originalRows cachedDepth free
              have facts := ready.checked.semantic.ready.semantic.1.normal.facts
              have resident := InternedEdgeResidency.resident_edges _ facts.linked _ available.resident
              obtain ⟨rebuilt, middle, final, actualRows, rowReads, middleStored, rowProfile, rowBudget⟩ :=
                (ih (sizeOf originalRows) smaller).2.2 entries originalRows (Nat.le_refl _) before inventory ready stored resident profile.2
                  (by change edgesHeight originalRows + 1 ≤ inputBound at heightBound; omega) populated allowed (ordinary_rows safe)
                  memos valid (by omega) (by omega)
              obtain ⟨next, receipt⟩ := SourceCurrentAllocatedSharedEditEffects.rows_effects rowReads populated allowed ready resident (ordinary_rows safe) valid
              have currentFacts := receipt.ready.checked.semantic.ready.semantic.1.normal.facts
              have made := SourceCurrentAllocatedFiniteOrdinaryOutputConstructors.makeNode rebuilt middle.checked.native.machine.heap
                currentFacts.coherent currentFacts.linked receipt.available rowProfile
                (Nat.le_trans (by rw [receipt.transport.length_eq.symm]; exact profile.1)
                  (SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.input_rows_le_outputRows record rows count depth bound inputRows))
              exact ⟨_, _, final, .ordinary actualRows rfl, .ordinary (actual := actualRows) (built := rfl) rowReads,
                heap_stored middle _ middleStored, made,
                budget_trans rowBudget (node_work middle rebuilt) (by omega) (by omega)⟩
    · intro entries offset values sizeBound before inventory ready stored available profile heightBound populated allowed safe memos valid nodes edges
      cases values with
      | nil => exact ⟨[], before, memos, .nil, .nil, stored, trivial, budget_refl _ _ _⟩
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
              obtain ⟨results, after, final, actual, reads, finalStored, tailProfile, tailBudget⟩ :=
                (ih (sizeOf values) restSmaller).2.1 entries (offset + 1) values (Nat.le_refl _) before inventory ready stored
                  tailAvailable profile.2 restHeight populated allowed (children_tail safe) memos valid (by omega) (by omega)
              have originalProfile := NodeShape.mono value profile.1
                (SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.input_rows_le_outputRows record rows count depth bound inputRows)
                (SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.input_arity_le_outputArity arity inputArity)
              exact ⟨value :: results, after, final, .unselected offset found actual,
                .unselected (absent := found) (rest := actual) reads, finalStored, ⟨originalProfile, tailProfile⟩,
                budget_mono tailBudget (by omega) (by omega)⟩
          | some edits =>
              have member := SourceEqualityNeededMap.lookup_mem _ _ _ found
              have childPopulated := (show ∀ index child, (index, child) ∈ entries → Populated child ∧ HasLeaf child from
                by simpa only [Populated] using populated) _ _ member
              have childAllowed : Allowed record edits := by rw [Allowed, All] at allowed; exact allowed _ _ member
              have firstSafe := safe 0 _ (by simpa using found) value rfl
              obtain ⟨result, middle, current, first, firstReads, middleStored, firstProfile, firstBudget⟩ :=
                (ih (sizeOf value) firstSmaller).1 edits value (Nat.le_refl _) before inventory ready stored
                  (available _ List.mem_cons_self) profile.1 childHeight childPopulated.1 childPopulated.2 childAllowed firstSafe
                  memos valid (by omega) (by omega)
              obtain ⟨next, receipt⟩ := SourceCurrentAllocatedSharedEditEffects.node_effects firstReads childPopulated.1 childPopulated.2 childAllowed ready
                (available _ List.mem_cons_self) firstSafe valid
              have firstSupply := budget_next firstBudget
              obtain ⟨results, after, final, rest, restReads, finalStored, tailProfile, tailBudget⟩ :=
                (ih (sizeOf values) restSmaller).2.1 entries (offset + 1) values (Nat.le_refl _) middle next receipt.ready middleStored
                  (fun child member => receipt.effects.keeps.available child (tailAvailable child member)) profile.2 restHeight
                  populated allowed (children_tail safe) current receipt.globals.valid (by omega) (by omega)
              exact ⟨result :: results, after, final, .selected offset found first rest,
                .selected (found := found) (first := first) (rest := rest) firstReads restReads,
                finalStored, ⟨firstProfile, tailProfile⟩, budget_trans firstBudget tailBudget (by omega) (by omega)⟩
    · intro entries originalRows sizeBound before inventory ready stored resident profile heightBound populated allowed safe memos valid nodes edges
      cases originalRows with
      | nil => exact ⟨[], before, memos, .nil, .nil, stored, trivial, budget_refl _ _ _⟩
      | cons edge originalRows =>
          have childrenSmaller : sizeOf edge.children < limit := by
            cases edge with
            | mk entry values => simp only [List.cons.sizeOf_spec, EdgeValue.mk.sizeOf_spec, EdgeValue.children] at *; omega
          have restSmaller : sizeOf originalRows < limit := by simp only [List.cons.sizeOf_spec] at sizeBound; omega
          have costs := SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.rows_cons LeafN LeafE edge originalRows
          have facts := ready.checked.semantic.ready.semantic.1.normal.facts
          have original := resident edge List.mem_cons_self
          have available := facts.cached.edges edge.entry.key edge original
          have childHeight : childrenHeight edge.children ≤ inputBound := by
            have firstHeight := Nat.le_trans (Nat.le_max_left _ _) heightBound
            cases edge with
            | mk entry values => exact firstHeight
          obtain ⟨values, middle, current, children, childrenReads, middleStored, childrenProfile, childBudget⟩ :=
            (ih (sizeOf edge.children) childrenSmaller).2.1 entries 0 edge.children (Nat.le_refl _) before inventory ready stored
              available (SourceCurrentAllocatedFiniteOrdinaryNativeProfile.EdgeShape.children edge profile.1) childHeight populated allowed (safe _ List.mem_cons_self) memos valid (by omega) (by omega)
          obtain ⟨next, receipt⟩ := SourceCurrentAllocatedSharedEditEffects.children_effects childrenReads populated allowed ready available (safe _ List.mem_cons_self) valid
          have field := (ready.checked.good.fields edge.entry.key edge original).grows receipt.effects.grows
          have built := SourceCurrentAllocatedSharedEditEffects.edge_physical receipt.ready edge.entry.key.symbol edge.entry.key.constraint values field receipt.available
          have currentFacts := receipt.ready.checked.semantic.ready.semantic.1.normal.facts
          have made := SourceCurrentAllocatedFiniteOrdinaryOutputConstructors.makeEdge edge.entry.key.symbol edge.entry.key.constraint values middle.checked.native.machine.heap
            currentFacts.coherent currentFacts.cached receipt.available childrenProfile
            (Nat.le_trans (by rw [children_length children]; exact SourceCurrentAllocatedFiniteOrdinaryNativeProfile.EdgeShape.arity edge profile.1)
              (SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.input_arity_le_outputArity arity inputArity))
          have prefixBudget := budget_trans childBudget (edge_work middle edge.entry.key.symbol edge.entry.key.constraint values)
            (nodes := CN edge.children) (edges := CE edge.children + 1) (by omega) (by omega)
          have prefixSupply := budget_next prefixBudget
          have globalValid := SourceQueryUnfoldMemo.valid_grows middle.checked.native.machine.heap _ receipt.ready.checked.semantic
            built.2.1.keeps current receipt.globals.valid
          have kept := receipt.effects.keeps.trans built.2.1.keeps
          obtain ⟨results, after, final, rest, restReads, finalStored, tailProfile, tailBudget⟩ :=
            (ih (sizeOf originalRows) restSmaller).2.2 entries originalRows (Nat.le_refl _) _ next built.1
              (heap_stored middle _ middleStored)
              (fun original member => InternedEdgeResidency.edge_grows _ _ kept.growth original (resident original (List.mem_cons_of_mem _ member)))
              profile.2 (Nat.le_trans (Nat.le_max_right _ _) heightBound) populated allowed
              (fun original member => safe original (List.mem_cons_of_mem _ member)) current globalValid (by omega) (by omega)
          exact ⟨_ :: results, after, final, .cons children rfl rest,
            .cons (children := children) (rebuilt := rfl) (rest := rest) childrenReads restReads,
            finalStored, ⟨made, tailProfile⟩, budget_trans prefixBudget tailBudget (by omega) (by omega)⟩

/-- Initial literal-input budgets construct the complete node edit and its actual worker return. -/
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
    ∃ result after next final requests, ∃ actual : EditNode record originals edits value before result after,
      NodeReads formulas solver base actual memos final ∧
      SourceCurrentAllocatedSharedEditEffects.NodeReceipt formulas solver next record originals base value before result after memos final ∧
      Stored TargetR (max arity 1) bound after ∧ NodeShape OutR OutA result ∧
      SourceCurrentAllocatedFiniteOrdinaryRequired.NodeNarrow value result ∧ height result ≤ inputBound ∧
      SourceCurrentAllocatedSharedEditWorkerCompletion.StableRun
        (fun e p h m s n => SourceCurrentAllocatedSharedEditWorker.edit record originals e p h m s n edits value before) result after ∧
      Trace before.checked.native.machine.heap after.checked.native.machine.heap requests ∧
      nodeRequests requests ≤ NN value ∧ edgeRequests requests ≤ NE value ∧
      SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity bits after.checked ∧
      after.checked.native.machine.heap.nodes.next ≤ before.checked.native.machine.heap.nodes.next + NN value ∧
      after.checked.native.machine.heap.edges.next ≤ before.checked.native.machine.heap.edges.next + NE value := by
  obtain ⟨result, after, final, actual, reads, finalStored, produced, requests, trace, nodeCount, edgeCount⟩ :=
    (complete formulas solver bits record originals base rows arity count depth bound inputRows inputArity inputBound
      known coherent active captured lengthBound pathsBound capturedHeight (sizeOf value)).1 edits value (Nat.le_refl _)
      before inventory ready stored available profile heightBound populated nonempty allowed safe memos valid nodes edges
  obtain ⟨next, receipt⟩ := SourceCurrentAllocatedSharedEditEffects.node_effects reads populated nonempty allowed ready available safe valid
  have narrowed := (SourceCurrentAllocatedFiniteOrdinaryEdits.node reads populated nonempty allowed ready available safe valid
    known (ChildrenShape.domain originals captured) stored.domain (NodeShape.domain value profile)).2
  have supply := trace.next_le
  exact ⟨result, after, next, final, requests, actual, reads, receipt, finalStored, produced, narrowed,
    Nat.le_trans narrowed.2 heightBound, SourceCurrentAllocatedSharedEditWorkerCompletion.node_complete actual,
    trace, nodeCount, edgeCount, ⟨by omega, by omega⟩, by omega, by omega⟩

/-- Initial cumulative budgets construct the ordered child scan and its retained positional receipt. -/
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
    ∃ results after next final requests, ∃ actual : EditChildren record originals entries offset values before results after,
      ChildrenReads formulas solver base actual memos final ∧
      SourceCurrentAllocatedSharedEditEffects.ChildrenReceipt formulas solver next record originals base values before results after memos final ∧
      Stored TargetR (max arity 1) bound after ∧ ChildrenShape OutR OutA results ∧
      All₂ SourceCurrentAllocatedFiniteOrdinaryRequired.NodeNarrow values results ∧ results.length = values.length ∧
      SourceCurrentAllocatedSharedEditWorkerCompletion.StableRun
        (fun e p h m s n => SourceCurrentAllocatedSharedEditWorker.children
          (SourceCurrentAllocatedSharedEditWorker.edit record originals e p h m s n) entries offset values before) results after ∧
      Trace before.checked.native.machine.heap after.checked.native.machine.heap requests ∧
      nodeRequests requests ≤ CN values ∧ edgeRequests requests ≤ CE values ∧
      SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity bits after.checked ∧
      after.checked.native.machine.heap.nodes.next ≤ before.checked.native.machine.heap.nodes.next + CN values ∧
      after.checked.native.machine.heap.edges.next ≤ before.checked.native.machine.heap.edges.next + CE values := by
  obtain ⟨results, after, final, actual, reads, finalStored, produced, requests, trace, nodeCount, edgeCount⟩ :=
    (complete formulas solver bits record originals base rows arity count depth bound inputRows inputArity inputBound
      known coherent active captured lengthBound pathsBound capturedHeight (sizeOf values)).2.1 entries offset values (Nat.le_refl _)
      before inventory ready stored available profile heightBound populated allowed safe memos valid nodes edges
  obtain ⟨next, receipt⟩ := SourceCurrentAllocatedSharedEditEffects.children_effects reads populated allowed ready available safe valid
  have narrowed := (SourceCurrentAllocatedFiniteOrdinaryEdits.children reads populated allowed ready available safe valid
    known (ChildrenShape.domain originals captured) stored.domain (ChildrenShape.domain values profile)).2
  have supply := trace.next_le
  exact ⟨results, after, next, final, requests, actual, reads, receipt, finalStored, produced, narrowed, children_length actual,
    SourceCurrentAllocatedSharedEditWorkerCompletion.children_complete actual,
    trace, nodeCount, edgeCount, ⟨by omega, by omega⟩, by omega, by omega⟩

/-- Initial cumulative budgets construct all raw rows with their original guards and returned heaps. -/
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
    ∃ results after next final requests, ∃ actual : EditRows record originals entries originalRows before results after,
      RowsReads formulas solver base actual memos final ∧
      SourceCurrentAllocatedSharedEditEffects.RowsReceipt formulas solver next record originals base originalRows before results after memos final ∧
      Stored TargetR (max arity 1) bound after ∧ RowsShape OutR OutA results ∧
      All₂ SourceCurrentAllocatedFiniteOrdinaryRequired.EdgeNarrow originalRows results ∧ results.length = originalRows.length ∧
      SourceCurrentAllocatedSharedEditWorkerCompletion.StableRun
        (fun e p h m s n => SourceCurrentAllocatedSharedEditWorker.rows
          (SourceCurrentAllocatedSharedEditWorker.edit record originals e p h m s n) entries originalRows before) results after ∧
      Trace before.checked.native.machine.heap after.checked.native.machine.heap requests ∧
      nodeRequests requests ≤ RN originalRows ∧ edgeRequests requests ≤ RE originalRows ∧
      SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity bits after.checked ∧
      after.checked.native.machine.heap.nodes.next ≤ before.checked.native.machine.heap.nodes.next + RN originalRows ∧
      after.checked.native.machine.heap.edges.next ≤ before.checked.native.machine.heap.edges.next + RE originalRows := by
  obtain ⟨results, after, final, actual, reads, finalStored, produced, requests, trace, nodeCount, edgeCount⟩ :=
    (complete formulas solver bits record originals base rows arity count depth bound inputRows inputArity inputBound
      known coherent active captured lengthBound pathsBound capturedHeight (sizeOf originalRows)).2.2 entries originalRows (Nat.le_refl _)
      before inventory ready stored resident profile heightBound populated allowed safe memos valid nodes edges
  obtain ⟨next, receipt⟩ := SourceCurrentAllocatedSharedEditEffects.rows_effects reads populated allowed ready resident safe valid
  have narrowed := (SourceCurrentAllocatedFiniteOrdinaryEdits.rows reads populated allowed ready resident safe valid
    known (ChildrenShape.domain originals captured) stored.domain (RowsShape.domain originalRows profile)).2
  have supply := trace.next_le
  exact ⟨results, after, next, final, requests, actual, reads, receipt, finalStored, produced, narrowed, receipt.transport.length_eq.symm,
    SourceCurrentAllocatedSharedEditWorkerCompletion.rows_complete actual,
    trace, nodeCount, edgeCount, ⟨by omega, by omega⟩, by omega, by omega⟩

end Construction
end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEditResources
