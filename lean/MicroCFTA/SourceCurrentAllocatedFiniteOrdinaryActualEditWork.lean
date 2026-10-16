import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryActualSharedWork
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEditShapes
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputConstructors
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEdits

/-!
# Constructor Work through supplied actual simultaneous edit reads

Each callback uses its original immutable input position.
The actual prefix produces the next Ready state and warm profile stores.
Constructor requests compose in literal child and row order.
No headroom, capacity, or future callback budget is a premise.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryActualEditWork
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityEdits SourceEqualityEditLeafPaths
open SourceEqualitySharedEditEffects (Allowed)
open SourceEqualityRequiredCache (Keeps)
open SourceCurrentEditDomains
open SourceCurrentAllocatedSharedEditGraph
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow EdgeNarrow)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace nodeRequests_append edgeRequests_append)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests observe makeNode_requests makeEdge_observe)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "HeapState" => InternedConstructorTemplates.State Symbol Guard
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "GlobalEffect" => SourceCurrentSubsumesQueryMemos.Effect
local notation "SharedStored" => SourceCurrentAllocatedFiniteOrdinaryShared.Stored
local notation "Stored" => SourceCurrentAllocatedFiniteOrdinarySharedProfiles.Stored
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape ChildrenShape RowsShape)
local notation "TargetRows" => SourceCurrentAllocatedFiniteOrdinarySharedForceResources.targetRows
local notation "OutRows" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.outputRows
local notation "OutArity" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.outputArity
local notation "LeafN" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.leafNodes
local notation "LeafE" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.leafEdges
local notation "NN" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.nodeNodes
local notation "NE" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.nodeEdges
local notation "CN" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.childrenNodes
local notation "CE" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.childrenEdges
local notation "RN" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.rowsNodes
local notation "RE" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.rowsEdges
open MergedOrdinaryHeight (height edgeHeight edgesHeight childrenHeight)
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula} {base : HeapState}

private def Budget (before after : SharedState width) (nodes edges : Nat) : Prop :=
  ∃ requests, Trace before.checked.native.machine.heap after.checked.native.machine.heap requests ∧
    nodeRequests requests ≤ nodes ∧ edgeRequests requests ≤ edges

omit [DecidableEq Symbol] in
private theorem budget_refl (state : SharedState width) (nodes edges : Nat) : Budget state state nodes edges :=
  ⟨[], .refl _, Nat.zero_le _, Nat.zero_le _⟩

omit [DecidableEq Symbol] in
private theorem budget_mono {before after : SharedState width} {nodes edges largerNodes largerEdges : Nat}
    (budget : Budget before after nodes edges) (nodeBound : nodes ≤ largerNodes) (edgeBound : edges ≤ largerEdges) :
    Budget before after largerNodes largerEdges := by
  obtain ⟨requests, actual, nodeCount, edgeCount⟩ := budget
  exact ⟨requests, actual, Nat.le_trans nodeCount nodeBound, Nat.le_trans edgeCount edgeBound⟩

omit [DecidableEq Symbol] in
private theorem budget_trans {before middle after : SharedState width} {firstNodes firstEdges lastNodes lastEdges nodes edges : Nat}
    (first : Budget before middle firstNodes firstEdges) (last : Budget middle after lastNodes lastEdges)
    (nodeBound : firstNodes + lastNodes ≤ nodes) (edgeBound : firstEdges + lastEdges ≤ edges) :
    Budget before after nodes edges := by
  obtain ⟨one, firstTrace, firstNodeCount, firstEdgeCount⟩ := first
  obtain ⟨two, lastTrace, lastNodeCount, lastEdgeCount⟩ := last
  refine ⟨one ++ two, firstTrace.trans lastTrace, ?_, ?_⟩
  · rw [nodeRequests_append]; omega
  · rw [edgeRequests_append]; omega

omit [DecidableEq Symbol] in
private theorem node_work (before : SharedState width) (rows : List (EdgeValue Symbol Guard)) :
    Budget before (advanceHeap before (run (makeNode rows) before.checked.native.machine.heap).2) 1 0 := by
  refine ⟨observe (makeNode rows) before.checked.native.machine.heap, .work _ _, ?_, ?_⟩
  · have counts := (makeNode_requests rows before.checked.native.machine.heap).1
    split at counts <;> omega
  · exact Nat.le_of_eq (makeNode_requests rows before.checked.native.machine.heap).2

omit [DecidableEq Symbol] in
private theorem edge_work (before : SharedState width) (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard)) :
    Budget before (advanceHeap before (run (makeEdge symbol guard values) before.checked.native.machine.heap).2) 0 1 := by
  refine ⟨observe (makeEdge symbol guard values) before.checked.native.machine.heap, .work _ _, ?_, ?_⟩
  · simp [makeEdge_observe, nodeRequests]
  · simp [makeEdge_observe, edgeRequests]

private def NodeLaw (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
    (edits : Edits EqualityNormalize.Path) (input : Value Symbol Guard) (before : SharedState width)
    (_result : Value Symbol Guard) (after : SharedState width) (memos _final : Memos) : Prop :=
  ∀ inventory, Populated edits → HasLeaf edits → Allowed record edits →
    Ready formulas solver inventory record originals base before → Available before.checked.native.machine.heap input →
    Safe edits input → Valid before.checked.native.machine.heap memos → Values base originals →
    SourceEqualityClassOrder.Coherent record → ∀ rows arity count depth bound inputRows inputArity inputBound,
      ChildrenShape rows arity originals → originals.length ≤ count →
      (∀ path ∈ record.paths, path.length ≤ depth) → childrenHeight originals ≤ bound →
      Stored (TargetRows record rows count depth bound) (max arity 1) bound before →
      NodeShape inputRows inputArity input → height input ≤ inputBound →
      Stored (TargetRows record rows count depth bound) (max arity 1) bound after ∧
      Budget before after (NN (LeafN record rows arity count depth bound inputRows inputArity inputBound) input) (NE (LeafE record rows arity count depth bound inputRows inputArity inputBound) input)

private def ChildrenLaw (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
    (entries : List (Int × Edits EqualityNormalize.Path)) (offset : Nat) (inputs : List (Value Symbol Guard))
    (before : SharedState width) (_results : List (Value Symbol Guard)) (after : SharedState width) (memos _final : Memos) : Prop :=
  ∀ inventory, Populated (.editBelow entries) → Allowed record (.editBelow entries) →
    Ready formulas solver inventory record originals base before → Values before.checked.native.machine.heap inputs →
    ChildrenSafe entries offset inputs → Valid before.checked.native.machine.heap memos → Values base originals →
    SourceEqualityClassOrder.Coherent record → ∀ rows arity count depth bound inputRows inputArity inputBound,
      ChildrenShape rows arity originals → originals.length ≤ count →
      (∀ path ∈ record.paths, path.length ≤ depth) → childrenHeight originals ≤ bound →
      Stored (TargetRows record rows count depth bound) (max arity 1) bound before →
      ChildrenShape inputRows inputArity inputs → childrenHeight inputs ≤ inputBound →
      Stored (TargetRows record rows count depth bound) (max arity 1) bound after ∧
      Budget before after (CN (LeafN record rows arity count depth bound inputRows inputArity inputBound) inputs) (CE (LeafE record rows arity count depth bound inputRows inputArity inputBound) inputs)

private def RowsLaw (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
    (entries : List (Int × Edits EqualityNormalize.Path)) (inputs : List (EdgeValue Symbol Guard))
    (before : SharedState width) (_results : List (EdgeValue Symbol Guard)) (after : SharedState width) (memos _final : Memos) : Prop :=
  ∀ inventory, Populated (.editBelow entries) → Allowed record (.editBelow entries) →
    Ready formulas solver inventory record originals base before → Edges before.checked.native.machine.heap inputs →
    RowsSafe entries inputs → Valid before.checked.native.machine.heap memos → Values base originals →
    SourceEqualityClassOrder.Coherent record → ∀ rows arity count depth bound inputRows inputArity inputBound,
      ChildrenShape rows arity originals → originals.length ≤ count →
      (∀ path ∈ record.paths, path.length ≤ depth) → childrenHeight originals ≤ bound →
      Stored (TargetRows record rows count depth bound) (max arity 1) bound before →
      RowsShape inputRows inputArity inputs → edgesHeight inputs ≤ inputBound →
      Stored (TargetRows record rows count depth bound) (max arity 1) bound after ∧
      Budget before after (RN (LeafN record rows arity count depth bound inputRows inputArity inputBound) inputs) (RE (LeafE record rows arity count depth bound inputRows inputArity inputBound) inputs)

set_option maxHeartbeats 1600000 in
private theorem retained :
    (∀ {record originals edits value before result after} {memos final : Memos}
      {actual : EditNode (width := width) record originals edits value before result after},
      NodeReads formulas solver base actual memos final →
        NodeLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals edits value before result after memos final) ∧
    (∀ {record originals entries offset values before results after} {memos final : Memos}
      {actual : EditChildren (width := width) record originals entries offset values before results after},
      ChildrenReads formulas solver base actual memos final →
        ChildrenLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries offset values before results after memos final) ∧
    (∀ {record originals entries edges before results after} {memos final : Memos}
      {actual : EditRows (width := width) record originals entries edges before results after},
      RowsReads formulas solver base actual memos final →
        RowsLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries edges before results after memos final) := by
  have leafCase : ∀ {next record originals path value before result after memos saved},
      SourceCurrentAllocatedSharedTargetLeaf.Receipt formulas solver next record originals base path value before result after memos saved →
      NodeLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals (.editAt path) value before result after memos saved := by
    intro next record originals path value before result after memos saved receipt inventory _ _ allowed ready _ _ _ known coherent
      rows arity count depth bound inputRows inputArity inputBound captured lengthBound pathsBound capturedHeight stored profile inputHeight
    have member : path ∈ record.paths := by simpa only [Allowed, All] using allowed
    have checked := SourceCurrentAllocatedFiniteOrdinaryActualSharedWork.leaf_receipt receipt ready known coherent member
      rows arity count depth bound stored captured lengthBound pathsBound capturedHeight inputRows inputArity inputBound profile inputHeight
    obtain ⟨requests, work, nodes, edges⟩ := checked.2.2.2.2
    have nodeCost := SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.leaf_nodes_bound record rows arity count depth bound inputRows inputArity inputBound before path
    have edgeCost := SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.leaf_edges_bound record rows arity count depth bound inputRows inputArity inputBound before path
    have positive := SourceCurrentAllocatedFiniteOrdinaryValuePositions.node_pos value
    refine ⟨checked.1, requests, work, ?_, ?_⟩
    · unfold SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.nodeNodes
      have paid := Nat.mul_le_mul_right (LeafN record rows arity count depth bound inputRows inputArity inputBound) positive
      omega
    · unfold SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.nodeEdges
      have paid := Nat.mul_le_mul_right (LeafE record rows arity count depth bound inputRows inputArity inputBound) positive
      omega
  have emptyCase : ∀ {record originals entries state memos},
      NodeLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals
        (.editBelow entries) (.empty : Value Symbol Guard) state .empty state memos memos := by
    intro record originals entries state memos inventory _ _ _ _ _ _ _ _ _
      rows arity count depth bound inputRows inputArity inputBound captured lengthBound pathsBound capturedHeight stored profile inputHeight
    exact ⟨stored, budget_refl _ _ _⟩
  have ordinaryCase : ∀ {record originals memos saved entries edges before rebuilt middle value heap entry depth free}
      {actual : EditRows record originals entries edges before rebuilt middle}
      {built : run (makeNode rebuilt) middle.checked.native.machine.heap = (value, heap)},
      RowsReads formulas solver base actual memos saved →
      RowsLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries edges before rebuilt middle memos saved →
      NodeLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals
        (.editBelow entries) (.node entry edges depth free) before value (advanceHeap middle heap) memos saved := by
    intro record originals memos saved entries edges before rebuilt middle value heap entry cachedDepth free actual built reads ih
      inventory populated _ allowed ready available safe valid known coherent
      rows arity count depth bound inputRows inputArity inputBound captured lengthBound pathsBound capturedHeight stored profile inputHeight
    have facts := ready.checked.semantic.ready.semantic.1.normal.facts
    have resident := InternedEdgeResidency.resident_edges _ facts.linked _ available.resident
    have related := ih inventory populated allowed ready resident (ordinary_rows safe) valid known coherent
      rows arity count depth bound inputRows inputArity inputBound captured lengthBound pathsBound capturedHeight stored profile.2
      (by change edgesHeight edges + 1 ≤ inputBound at inputHeight; omega)
    obtain ⟨next, checked⟩ := SourceCurrentAllocatedSharedEditEffects.rows_effects reads populated allowed ready
      resident (ordinary_rows safe) valid
    have costs := SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.node_ordinary
      (LeafN record rows arity count depth bound inputRows inputArity inputBound)
      (LeafE record rows arity count depth bound inputRows inputArity inputBound) entry edges cachedDepth free
    have work : Budget middle (advanceHeap middle heap) 1 0 := by simpa only [built] using node_work middle rebuilt
    exact ⟨SourceCurrentAllocatedFiniteOrdinarySharedProfiles.physical_stored middle ⟨heap, middle.checked.operations⟩ related.1,
      budget_trans related.2 work (by omega) (by omega)⟩
  have recursiveCase : ∀ {record originals memos current saved entries original before exposed heap value after}
      {recursive : SourceEqualityRequiredGraph.Recursive original}
      {head : SourceEqualityRequiredHead.Head original before.checked.native.machine.heap exposed heap}
      {body : EditNode record originals (.editBelow entries) exposed (advanceHeap before heap) value after},
      SourceCurrentRequiredQueryMemos.HeadReads head memos current →
      GlobalEffect before.checked.native.machine.heap heap memos current →
      NodeReads formulas solver base body current saved →
      NodeLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals
        (.editBelow entries) exposed (advanceHeap before heap) value after current saved →
      NodeLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals
        (.editBelow entries) original before value after memos saved := by
    intro record originals memos current saved entries original before exposed heap value after recursive head body
      _ _ _ _ inventory _ _ _ _ _ _ _ _ _ rows arity count depth bound inputRows inputArity inputBound
      captured lengthBound pathsBound capturedHeight stored profile inputHeight
    cases (SourceCurrentAllocatedFiniteOrdinaryNativeProfile.NodeShape.domain _ profile) <;> cases recursive
  have nilChildren : ∀ {record originals entries offset state memos},
      ChildrenLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries offset
        ([] : List (Value Symbol Guard)) state [] state memos memos := by
    intro record originals entries offset state memos inventory _ _ _ _ _ _ _ _
      rows arity count depth bound inputRows inputArity inputBound captured lengthBound pathsBound capturedHeight stored profile inputHeight
    exact ⟨stored, budget_refl _ _ _⟩
  have unselectedCase : ∀ {record originals memos saved entries values before results after value} {offset : Nat}
      {absent : SourceEqualityNeededMap.lookup (offset : Int) entries = none}
      {rest : EditChildren record originals entries (offset + 1) values before results after},
      ChildrenReads formulas solver base rest memos saved →
      ChildrenLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries (offset + 1) values before results after memos saved →
      ChildrenLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries offset (value :: values) before (value :: results) after memos saved := by
    intro record originals memos saved entries values before results after value offset absent rest reads ih
      inventory populated allowed ready available safe valid known coherent
      rows arity count depth bound inputRows inputArity inputBound captured lengthBound pathsBound capturedHeight stored profile inputHeight
    have later := ih inventory populated allowed ready
      (fun original member => available original (List.mem_cons_of_mem _ member)) (children_tail safe) valid known coherent
      rows arity count depth bound inputRows inputArity inputBound captured lengthBound pathsBound capturedHeight stored profile.2
      (Nat.le_trans (Nat.le_max_right _ _) inputHeight)
    have costs := SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.children_cons
      (LeafN record rows arity count depth bound inputRows inputArity inputBound)
      (LeafE record rows arity count depth bound inputRows inputArity inputBound) value values
    exact ⟨later.1, budget_mono later.2 (by omega) (by omega)⟩
  have selectedCase : ∀ {record originals memos current saved entries edits value before result middle values results after} {offset : Nat}
      {found : SourceEqualityNeededMap.lookup (offset : Int) entries = some edits}
      {first : EditNode record originals edits value before result middle}
      {rest : EditChildren record originals entries (offset + 1) values middle results after},
      NodeReads formulas solver base first memos current → ChildrenReads formulas solver base rest current saved →
      NodeLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals edits value before result middle memos current →
      ChildrenLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries (offset + 1) values middle results after current saved →
      ChildrenLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries offset (value :: values) before (result :: results) after memos saved := by
    intro record originals memos current saved entries edits value before result middle values results after offset found first rest
      firstReads restReads firstIH restIH inventory populated allowed ready available safe valid known coherent
      rows arity count depth bound inputRows inputArity inputBound captured lengthBound pathsBound capturedHeight stored profile inputHeight
    have member := SourceEqualityNeededMap.lookup_mem _ _ _ found
    have children := (show ∀ index child, (index, child) ∈ entries → Populated child ∧ HasLeaf child from
      by simpa only [Populated] using populated)
    have childAllowed : Allowed record edits := by
      rw [Allowed, All] at allowed
      exact allowed _ _ member
    have firstSafe := safe 0 _ (by simpa using found) value rfl
    have firstProfiles := firstIH inventory (children _ _ member).1 (children _ _ member).2 childAllowed
      ready (available _ List.mem_cons_self) firstSafe valid known coherent
      rows arity count depth bound inputRows inputArity inputBound captured lengthBound pathsBound capturedHeight stored profile.1
      (Nat.le_trans (Nat.le_max_left _ _) inputHeight)
    obtain ⟨middleInventory, checked⟩ := SourceCurrentAllocatedSharedEditEffects.node_effects firstReads
      (children _ _ member).1 (children _ _ member).2 childAllowed ready (available _ List.mem_cons_self) firstSafe valid
    have later := restIH middleInventory populated allowed checked.ready
      (fun original member => checked.effects.keeps.available original (available original (List.mem_cons_of_mem _ member)))
      (children_tail safe) checked.globals.valid known coherent
      rows arity count depth bound inputRows inputArity inputBound captured lengthBound pathsBound capturedHeight firstProfiles.1 profile.2
      (Nat.le_trans (Nat.le_max_right _ _) inputHeight)
    have costs := SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.children_cons
      (LeafN record rows arity count depth bound inputRows inputArity inputBound)
      (LeafE record rows arity count depth bound inputRows inputArity inputBound) value values
    exact ⟨later.1, budget_trans firstProfiles.2 later.2 (by omega) (by omega)⟩
  have nilRows : ∀ {record originals entries state memos},
      RowsLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries
        ([] : List (EdgeValue Symbol Guard)) state [] state memos memos := by
    intro record originals entries state memos inventory _ _ _ _ _ _ _ _
      rows arity count depth bound inputRows inputArity inputBound captured lengthBound pathsBound capturedHeight stored profile inputHeight
    exact ⟨stored, budget_refl _ _ _⟩
  have consCase : ∀ {record originals memos current saved entries before values middle result heap edges results after edge}
      {children : EditChildren record originals entries 0 edge.children before values middle}
      {rebuilt : run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.checked.native.machine.heap = (result, heap)}
      {rest : EditRows record originals entries edges (advanceHeap middle heap) results after},
      ChildrenReads formulas solver base children memos current → RowsReads formulas solver base rest current saved →
      ChildrenLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries 0 edge.children before values middle memos current →
      RowsLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries edges (advanceHeap middle heap) results after current saved →
      RowsLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries (edge :: edges) before (result :: results) after memos saved := by
    intro record originals memos current saved entries before values middle result heap edges results after edge children rebuilt rest
      firstReads restReads firstIH restIH inventory populated allowed ready resident safe valid known coherent
      rows arity count depth bound inputRows inputArity inputBound captured lengthBound pathsBound capturedHeight stored profile inputHeight
    have facts := ready.checked.semantic.ready.semantic.1.normal.facts
    have available := facts.cached.edges edge.entry.key edge (resident _ List.mem_cons_self)
    have childHeight : childrenHeight edge.children ≤ inputBound := by
      have firstHeight := Nat.le_trans (Nat.le_max_left _ _) inputHeight
      cases edge with | mk entry values => exact firstHeight
    have firstProfiles := firstIH inventory populated allowed ready available (safe _ List.mem_cons_self) valid known coherent
      rows arity count depth bound inputRows inputArity inputBound captured lengthBound pathsBound capturedHeight stored
      (SourceCurrentAllocatedFiniteOrdinaryNativeProfile.EdgeShape.children edge profile.1) childHeight
    obtain ⟨middleInventory, checked⟩ := SourceCurrentAllocatedSharedEditEffects.children_effects firstReads
      populated allowed ready available (safe _ List.mem_cons_self) valid
    have field := (ready.checked.good.fields _ _ (resident _ List.mem_cons_self)).grows checked.effects.grows
    have rebuiltPhysical := SourceCurrentAllocatedSharedEditEffects.edge_physical checked.ready edge.entry.key.symbol
      edge.entry.key.constraint values field checked.available
    have edgeReady : Ready formulas solver middleInventory record originals base (advanceHeap middle heap) := by
      simpa only [rebuilt] using rebuiltPhysical.1
    have edgeKeeps : Keeps middle.checked.native.machine.heap heap := by
      have keeps := rebuiltPhysical.2.1.keeps
      change Keeps middle.checked.native.machine.heap
        (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.checked.native.machine.heap).2 at keeps
      simpa only [rebuilt] using keeps
    have currentValid := SourceQueryUnfoldMemo.valid_grows _ _ checked.ready.checked.semantic edgeKeeps current checked.globals.valid
    have later := restIH middleInventory populated allowed edgeReady
      (fun original member => InternedEdgeResidency.edge_grows _ _ (checked.effects.keeps.trans edgeKeeps).growth original
        (resident original (List.mem_cons_of_mem _ member)))
      (fun original member => safe original (List.mem_cons_of_mem _ member)) currentValid known coherent
      rows arity count depth bound inputRows inputArity inputBound captured lengthBound pathsBound capturedHeight
      (SourceCurrentAllocatedFiniteOrdinarySharedProfiles.physical_stored middle ⟨heap, middle.checked.operations⟩ firstProfiles.1)
      profile.2 (Nat.le_trans (Nat.le_max_right _ _) inputHeight)
    have costs := SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.rows_cons
      (LeafN record rows arity count depth bound inputRows inputArity inputBound)
      (LeafE record rows arity count depth bound inputRows inputArity inputBound) edge edges
    have work : Budget middle (advanceHeap middle heap) 0 1 := by
      simpa only [rebuilt] using edge_work middle edge.entry.key.symbol edge.entry.key.constraint values
    have prefixBudget := budget_trans firstProfiles.2 work (nodes := CN (LeafN record rows arity count depth bound inputRows inputArity inputBound) edge.children)
      (edges := CE (LeafE record rows arity count depth bound inputRows inputArity inputBound) edge.children + 1) (by omega) (by omega)
    exact ⟨later.1, budget_trans prefixBudget later.2 (by omega) (by omega)⟩
  refine ⟨?_, ?_, ?_⟩
  · intro record originals edits value before result after memos final actual reads
    exact NodeReads.rec
      (motive_1 := fun {record originals edits value before result after} _ memos final _ =>
        NodeLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals edits value before result after memos final)
      (motive_2 := fun {record originals entries offset values before results after} _ memos final _ =>
        ChildrenLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries offset values before results after memos final)
      (motive_3 := fun {record originals entries edges before results after} _ memos final _ =>
        RowsLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries edges before results after memos final)
      @leafCase @emptyCase @ordinaryCase @recursiveCase @nilChildren @unselectedCase @selectedCase @nilRows @consCase reads
  · intro record originals entries offset values before results after memos final actual reads
    exact ChildrenReads.rec
      (motive_1 := fun {record originals edits value before result after} _ memos final _ =>
        NodeLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals edits value before result after memos final)
      (motive_2 := fun {record originals entries offset values before results after} _ memos final _ =>
        ChildrenLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries offset values before results after memos final)
      (motive_3 := fun {record originals entries edges before results after} _ memos final _ =>
        RowsLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries edges before results after memos final)
      @leafCase @emptyCase @ordinaryCase @recursiveCase @nilChildren @unselectedCase @selectedCase @nilRows @consCase reads
  · intro record originals entries edges before results after memos final actual reads
    exact RowsReads.rec
      (motive_1 := fun {record originals edits value before result after} _ memos final _ =>
        NodeLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals edits value before result after memos final)
      (motive_2 := fun {record originals entries offset values before results after} _ memos final _ =>
        ChildrenLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries offset values before results after memos final)
      (motive_3 := fun {record originals entries edges before results after} _ memos final _ =>
        RowsLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries edges before results after memos final)
      @leafCase @emptyCase @ordinaryCase @recursiveCase @nilChildren @unselectedCase @selectedCase @nilRows @consCase reads


variable {inventory : Inventory} {record : SourceEqualityClassOrder.Record}
variable {originals : List (Value Symbol Guard)}

/-- Supplied actual node reads produce their output shape and retain all positional structural facts. -/
theorem node {edits value before result after memos final}
    {actual : EditNode (width := width) record originals edits value before result after}
    (reads : NodeReads formulas solver base actual memos final)
    (populated : Populated edits) (nonempty : HasLeaf edits) (allowed : Allowed record edits)
    (ready : Ready formulas solver inventory record originals base before)
    (available : Available before.checked.native.machine.heap value) (safe : Safe edits value)
    (valid : Valid before.checked.native.machine.heap memos) (known : Values base originals)
    (coherent : SourceEqualityClassOrder.Coherent record)
    (rowLimit arity count depth bound inputRows inputArity inputBound : Nat)
    (captured : ChildrenShape rowLimit arity originals) (lengthBound : originals.length ≤ count)
    (pathsBound : ∀ path ∈ record.paths, path.length ≤ depth) (capturedHeight : childrenHeight originals ≤ bound)
    (stored : Stored (TargetRows record rowLimit count depth bound) (max arity 1) bound before)
    (profile : NodeShape inputRows inputArity value) (inputHeight : height value ≤ inputBound) :
    Stored (TargetRows record rowLimit count depth bound) (max arity 1) bound after ∧
      NodeShape (OutRows record rowLimit count depth bound inputRows) (OutArity arity inputArity) result ∧
      NodeNarrow value result ∧ height result ≤ inputBound ∧
      ∃ requests, Trace before.checked.native.machine.heap after.checked.native.machine.heap requests ∧
        nodeRequests requests ≤ NN (LeafN record rowLimit arity count depth bound inputRows inputArity inputBound) value ∧ edgeRequests requests ≤ NE (LeafE record rowLimit arity count depth bound inputRows inputArity inputBound) value := by
  have counted := retained.1 reads inventory populated nonempty allowed ready available safe valid known coherent
    rowLimit arity count depth bound inputRows inputArity inputBound captured lengthBound pathsBound capturedHeight stored profile inputHeight
  have previous := SourceCurrentAllocatedFiniteOrdinaryEditShapes.node reads populated nonempty allowed ready available safe valid known coherent
    rowLimit arity count depth bound inputRows inputArity inputBound captured lengthBound pathsBound capturedHeight stored profile inputHeight
  exact ⟨previous.1, previous.2.1, previous.2.2.1, previous.2.2.2, counted.2⟩

/-- Supplied actual children reads produce their output shape and retain all positional structural facts. -/
theorem children {entries offset values before results after memos final}
    {actual : EditChildren (width := width) record originals entries offset values before results after}
    (reads : ChildrenReads formulas solver base actual memos final)
    (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : Ready formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap values) (safe : ChildrenSafe entries offset values)
    (valid : Valid before.checked.native.machine.heap memos) (known : Values base originals)
    (coherent : SourceEqualityClassOrder.Coherent record)
    (rowLimit arity count depth bound inputRows inputArity inputBound : Nat)
    (captured : ChildrenShape rowLimit arity originals) (lengthBound : originals.length ≤ count)
    (pathsBound : ∀ path ∈ record.paths, path.length ≤ depth) (capturedHeight : childrenHeight originals ≤ bound)
    (stored : Stored (TargetRows record rowLimit count depth bound) (max arity 1) bound before)
    (profile : ChildrenShape inputRows inputArity values) (inputHeight : childrenHeight values ≤ inputBound) :
    Stored (TargetRows record rowLimit count depth bound) (max arity 1) bound after ∧
      ChildrenShape (OutRows record rowLimit count depth bound inputRows) (OutArity arity inputArity) results ∧
      All₂ NodeNarrow values results ∧ results.length = values.length ∧ childrenHeight results ≤ inputBound ∧
      ∃ requests, Trace before.checked.native.machine.heap after.checked.native.machine.heap requests ∧
        nodeRequests requests ≤ CN (LeafN record rowLimit arity count depth bound inputRows inputArity inputBound) values ∧ edgeRequests requests ≤ CE (LeafE record rowLimit arity count depth bound inputRows inputArity inputBound) values := by
  have counted := retained.2.1 reads inventory populated allowed ready available safe valid known coherent
    rowLimit arity count depth bound inputRows inputArity inputBound captured lengthBound pathsBound capturedHeight stored profile inputHeight
  have previous := SourceCurrentAllocatedFiniteOrdinaryEditShapes.children reads populated allowed ready available safe valid known coherent
    rowLimit arity count depth bound inputRows inputArity inputBound captured lengthBound pathsBound capturedHeight stored profile inputHeight
  exact ⟨previous.1, previous.2.1, previous.2.2.1, previous.2.2.2.1, previous.2.2.2.2, counted.2⟩

/-- Supplied actual rows reads produce their output shape and retain all positional structural facts. -/
theorem rows {entries edges before results after memos final}
    {actual : EditRows (width := width) record originals entries edges before results after}
    (reads : RowsReads formulas solver base actual memos final)
    (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : Ready formulas solver inventory record originals base before)
    (available : Edges before.checked.native.machine.heap edges) (safe : RowsSafe entries edges)
    (valid : Valid before.checked.native.machine.heap memos) (known : Values base originals)
    (coherent : SourceEqualityClassOrder.Coherent record)
    (rowLimit arity count depth bound inputRows inputArity inputBound : Nat)
    (captured : ChildrenShape rowLimit arity originals) (lengthBound : originals.length ≤ count)
    (pathsBound : ∀ path ∈ record.paths, path.length ≤ depth) (capturedHeight : childrenHeight originals ≤ bound)
    (stored : Stored (TargetRows record rowLimit count depth bound) (max arity 1) bound before)
    (profile : RowsShape inputRows inputArity edges) (inputHeight : edgesHeight edges ≤ inputBound) :
    Stored (TargetRows record rowLimit count depth bound) (max arity 1) bound after ∧
      RowsShape (OutRows record rowLimit count depth bound inputRows) (OutArity arity inputArity) results ∧
      All₂ EdgeNarrow edges results ∧ results.length = edges.length ∧ edgesHeight results ≤ inputBound ∧
      ∃ requests, Trace before.checked.native.machine.heap after.checked.native.machine.heap requests ∧
        nodeRequests requests ≤ RN (LeafN record rowLimit arity count depth bound inputRows inputArity inputBound) edges ∧ edgeRequests requests ≤ RE (LeafE record rowLimit arity count depth bound inputRows inputArity inputBound) edges := by
  have counted := retained.2.2 reads inventory populated allowed ready available safe valid known coherent
    rowLimit arity count depth bound inputRows inputArity inputBound captured lengthBound pathsBound capturedHeight stored profile inputHeight
  have previous := SourceCurrentAllocatedFiniteOrdinaryEditShapes.rows reads populated allowed ready available safe valid known coherent
    rowLimit arity count depth bound inputRows inputArity inputBound captured lengthBound pathsBound capturedHeight stored profile inputHeight
  exact ⟨previous.1, previous.2.1, previous.2.2.1, previous.2.2.2.1, previous.2.2.2.2, counted.2⟩

/-- Supplied actual list reads produce their output shape and retain all positional structural facts. -/
theorem list {edits values before results after memos final}
    {actual : EditList (width := width) record originals edits values before results after}
    (reads : ListReads formulas solver base actual memos final)
    (populated : Populated edits) (allowed : Allowed record edits)
    (ready : Ready formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap values) (safe : SourceCurrentAllocatedSharedEditEffects.ListSafe edits values)
    (valid : Valid before.checked.native.machine.heap memos) (known : Values base originals)
    (coherent : SourceEqualityClassOrder.Coherent record)
    (rowLimit arity count depth bound inputRows inputArity inputBound : Nat)
    (captured : ChildrenShape rowLimit arity originals) (lengthBound : originals.length ≤ count)
    (pathsBound : ∀ path ∈ record.paths, path.length ≤ depth) (capturedHeight : childrenHeight originals ≤ bound)
    (stored : Stored (TargetRows record rowLimit count depth bound) (max arity 1) bound before)
    (profile : ChildrenShape inputRows inputArity values) (inputHeight : childrenHeight values ≤ inputBound) :
    Stored (TargetRows record rowLimit count depth bound) (max arity 1) bound after ∧
      ChildrenShape (OutRows record rowLimit count depth bound inputRows) (OutArity arity inputArity) results ∧
      All₂ NodeNarrow values results ∧ results.length = values.length ∧ childrenHeight results ≤ inputBound ∧
      ∃ requests, Trace before.checked.native.machine.heap after.checked.native.machine.heap requests ∧
        nodeRequests requests ≤ CN (LeafN record rowLimit arity count depth bound inputRows inputArity inputBound) values ∧ edgeRequests requests ≤ CE (LeafE record rowLimit arity count depth bound inputRows inputArity inputBound) values := by
  have previous := SourceCurrentAllocatedFiniteOrdinaryEditShapes.list reads populated allowed ready available safe valid known coherent
    rowLimit arity count depth bound inputRows inputArity inputBound captured lengthBound pathsBound capturedHeight stored profile inputHeight
  have counted : Budget before after (CN (LeafN record rowLimit arity count depth bound inputRows inputArity inputBound) values) (CE (LeafE record rowLimit arity count depth bound inputRows inputArity inputBound) values) := by
    cases reads with
    | leaf => exact budget_refl _ _ _
    | children read => exact (retained.2.1 read inventory populated allowed ready available safe valid known coherent
        rowLimit arity count depth bound inputRows inputArity inputBound captured lengthBound pathsBound capturedHeight stored profile inputHeight).2
  exact ⟨previous.1, previous.2.1, previous.2.2.1, previous.2.2.2.1, previous.2.2.2.2, counted⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryActualEditWork
