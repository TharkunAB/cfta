import MicroCFTA.SourceCurrentEditDomains
import MicroCFTA.SourceCurrentMemoSharedEditGraph
import MicroCFTA.SourceCurrentRequiredHeapEffects
import MicroCFTA.SourceEqualitySharedEditEffects
import MicroCFTA.SourceEqualityOpenOrdinaryHead

/-!
# Selected path domains through memo-aware shared edits

Captured class paths supply the closed native operands. Ordinary traversal
can retain open unselected children. Each actual shared target force and
native request retains its returned state. The result preserves every
original tracked path domain. No future result domain is supplied.
-/
namespace MicroCFTA.SourceCurrentMemoSharedEditDomains
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityNativeScoped
open SourceEqualityEdits SourceEqualityEditLeafPaths SourceCurrentMemoSharedEditGraph SourceEqualitySharedEditEffects
open SourceCurrentMemoSharedTargetState SourceCurrentMemoSharedTargetForce SourceCurrentMemoSharedTargetLeaf
open SourceEqualityProjectionPathDomain
open SourceCurrentEditDomains

/-- A concrete source leaf derives closed output from its actual force and native request. -/
theorem leaf_effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {originals : List (Value Symbol Guard)}
    {base : InternedConstructorTemplates.State Symbol Guard} {path : EqualityNormalize.Path}
    {input result : Value Symbol Guard} {before after : SharedState width Symbol Guard}
    (actual : Leaf emptyGuard conjoin clear top record originals path input before result after)
    (ready : SourceCurrentMemoSharedTargetState.Ready emptyGuard conjoin clear top record originals base before)
    (known : Values base originals)
    (domains : ∀ p ∈ record.paths, ForestClosed (p.map Int.ofNat) originals)
    (member : path ∈ record.paths) (available : Available before.native.machine.heap input) (closed : input.free = []) :
    SourceCurrentMemoSharedTargetState.Ready emptyGuard conjoin clear top record originals base after ∧
      Keeps before.native.machine.heap after.native.machine.heap ∧ Available after.native.machine.heap result ∧ result.free = [] := by
  have checked := actual.effects ready known domains member available closed
  exact ⟨checked.1, checked.2.1, checked.2.2.1, checked.2.2.2.1⟩

private theorem aligned_rows_closed {edges results : List (EdgeValue Symbol Guard)}
    (aligned : All₂ (fun edge result => All₂ Transport edge.children result.children) edges results)
    (closed : ClosedEdges edges) : ClosedEdges results := by
  induction aligned with
  | nil => intro edge member; cases member
  | cons first rest ih =>
      intro edge member
      rcases List.mem_cons.mp member with rfl | member
      · exact transport_forest first [] (closed _ List.mem_cons_self)
      · exact ih (fun original included => closed original (List.mem_cons_of_mem _ included)) edge member

private theorem aligned_rows_path {edges results : List (EdgeValue Symbol Guard)}
    (aligned : All₂ (fun edge result => All₂ Transport edge.children result.children) edges results)
    (index : Int) (path : List Int) (domain : RowsClosed path index edges) : RowsClosed path index results := by
  induction aligned with
  | nil => intro edge member; cases member
  | cons first rest ih =>
      intro edge member
      rcases List.mem_cons.mp member with rfl | member
      · exact transport_forest first (index :: path) (domain _ List.mem_cons_self)
      · exact ih (fun original included => domain original (List.mem_cons_of_mem _ included)) edge member

private theorem makeNode_path [DecidableEq (EdgeKey Symbol Guard)]
    (index : Int) (path : List Int) (edges : List (EdgeValue Symbol Guard)) (state : InternedConstructorTemplates.State Symbol Guard)
    (facts : InternedNestedFacts.Facts state) (resident : Edges state edges) (domain : RowsClosed path index edges) :
    NodeClosed (index :: path) (run (makeNode edges) state).1 := by
  have ordinary := SourceEqualityRequiredCache.node_ordinary edges state facts resident
  generalize same : (run (makeNode edges) state).1 = value at ordinary ⊢
  cases value with
  | empty => simp only [NodeClosed]
  | reference | union | mu => cases ordinary
  | node entry rows depth free =>
      rw [NodeClosed]
      intro edge member child selected
      have origin : edge ∈ edges := by
        have present : edge ∈ InternedEdgeResidency.nodeEdges (run (makeNode edges) state).1 := by
          rw [same]
          exact member
        rw [EqualityLeafProjectionPhysical.makeNode_edges edges state facts.coherent facts.linked resident] at present
        exact (List.mem_filter.mp (canonicalEdges_member _ edge present)).1
      exact domain edge origin child selected

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
variable (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
variable (base : InternedConstructorTemplates.State Symbol Guard)
variable (known : Values base originals)
variable (domains : ∀ p ∈ record.paths, ForestClosed (p.map Int.ofNat) originals)

private def NodeEffects (edits : Edits EqualityNormalize.Path) (value : Value Symbol Guard)
    (before : SharedState width Symbol Guard) (result : Value Symbol Guard) (after : SharedState width Symbol Guard) : Prop :=
  Populated edits → HasLeaf edits → Allowed record edits →
    SourceCurrentMemoSharedTargetState.Ready emptyGuard conjoin clear top record originals base before →
    Available before.native.machine.heap value → Safe edits value →
    SourceCurrentMemoSharedTargetState.Ready emptyGuard conjoin clear top record originals base after ∧
      Keeps before.native.machine.heap after.native.machine.heap ∧ Available after.native.machine.heap result ∧ Transport value result

private def ChildrenEffects (entries : List (Int × Edits EqualityNormalize.Path)) (offset : Nat) (values : List (Value Symbol Guard))
    (before : SharedState width Symbol Guard) (results : List (Value Symbol Guard)) (after : SharedState width Symbol Guard) : Prop :=
  Populated (.editBelow entries) → Allowed record (.editBelow entries) →
    SourceCurrentMemoSharedTargetState.Ready emptyGuard conjoin clear top record originals base before →
    Values before.native.machine.heap values → ChildrenSafe entries offset values →
    SourceCurrentMemoSharedTargetState.Ready emptyGuard conjoin clear top record originals base after ∧
      Keeps before.native.machine.heap after.native.machine.heap ∧ Values after.native.machine.heap results ∧ All₂ Transport values results

private def RowsEffects (entries : List (Int × Edits EqualityNormalize.Path)) (edges : List (EdgeValue Symbol Guard))
    (before : SharedState width Symbol Guard) (results : List (EdgeValue Symbol Guard)) (after : SharedState width Symbol Guard) : Prop :=
  Populated (.editBelow entries) → Allowed record (.editBelow entries) →
    SourceCurrentMemoSharedTargetState.Ready emptyGuard conjoin clear top record originals base before →
    Edges before.native.machine.heap edges → RowsSafe entries edges →
    SourceCurrentMemoSharedTargetState.Ready emptyGuard conjoin clear top record originals base after ∧
      Keeps before.native.machine.heap after.native.machine.heap ∧ Edges after.native.machine.heap results ∧
        All₂ (fun edge result => All₂ Transport edge.children result.children) edges results

local notation "NodeLaw" => NodeEffects (width := width) emptyGuard conjoin clear top record originals base
local notation "ChildrenLaw" => ChildrenEffects (width := width) emptyGuard conjoin clear top record originals base
local notation "RowsLaw" => RowsEffects (width := width) emptyGuard conjoin clear top record originals base

include known domains

private theorem effects :
    (∀ edits (value : Value Symbol Guard) before result after,
      EditNode emptyGuard conjoin clear top record originals edits value before result after → NodeLaw edits value before result after) ∧
    (∀ entries offset (values : List (Value Symbol Guard)) before results after,
      EditChildren emptyGuard conjoin clear top record originals entries offset values before results after → ChildrenLaw entries offset values before results after) ∧
    (∀ entries (edges : List (EdgeValue Symbol Guard)) before results after,
      EditRows emptyGuard conjoin clear top record originals entries edges before results after → RowsLaw entries edges before results after) := by
  have leafCase : ∀ {path value before result after}, Leaf emptyGuard conjoin clear top record originals path value before result after →
      NodeLaw (.editAt path) value before result after := by
    intro path value before result after trace _ _ allowed ready available safe
    have member : path ∈ record.paths := by simpa only [Allowed, All] using allowed
    have closed : value.free = [] := by simpa only [NodeClosed] using safe [] path (by simp [leaves])
    have checked := leaf_effects trace ready known domains member available closed
    refine ⟨checked.1, checked.2.1, checked.2.2.1, ?_⟩
    intro query _
    exact SourceCurrentRequiredEndpoints.closed_path query result after.native.machine.heap checked.1.native.semantic checked.2.2.1 checked.2.2.2
  have emptyCase : ∀ {entries state}, NodeLaw (.editBelow entries) (.empty : Value Symbol Guard) state .empty state := by
    intro entries state _ _ _ ready available _
    exact ⟨ready, pure_keeps _ ready.native.semantic.ready, available, fun _ domain => domain⟩
  have ordinaryCase : ∀ {entries edges before rebuilt middle value heap entry depth free},
      EditRows emptyGuard conjoin clear top record originals entries edges before rebuilt middle →
      run (makeNode rebuilt) middle.native.machine.heap = (value, heap) → RowsLaw entries edges before rebuilt middle →
      NodeLaw (.editBelow entries) (.node entry edges depth free) before value (advanceHeap middle heap) := by
    intro entries edges before rebuilt middle value heap entry depth free _ built ih populated _ allowed ready available safe
    have facts := ready.native.semantic.ready.semantic.1.normal.facts
    have rows := ih populated allowed ready (InternedEdgeResidency.resident_edges _ facts.linked _ available.resident)
      (ordinary_rows safe)
    have finished := SourceEqualityOpenOrdinaryHead.node rebuilt middle.native.machine.heap rows.1.native.semantic rows.2.2.1
    have kept : Keeps middle.native.machine.heap heap := by simpa only [built] using finished.1
    have semantic : SemanticReady heap := by simpa only [built] using finished.2.1
    have resultAvailable : Available heap value := by simpa only [built] using finished.2.2.1
    refine ⟨rows.1.heap heap kept semantic (by
      have costs := InternedFreshOrdinaryCostHeap.preserve middle.native.machine.heap _ rows.1.costs
        (InternedShallowHeap.makeNode_noNewMu rebuilt middle.native.machine.heap)
      simpa only [built] using costs), rows.2.1.trans kept, resultAvailable, ?_⟩
    intro query domain
    cases query with
    | nil =>
        have inputClosed : (.node entry edges depth free : Value Symbol Guard).free = [] := by simpa only [NodeClosed] using domain
        have originalClosed := MergedColdReaderClosed.node_children_closed _ facts entry edges depth free available inputClosed
        have rebuiltClosed := aligned_rows_closed rows.2.2.2 originalClosed
        have closed := SourceEqualityRequiredCache.node rebuilt middle.native.machine.heap rows.1.native.semantic.ready rows.2.2.1 rebuiltClosed
        simpa only [NodeClosed, built] using closed.2.2.1
    | cons index path =>
        have inputDomain : RowsClosed path index edges := by simpa only [NodeClosed, RowsClosed] using domain
        have resultDomain := makeNode_path index path rebuilt middle.native.machine.heap
          rows.1.native.semantic.ready.semantic.1.normal.facts rows.2.2.1 (aligned_rows_path rows.2.2.2 index path inputDomain)
        simpa only [built] using resultDomain
  have recursiveCase : ∀ {entries original before exposed heap result after},
      SourceEqualityRequiredGraph.Recursive original → SourceEqualityRequiredHead.Head original before.native.machine.heap exposed heap →
      EditNode emptyGuard conjoin clear top record originals (.editBelow entries) exposed (advanceHeap before heap) result after →
      NodeLaw (.editBelow entries) exposed (advanceHeap before heap) result after → NodeLaw (.editBelow entries) original before result after := by
    intro entries original before exposed heap result after recursive head _ ih populated nonempty allowed ready available safe
    have closed := recursive_closed recursive nonempty safe
    have first := head.verified ready.native.semantic.ready available closed
    have semantic := SourceEqualityRequiredSemanticCache.head head ready.native.semantic available closed
    have physical := SourceCurrentRequiredHeapEffects.head (fun _ => True) head ready.native.semantic ready.costs (fun _ _ _ => trivial) available
    have later := ih populated nonempty allowed (ready.heap heap first.1 semantic physical.2.2.1) first.2.1
      (closed_safe _ exposed heap semantic first.2.1 first.2.2.1)
    refine ⟨later.1, first.1.trans later.2.1, later.2.2.1, ?_⟩
    intro query _
    exact later.2.2.2 query (SourceCurrentRequiredEndpoints.closed_path query exposed heap semantic first.2.1 first.2.2.1)
  have nilChildren : ∀ {entries offset state}, ChildrenLaw entries offset ([] : List (Value Symbol Guard)) state [] state := by
    intro entries offset state _ _ ready _ _
    exact ⟨ready, pure_keeps _ ready.native.semantic.ready, by simp [Values], .nil⟩
  have unselectedCase : ∀ {entries values before results after value} (offset : Nat),
      SourceEqualityNeededMap.lookup (offset : Int) entries = none →
      EditChildren emptyGuard conjoin clear top record originals entries (offset + 1) values before results after →
      ChildrenLaw entries (offset + 1) values before results after → ChildrenLaw entries offset (value :: values) before (value :: results) after := by
    intro entries values before results after value offset _ _ ih populated allowed ready available safe
    have later := ih populated allowed ready (fun original member => available original (List.mem_cons_of_mem _ member))
      (children_tail safe)
    refine ⟨later.1, later.2.1, ?_, .cons (fun _ domain => domain) later.2.2.2⟩
    intro original member
    rcases List.mem_cons.mp member with rfl | member
    · exact later.2.1.available _ (available _ List.mem_cons_self)
    · exact later.2.2.1 _ member
  have selectedCase : ∀ {entries edits value before result middle values results after} (offset : Nat),
      SourceEqualityNeededMap.lookup (offset : Int) entries = some edits →
      EditNode emptyGuard conjoin clear top record originals edits value before result middle →
      EditChildren emptyGuard conjoin clear top record originals entries (offset + 1) values middle results after →
      NodeLaw edits value before result middle → ChildrenLaw entries (offset + 1) values middle results after →
      ChildrenLaw entries offset (value :: values) before (result :: results) after := by
    intro entries edits value before result middle values results after offset found _ _ firstIH restIH populated allowed ready available safe
    have member := SourceEqualityNeededMap.lookup_mem _ _ _ found
    have populated := (show ∀ index child, (index, child) ∈ entries → Populated child ∧ HasLeaf child from
      by simpa only [Populated] using populated)
    have childAllowed : Allowed record edits := by
      have allowed := allowed
      rw [Allowed, All] at allowed
      exact allowed _ _ member
    have first := firstIH (populated _ _ member).1 (populated _ _ member).2 childAllowed ready
      (available _ List.mem_cons_self) (safe 0 _ (by simpa using found) value rfl)
    have later := restIH (by simpa only [Populated] using populated) allowed first.1
      (fun original member => first.2.1.available original (available original (List.mem_cons_of_mem _ member))) (children_tail safe)
    refine ⟨later.1, first.2.1.trans later.2.1, ?_, .cons first.2.2.2 later.2.2.2⟩
    intro original member
    rcases List.mem_cons.mp member with rfl | member
    · exact later.2.1.available _ first.2.2.1
    · exact later.2.2.1 _ member
  have nilRows : ∀ {entries state}, RowsLaw entries ([] : List (EdgeValue Symbol Guard)) state [] state := by
    intro entries state _ _ ready _ _
    exact ⟨ready, pure_keeps _ ready.native.semantic.ready, by simp [Edges], .nil⟩
  have consCase : ∀ {entries before values middle result heap edges results after edge},
      EditChildren emptyGuard conjoin clear top record originals entries 0 edge.children before values middle →
      run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.native.machine.heap = (result, heap) →
      EditRows emptyGuard conjoin clear top record originals entries edges (advanceHeap middle heap) results after →
      ChildrenLaw entries 0 edge.children before values middle → RowsLaw entries edges (advanceHeap middle heap) results after →
      RowsLaw entries (edge :: edges) before (result :: results) after := by
    intro entries before values middle result heap edges results after edge _ built _ firstIH restIH populated allowed ready resident safe
    have facts := ready.native.semantic.ready.semantic.1.normal.facts
    have first := firstIH populated allowed ready (facts.cached.edges edge.entry.key edge (resident _ List.mem_cons_self))
      (safe _ List.mem_cons_self)
    have rebuilt := SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle.native.machine.heap
      first.1.native.semantic.ready first.2.2.1
    have semantic := SourceEqualityRequiredSemanticCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle.native.machine.heap
      first.1.native.semantic first.2.2.1
    have edgeKept : Keeps middle.native.machine.heap heap := by simpa only [built] using rebuilt.1
    have edgeSemantic : SemanticReady heap := by simpa only [built] using semantic
    have edgeResident : InternedEdgeResidency.EdgeResident heap result := by simpa only [built] using rebuilt.2.1
    have children : result.children = values := by simpa only [built] using rebuilt.2.2
    have firstKept := first.2.1.trans edgeKept
    have later := restIH populated allowed (first.1.heap heap edgeKept edgeSemantic (by
      have costs : InternedFreshOrdinaryCostHeap.Heap (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.native.machine.heap).2 := first.1.costs
      simpa only [built] using costs))
      (fun original member => InternedEdgeResidency.edge_grows _ _ firstKept.growth original (resident original (List.mem_cons_of_mem _ member)))
      (fun original member => safe original (List.mem_cons_of_mem _ member))
    refine ⟨later.1, firstKept.trans later.2.1, ?_, .cons ?_ later.2.2.2⟩
    · intro original member
      rcases List.mem_cons.mp member with rfl | member
      · exact InternedEdgeResidency.edge_grows _ _ later.2.1.growth _ edgeResident
      · exact later.2.2.1 original member
    · simpa only [children] using first.2.2.2
  refine ⟨?_, ?_, ?_⟩
  · intro edits value before result after trace
    exact EditNode.rec (motive_1 := fun edits value before result after _ => NodeLaw edits value before result after)
      (motive_2 := fun entries offset values before results after _ => ChildrenLaw entries offset values before results after)
      (motive_3 := fun entries edges before results after _ => RowsLaw entries edges before results after)
      leafCase emptyCase ordinaryCase recursiveCase nilChildren unselectedCase selectedCase nilRows consCase trace
  · intro entries offset values before results after trace
    exact EditChildren.rec (motive_1 := fun edits value before result after _ => NodeLaw edits value before result after)
      (motive_2 := fun entries offset values before results after _ => ChildrenLaw entries offset values before results after)
      (motive_3 := fun entries edges before results after _ => RowsLaw entries edges before results after)
      leafCase emptyCase ordinaryCase recursiveCase nilChildren unselectedCase selectedCase nilRows consCase trace
  · intro entries edges before results after trace
    exact EditRows.rec (motive_1 := fun edits value before result after _ => NodeLaw edits value before result after)
      (motive_2 := fun entries offset values before results after _ => ChildrenLaw entries offset values before results after)
      (motive_3 := fun entries edges before results after _ => RowsLaw entries edges before results after)
      leafCase emptyCase ordinaryCase recursiveCase nilChildren unselectedCase selectedCase nilRows consCase trace

/-- Actual node edits retain their shared state and every tracked node-path domain. -/
theorem node_domains {edits value before result after}
    (actual : EditNode (width := width) emptyGuard conjoin clear top record originals edits value before result after)
    (populated : Populated edits) (nonempty : HasLeaf edits) (allowed : Allowed record edits)
    (ready : SourceCurrentMemoSharedTargetState.Ready emptyGuard conjoin clear top record originals base before)
    (available : Available before.native.machine.heap value) (safe : Safe edits value) :
    SourceCurrentMemoSharedTargetState.Ready emptyGuard conjoin clear top record originals base after ∧
      Keeps before.native.machine.heap after.native.machine.heap ∧ Available after.native.machine.heap result ∧ Transport value result :=
  (effects emptyGuard conjoin clear top record originals base known domains).1 _ _ _ _ _ actual populated nonempty allowed ready available safe

/-- Actual ordered child edits retain every original position and its path-domain transport. -/
theorem children_domains {entries offset values before results after}
    (actual : EditChildren (width := width) emptyGuard conjoin clear top record originals entries offset values before results after)
    (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : SourceCurrentMemoSharedTargetState.Ready emptyGuard conjoin clear top record originals base before)
    (available : Values before.native.machine.heap values) (safe : ChildrenSafe entries offset values) :
    SourceCurrentMemoSharedTargetState.Ready emptyGuard conjoin clear top record originals base after ∧
      Keeps before.native.machine.heap after.native.machine.heap ∧ Values after.native.machine.heap results ∧ All₂ Transport values results :=
  (effects emptyGuard conjoin clear top record originals base known domains).2.1 _ _ _ _ _ _ actual populated allowed ready available safe

/-- Actual row edits retain every original row and the domains of its same-position children. -/
theorem rows_domains {entries edges before results after}
    (actual : EditRows (width := width) emptyGuard conjoin clear top record originals entries edges before results after)
    (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : SourceCurrentMemoSharedTargetState.Ready emptyGuard conjoin clear top record originals base before)
    (resident : Edges before.native.machine.heap edges) (safe : RowsSafe entries edges) :
    SourceCurrentMemoSharedTargetState.Ready emptyGuard conjoin clear top record originals base after ∧
      Keeps before.native.machine.heap after.native.machine.heap ∧ Edges after.native.machine.heap results ∧
        All₂ (fun edge result => All₂ Transport edge.children result.children) edges results :=
  (effects emptyGuard conjoin clear top record originals base known domains).2.2 _ _ _ _ _ actual populated allowed ready resident safe

end MicroCFTA.SourceCurrentMemoSharedEditDomains
