import MicroCFTA.SourceCurrentMemoSharedEditDomains
import MicroCFTA.SourceCurrentMemoSharedEditRanges

/-!
# Finite shared class edits from selected path domains

Actual demand-prefix range checks derive each first target force and native
leaf. The finite edit trie derives the remaining calls. The proof retains
unselected open children and the literal returned native states.
-/
namespace MicroCFTA.SourceCurrentMemoSharedEditComplete
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityNativeScoped
open SourceCurrentMemoSharedTargetState SourceCurrentMemoSharedTargetForce SourceCurrentMemoSharedTargetLeaf
open SourceEqualityEdits SourceCurrentMemoSharedEditGraph SourceCurrentMemoSharedEditRanges SourceEqualitySharedEditEffects
open SourceEqualityProjectionPathDomain SourceCurrentEditDomains SourceCurrentMemoSharedEditDomains

/-- Actual first-force checks and native word checks derive a concrete closed leaf result. -/
theorem leaf_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
    (base : InternedConstructorTemplates.State Symbol Guard) (known : Values base originals)
    (domains : ∀ p ∈ record.paths, ForestClosed (p.map Int.ofNat) originals)
    (path : EqualityNormalize.Path) (member : path ∈ record.paths) (input : Value Symbol Guard)
    (before : SharedState width Symbol Guard)
    (ready : SourceCurrentMemoSharedTargetState.Ready emptyGuard conjoin clear top record originals base before)
    (ranges : SourceCurrentMemoSharedTargetLeaf.LeafRanges emptyGuard conjoin clear top record originals path input before)
    (available : Available before.native.machine.heap input) (closed : input.free = []) :
    ∃ result after, Leaf emptyGuard conjoin clear top record originals path input before result after ∧
      SourceCurrentMemoSharedTargetState.Ready emptyGuard conjoin clear top record originals base after ∧
      Keeps before.native.machine.heap after.native.machine.heap ∧ Available after.native.machine.heap result ∧ result.free = [] := by
  obtain ⟨result, after, actual, checked⟩ := SourceCurrentMemoSharedTargetLeaf.complete
    emptyGuard conjoin clear top record originals base known domains path member input before ready ranges available closed
  exact ⟨result, after, actual, checked.1, checked.2.1, checked.2.2.1, checked.2.2.2.1⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
variable (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
variable (base : InternedConstructorTemplates.State Symbol Guard) (known : Values base originals)
variable (domains : ∀ p ∈ record.paths, ForestClosed (p.map Int.ofNat) originals)

private def NodeComplete (edits : Edits EqualityNormalize.Path) (value : Value Symbol Guard)
    (before : SharedState width Symbol Guard) : Prop :=
  Populated edits → HasLeaf edits → Allowed record edits →
    SourceCurrentMemoSharedTargetState.Ready emptyGuard conjoin clear top record originals base before →
    Available before.native.machine.heap value → Safe edits value →
      ∃ result after, EditNode emptyGuard conjoin clear top record originals edits value before result after

private def ChildrenComplete (entries : List (Int × Edits EqualityNormalize.Path)) (offset : Nat)
    (values : List (Value Symbol Guard)) (before : SharedState width Symbol Guard) : Prop :=
  Populated (.editBelow entries) → Allowed record (.editBelow entries) →
    SourceCurrentMemoSharedTargetState.Ready emptyGuard conjoin clear top record originals base before →
    Values before.native.machine.heap values → ChildrenSafe entries offset values →
      ∃ results after, EditChildren emptyGuard conjoin clear top record originals entries offset values before results after

private def RowsComplete (entries : List (Int × Edits EqualityNormalize.Path)) (edges : List (EdgeValue Symbol Guard))
    (before : SharedState width Symbol Guard) : Prop :=
  Populated (.editBelow entries) → Allowed record (.editBelow entries) →
    SourceCurrentMemoSharedTargetState.Ready emptyGuard conjoin clear top record originals base before →
    Edges before.native.machine.heap edges → RowsSafe entries edges →
      ∃ results after, EditRows emptyGuard conjoin clear top record originals entries edges before results after

local notation "NodeLaw" => NodeComplete (width := width) emptyGuard conjoin clear top record originals base
local notation "ChildrenLaw" => ChildrenComplete (width := width) emptyGuard conjoin clear top record originals base
local notation "RowsLaw" => RowsComplete (width := width) emptyGuard conjoin clear top record originals base

include known domains

private theorem complete :
    (∀ edits (value : Value Symbol Guard) before,
      NodeRanges emptyGuard conjoin clear top record originals edits value before → NodeLaw edits value before) ∧
    (∀ entries offset (values : List (Value Symbol Guard)) before,
      ChildrenRanges emptyGuard conjoin clear top record originals entries offset values before → ChildrenLaw entries offset values before) ∧
    (∀ entries (edges : List (EdgeValue Symbol Guard)) before,
      RowsRanges emptyGuard conjoin clear top record originals entries edges before → RowsLaw entries edges before) := by
  have leafCase : ∀ {path value before}, SourceCurrentMemoSharedTargetLeaf.LeafRanges emptyGuard conjoin clear top record originals path value before →
      NodeLaw (.editAt path) value before := by
    intro path value before ranges _ _ allowed ready available safe
    have member : path ∈ record.paths := by simpa only [Allowed, All] using allowed
    have closed : value.free = [] := by simpa only [NodeClosed] using safe [] path (by simp [SourceEqualityEditLeafPaths.leaves])
    obtain ⟨result, after, actual, _⟩ := leaf_complete emptyGuard conjoin clear top record originals base known domains path member value before ready ranges available closed
    exact ⟨result, after, .leaf actual⟩
  have emptyCase : ∀ {entries before}, NodeLaw (.editBelow entries) (.empty : Value Symbol Guard) before := by
    intro entries before _ _ _ _ _ _
    exact ⟨_, _, .empty⟩
  have ordinaryCase : ∀ {entries edges before entry depth free},
      RowsRanges emptyGuard conjoin clear top record originals entries edges before → RowsLaw entries edges before →
      NodeLaw (.editBelow entries) (.node entry edges depth free) before := by
    intro entries edges before entry depth free _ ih populated _ allowed ready available safe
    have facts := ready.native.semantic.ready.semantic.1.normal.facts
    obtain ⟨rebuilt, middle, rows⟩ := ih populated allowed ready
      (InternedEdgeResidency.resident_edges _ facts.linked _ available.resident) (ordinary_rows safe)
    exact ⟨_, _, .ordinary rows rfl⟩
  have recursiveCase : ∀ {original entries before}, SourceEqualityRequiredGraph.Recursive original →
      (∀ exposed heap, SourceEqualityRequiredHead.Head original before.native.machine.heap exposed heap →
        NodeRanges emptyGuard conjoin clear top record originals (.editBelow entries) exposed (advanceHeap before heap)) →
      (∀ exposed heap, SourceEqualityRequiredHead.Head original before.native.machine.heap exposed heap →
        NodeLaw (.editBelow entries) exposed (advanceHeap before heap)) → NodeLaw (.editBelow entries) original before := by
    intro original entries before recursive _ ih populated nonempty allowed ready available safe
    have closed := recursive_closed recursive nonempty safe
    obtain ⟨exposed, heap, head, kept, exposedAvailable, exposedClosed, _⟩ :=
      SourceEqualityRequiredHead.complete original before.native.machine.heap ready.native.semantic.ready available closed
    have semantic := SourceEqualityRequiredSemanticCache.head head ready.native.semantic available closed
    have physical := SourceCurrentRequiredHeapEffects.head (fun _ => True) head ready.native.semantic ready.costs (fun _ _ _ => trivial) available
    obtain ⟨result, after, body⟩ := ih exposed heap head populated nonempty allowed (ready.heap heap kept semantic physical.2.2.1)
      exposedAvailable (closed_safe _ exposed heap semantic exposedAvailable exposedClosed)
    exact ⟨result, after, .recursive recursive head body⟩
  have nilChildren : ∀ {entries offset before}, ChildrenLaw entries offset ([] : List (Value Symbol Guard)) before := by
    intro entries offset before _ _ _ _ _
    exact ⟨_, _, .nil⟩
  have unselectedCase : ∀ {entries values before value} (offset : Nat),
      SourceEqualityNeededMap.lookup (offset : Int) entries = none →
      ChildrenRanges emptyGuard conjoin clear top record originals entries (offset + 1) values before →
      ChildrenLaw entries (offset + 1) values before → ChildrenLaw entries offset (value :: values) before := by
    intro entries values before value offset absent _ ih populated allowed ready available safe
    obtain ⟨results, after, rest⟩ := ih populated allowed ready
      (fun original member => available original (List.mem_cons_of_mem _ member)) (children_tail safe)
    exact ⟨_, _, .unselected offset absent rest⟩
  have selectedCase : ∀ {entries edits value before values} (offset : Nat),
      SourceEqualityNeededMap.lookup (offset : Int) entries = some edits →
      NodeRanges emptyGuard conjoin clear top record originals edits value before →
      (∀ result middle, EditNode emptyGuard conjoin clear top record originals edits value before result middle →
        ChildrenRanges emptyGuard conjoin clear top record originals entries (offset + 1) values middle) →
      NodeLaw edits value before →
      (∀ result middle, EditNode emptyGuard conjoin clear top record originals edits value before result middle →
        ChildrenLaw entries (offset + 1) values middle) → ChildrenLaw entries offset (value :: values) before := by
    intro entries edits value before values offset found _ _ firstIH restIH populated allowed ready available safe
    have member := SourceEqualityNeededMap.lookup_mem _ _ _ found
    have childPopulated := (show ∀ index child, (index, child) ∈ entries → Populated child ∧ HasLeaf child from
      by simpa only [Populated] using populated) _ _ member
    have childAllowed : Allowed record edits := by
      have allowed := allowed
      rw [Allowed, All] at allowed
      exact allowed _ _ member
    have firstSafe := safe 0 _ (by simpa using found) value rfl
    obtain ⟨result, middle, first⟩ := firstIH childPopulated.1 childPopulated.2 childAllowed ready (available _ List.mem_cons_self) firstSafe
    have effects := node_domains emptyGuard conjoin clear top record originals base known domains first childPopulated.1 childPopulated.2 childAllowed
      ready (available _ List.mem_cons_self) firstSafe
    obtain ⟨results, after, rest⟩ := restIH result middle first populated allowed effects.1
      (fun original member => effects.2.1.available original (available original (List.mem_cons_of_mem _ member))) (children_tail safe)
    exact ⟨_, _, .selected offset found first rest⟩
  have nilRows : ∀ {entries before}, RowsLaw entries ([] : List (EdgeValue Symbol Guard)) before := by
    intro entries before _ _ _ _ _
    exact ⟨_, _, .nil⟩
  have consCase : ∀ {entries edge edges before},
      ChildrenRanges emptyGuard conjoin clear top record originals entries 0 edge.children before →
      (∀ values middle, EditChildren emptyGuard conjoin clear top record originals entries 0 edge.children before values middle →
        RowsRanges emptyGuard conjoin clear top record originals entries edges
          (advanceHeap middle (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.native.machine.heap).2)) →
      ChildrenLaw entries 0 edge.children before →
      (∀ values middle, EditChildren emptyGuard conjoin clear top record originals entries 0 edge.children before values middle →
        RowsLaw entries edges (advanceHeap middle (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.native.machine.heap).2)) →
      RowsLaw entries (edge :: edges) before := by
    intro entries edge edges before _ _ firstIH restIH populated allowed ready resident safe
    have available := ready.native.semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident _ List.mem_cons_self)
    obtain ⟨values, middle, first⟩ := firstIH populated allowed ready available (safe _ List.mem_cons_self)
    have effects := children_domains emptyGuard conjoin clear top record originals base known domains first populated allowed ready available (safe _ List.mem_cons_self)
    let built := run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.native.machine.heap
    have edgeKept := (SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle.native.machine.heap
      effects.1.native.semantic.ready effects.2.2.1).1
    have edgeSemantic := SourceEqualityRequiredSemanticCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle.native.machine.heap
      effects.1.native.semantic effects.2.2.1
    have firstKept := effects.2.1.trans edgeKept
    obtain ⟨results, after, rest⟩ := restIH values middle first populated allowed (effects.1.heap built.2 edgeKept edgeSemantic effects.1.costs)
      (fun original member => InternedEdgeResidency.edge_grows _ _ firstKept.growth original (resident original (List.mem_cons_of_mem _ member)))
      (fun original member => safe original (List.mem_cons_of_mem _ member))
    exact ⟨_, _, .cons first rfl rest⟩
  refine ⟨?_, ?_, ?_⟩
  · intro edits value before ranges
    exact NodeRanges.rec (motive_1 := fun edits value before _ => NodeLaw edits value before)
      (motive_2 := fun entries offset values before _ => ChildrenLaw entries offset values before)
      (motive_3 := fun entries edges before _ => RowsLaw entries edges before)
      leafCase emptyCase ordinaryCase recursiveCase nilChildren unselectedCase selectedCase nilRows consCase ranges
  · intro entries offset values before ranges
    exact ChildrenRanges.rec (motive_1 := fun edits value before _ => NodeLaw edits value before)
      (motive_2 := fun entries offset values before _ => ChildrenLaw entries offset values before)
      (motive_3 := fun entries edges before _ => RowsLaw entries edges before)
      leafCase emptyCase ordinaryCase recursiveCase nilChildren unselectedCase selectedCase nilRows consCase ranges
  · intro entries edges before ranges
    exact RowsRanges.rec (motive_1 := fun edits value before _ => NodeLaw edits value before)
      (motive_2 := fun entries offset values before _ => ChildrenLaw entries offset values before)
      (motive_3 := fun entries edges before _ => RowsLaw entries edges before)
      leafCase emptyCase ordinaryCase recursiveCase nilChildren unselectedCase selectedCase nilRows consCase ranges

/-- Range checks derive finite actual node edits in the selected-path execution domain. -/
theorem node_complete {edits value before}
    (ranges : NodeRanges (width := width) emptyGuard conjoin clear top record originals edits value before)
    (populated : Populated edits) (nonempty : HasLeaf edits) (allowed : Allowed record edits)
    (ready : SourceCurrentMemoSharedTargetState.Ready emptyGuard conjoin clear top record originals base before)
    (available : Available before.native.machine.heap value) (safe : Safe edits value) :
    ∃ result after, EditNode emptyGuard conjoin clear top record originals edits value before result after ∧
      SourceCurrentMemoSharedTargetState.Ready emptyGuard conjoin clear top record originals base after ∧
      Keeps before.native.machine.heap after.native.machine.heap ∧ Available after.native.machine.heap result ∧ Transport value result := by
  obtain ⟨result, after, actual⟩ := (complete emptyGuard conjoin clear top record originals base known domains).1 _ _ _ ranges populated nonempty allowed ready available safe
  exact ⟨result, after, actual, node_domains emptyGuard conjoin clear top record originals base known domains actual populated nonempty allowed ready available safe⟩

/-- Range checks derive finite ordered child edits without closing unselected positions. -/
theorem children_complete {entries offset values before}
    (ranges : ChildrenRanges (width := width) emptyGuard conjoin clear top record originals entries offset values before)
    (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : SourceCurrentMemoSharedTargetState.Ready emptyGuard conjoin clear top record originals base before)
    (available : Values before.native.machine.heap values) (safe : ChildrenSafe entries offset values) :
    ∃ results after, EditChildren emptyGuard conjoin clear top record originals entries offset values before results after ∧
      SourceCurrentMemoSharedTargetState.Ready emptyGuard conjoin clear top record originals base after ∧
      Keeps before.native.machine.heap after.native.machine.heap ∧ Values after.native.machine.heap results ∧ All₂ Transport values results := by
  obtain ⟨results, after, actual⟩ := (complete emptyGuard conjoin clear top record originals base known domains).2.1 _ _ _ _ ranges populated allowed ready available safe
  exact ⟨results, after, actual, children_domains emptyGuard conjoin clear top record originals base known domains actual populated allowed ready available safe⟩

end MicroCFTA.SourceCurrentMemoSharedEditComplete
