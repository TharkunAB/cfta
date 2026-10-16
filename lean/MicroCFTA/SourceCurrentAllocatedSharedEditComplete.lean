import MicroCFTA.SourceCurrentAllocatedSharedEditEffects
import MicroCFTA.SourceCurrentAllocatedSharedEditRanges

/-!
# Finite checked class edits from actual-prefix ranges

The finite trie constructs each leaf, recursive head, and later child call.
Each actual returned inventory and global bundle enters the next call.
Unselected ordinary siblings can remain open.
-/
namespace MicroCFTA.SourceCurrentAllocatedSharedEditComplete
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityEdits SourceEqualityEditLeafPaths SourceEqualityProjectionPathDomain
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentEditDomains SourceCurrentAllocatedSharedEditGraph
open SourceCurrentAllocatedSharedEditRanges SourceCurrentAllocatedSharedEditEffects
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "HeapState" => InternedConstructorTemplates.State Symbol Guard
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
variable (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) (base : HeapState)

private def NodeComplete (edits : Edits EqualityNormalize.Path) (value : Value Symbol Guard)
    (before : SharedState width) : Prop :=
  Populated edits → HasLeaf edits → Allowed record edits → ∀ inventory,
    Ready formulas solver inventory record originals base before →
    Available before.checked.native.machine.heap value → Safe edits value →
    ∀ memos, Valid before.checked.native.machine.heap memos →
      ∃ result after final, ∃ actual : EditNode record originals edits value before result after,
        NodeReads formulas solver base actual memos final

private def ChildrenComplete (entries : List (Int × Edits EqualityNormalize.Path)) (offset : Nat)
    (values : List (Value Symbol Guard)) (before : SharedState width) : Prop :=
  Populated (.editBelow entries) → Allowed record (.editBelow entries) → ∀ inventory,
    Ready formulas solver inventory record originals base before →
    Values before.checked.native.machine.heap values → ChildrenSafe entries offset values →
    ∀ memos, Valid before.checked.native.machine.heap memos →
      ∃ results after final, ∃ actual : EditChildren record originals entries offset values before results after,
        ChildrenReads formulas solver base actual memos final

private def RowsComplete (entries : List (Int × Edits EqualityNormalize.Path))
    (edges : List (EdgeValue Symbol Guard)) (before : SharedState width) : Prop :=
  Populated (.editBelow entries) → Allowed record (.editBelow entries) → ∀ inventory,
    Ready formulas solver inventory record originals base before →
    Edges before.checked.native.machine.heap edges → RowsSafe entries edges →
    ∀ memos, Valid before.checked.native.machine.heap memos →
      ∃ results after final, ∃ actual : EditRows record originals entries edges before results after,
        RowsReads formulas solver base actual memos final

local notation "NodeLaw" => NodeComplete (width := width) formulas solver record originals base
local notation "ChildrenLaw" => ChildrenComplete (width := width) formulas solver record originals base
local notation "RowsLaw" => RowsComplete (width := width) formulas solver record originals base
variable (known : Values base originals)
variable (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) originals)
variable (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)

include known domains coherent active

private theorem complete :
    (∀ edits (value : Value Symbol Guard) before,
      NodeRanges record originals edits value before → NodeLaw edits value before) ∧
    (∀ entries offset (values : List (Value Symbol Guard)) before,
      ChildrenRanges record originals entries offset values before → ChildrenLaw entries offset values before) ∧
    (∀ entries (edges : List (EdgeValue Symbol Guard)) before,
      RowsRanges record originals entries edges before → RowsLaw entries edges before) := by
  have leafCase : ∀ {path value before},
      SourceCurrentAllocatedSharedTargetLeaf.Ranges record originals path value before →
      NodeLaw (.editAt path) value before := by
    intro path value before ranges _ _ allowed inventory ready available safe memos valid
    have member : path ∈ record.paths := by simpa only [Allowed, All] using allowed
    have closed : value.free = [] := by simpa only [NodeClosed] using safe [] path (by simp [leaves])
    obtain ⟨result, after, next, final, receipt⟩ := SourceCurrentAllocatedSharedTargetLeaf.complete
      formulas solver inventory record originals base before ready known domains coherent active path member value
      available closed ranges memos valid
    exact ⟨result, after, final, .leaf receipt.actual, .leaf receipt⟩
  have emptyCase : ∀ {entries before}, NodeLaw (.editBelow entries) (.empty : Value Symbol Guard) before := by
    intro entries before _ _ _ _ _ _ _ memos _
    exact ⟨_, _, memos, .empty, .empty⟩
  have ordinaryCase : ∀ {entries edges before entry depth free},
      RowsRanges record originals entries edges before → RowsLaw entries edges before →
      NodeLaw (.editBelow entries) (.node entry edges depth free) before := by
    intro entries edges before entry depth free _ ih populated _ allowed inventory ready available safe memos valid
    have facts := ready.checked.semantic.ready.semantic.1.normal.facts
    obtain ⟨rebuilt, middle, final, actual, reads⟩ := ih populated allowed inventory ready
      (InternedEdgeResidency.resident_edges _ facts.linked _ available.resident) (ordinary_rows safe) memos valid
    exact ⟨_, _, final, .ordinary actual rfl, .ordinary (actual := actual) (built := rfl) reads⟩
  have recursiveCase : ∀ {original entries before}, SourceEqualityRequiredGraph.Recursive original →
      (∀ exposed heap, SourceEqualityRequiredHead.Head original before.checked.native.machine.heap exposed heap →
        NodeRanges record originals (.editBelow entries) exposed (advanceHeap before heap)) →
      (∀ exposed heap, SourceEqualityRequiredHead.Head original before.checked.native.machine.heap exposed heap →
        NodeLaw (.editBelow entries) exposed (advanceHeap before heap)) → NodeLaw (.editBelow entries) original before := by
    intro original entries before recursive _ ih populated nonempty allowed inventory ready available safe memos valid
    have closed := recursive_closed recursive nonempty safe
    obtain ⟨exposed, heap, head, _, exposedAvailable, exposedClosed, _⟩ :=
      SourceEqualityRequiredHead.complete original before.checked.native.machine.heap ready.checked.semantic.ready available closed
    have physical := head_physical ready head available
    obtain ⟨current, headRead, headValid, retained, queries⟩ := SourceCurrentRequiredQueryMemos.head_memos
      head ready.checked.semantic ready.checked.costs available memos valid
    have headGlobal : SourceCurrentSubsumesQueryMemos.Effect before.checked.native.machine.heap heap memos current :=
      ⟨physical.2.1.keeps, physical.1.checked.semantic, physical.1.checked.costs, headValid, retained, queries⟩
    obtain ⟨result, after, final, body, reads⟩ := ih exposed heap head populated nonempty allowed inventory physical.1
      exposedAvailable (closed_safe _ exposed heap physical.1.checked.semantic exposedAvailable exposedClosed) current headValid
    exact ⟨result, after, final, .recursive recursive head body,
      .recursive (recursive := recursive) (head := head) (body := body) headRead headGlobal reads⟩
  have nilChildren : ∀ {entries offset before}, ChildrenLaw entries offset ([] : List (Value Symbol Guard)) before := by
    intro entries offset before _ _ _ _ _ _ memos _
    exact ⟨_, _, memos, .nil, .nil⟩
  have unselectedCase : ∀ {entries values before value} (offset : Nat),
      SourceEqualityNeededMap.lookup (offset : Int) entries = none →
      ChildrenRanges record originals entries (offset + 1) values before →
      ChildrenLaw entries (offset + 1) values before → ChildrenLaw entries offset (value :: values) before := by
    intro entries values before value offset absent _ ih populated allowed inventory ready available safe memos valid
    obtain ⟨results, after, final, rest, reads⟩ := ih populated allowed inventory ready
      (fun original member => available original (List.mem_cons_of_mem _ member)) (children_tail safe) memos valid
    exact ⟨_, _, final, .unselected offset absent rest, .unselected (absent := absent) (rest := rest) reads⟩
  have selectedCase : ∀ {entries edits value before values} (offset : Nat),
      SourceEqualityNeededMap.lookup (offset : Int) entries = some edits →
      NodeRanges record originals edits value before →
      (∀ result middle, EditNode record originals edits value before result middle →
        ChildrenRanges record originals entries (offset + 1) values middle) →
      NodeLaw edits value before →
      (∀ result middle, EditNode record originals edits value before result middle →
        ChildrenLaw entries (offset + 1) values middle) → ChildrenLaw entries offset (value :: values) before := by
    intro entries edits value before values offset found _ _ firstIH restIH populated allowed inventory ready available safe memos valid
    have member := SourceEqualityNeededMap.lookup_mem _ _ _ found
    have childPopulated := (show ∀ index child, (index, child) ∈ entries → Populated child ∧ HasLeaf child from
      by simpa only [Populated] using populated) _ _ member
    have childAllowed : Allowed record edits := by rw [Allowed, All] at allowed; exact allowed _ _ member
    have firstSafe := safe 0 _ (by simpa using found) value rfl
    obtain ⟨result, middle, current, first, firstRead⟩ := firstIH childPopulated.1 childPopulated.2 childAllowed inventory ready
      (available _ List.mem_cons_self) firstSafe memos valid
    obtain ⟨next, checked⟩ := node_effects firstRead childPopulated.1 childPopulated.2 childAllowed ready
      (available _ List.mem_cons_self) firstSafe valid
    obtain ⟨results, after, final, rest, restRead⟩ := restIH result middle first populated allowed next checked.ready
      (fun original member => checked.effects.keeps.available original (available original (List.mem_cons_of_mem _ member)))
      (children_tail safe) current checked.globals.valid
    exact ⟨_, _, final, .selected offset found first rest,
      .selected (found := found) (first := first) (rest := rest) firstRead restRead⟩
  have nilRows : ∀ {entries before}, RowsLaw entries ([] : List (EdgeValue Symbol Guard)) before := by
    intro entries before _ _ _ _ _ _ memos _
    exact ⟨_, _, memos, .nil, .nil⟩
  have consCase : ∀ {entries edges before} {edge : EdgeValue Symbol Guard},
      ChildrenRanges record originals entries 0 edge.children before →
      (∀ values middle, EditChildren record originals entries 0 edge.children before values middle →
        RowsRanges record originals entries edges
          (advanceHeap middle (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.checked.native.machine.heap).2)) →
      ChildrenLaw entries 0 edge.children before →
      (∀ values middle, EditChildren record originals entries 0 edge.children before values middle →
        RowsLaw entries edges (advanceHeap middle (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.checked.native.machine.heap).2)) →
      RowsLaw entries (edge :: edges) before := by
    intro entries edges before edge _ _ firstIH restIH populated allowed inventory ready resident safe memos valid
    have original := resident edge List.mem_cons_self
    have available := ready.checked.semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge original
    obtain ⟨values, middle, current, children, reads⟩ := firstIH populated allowed inventory ready available (safe _ List.mem_cons_self) memos valid
    obtain ⟨next, checked⟩ := children_effects reads populated allowed ready available (safe _ List.mem_cons_self) valid
    have field := (ready.checked.good.fields edge.entry.key edge original).grows checked.effects.grows
    have built := edge_physical checked.ready edge.entry.key.symbol edge.entry.key.constraint values field checked.available
    have globalValid := SourceQueryUnfoldMemo.valid_grows middle.checked.native.machine.heap _ checked.ready.checked.semantic
      built.2.1.keeps current checked.globals.valid
    have kept := checked.effects.keeps.trans built.2.1.keeps
    obtain ⟨results, after, final, rest, restReads⟩ := restIH values middle children populated allowed next built.1
      (fun original member => InternedEdgeResidency.edge_grows _ _ kept.growth original (resident original (List.mem_cons_of_mem _ member)))
      (fun original member => safe original (List.mem_cons_of_mem _ member)) current globalValid
    exact ⟨_, _, final, .cons children rfl rest, .cons (children := children) (rebuilt := rfl) (rest := rest) reads restReads⟩
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

/-- Reached ranges construct finite node edits and derive their actual returned inventory. -/
theorem node_complete (inventory : Inventory) {edits value before}
    (ranges : NodeRanges (width := width) record originals edits value before)
    (populated : Populated edits) (nonempty : HasLeaf edits) (allowed : Allowed record edits)
    (ready : Ready formulas solver inventory record originals base before)
    (available : Available before.checked.native.machine.heap value) (safe : Safe edits value)
    (memos : Memos) (valid : Valid before.checked.native.machine.heap memos) :
    ∃ result after next final, ∃ actual : EditNode record originals edits value before result after,
      NodeReads formulas solver base actual memos final ∧
      NodeReceipt formulas solver next record originals base value before result after memos final := by
  obtain ⟨result, after, final, actual, reads⟩ := (complete formulas solver record originals base known domains coherent active).1
    _ _ _ ranges populated nonempty allowed inventory ready available safe memos valid
  obtain ⟨next, receipt⟩ := node_effects reads populated nonempty allowed ready available safe valid
  exact ⟨result, after, next, final, actual, reads, receipt⟩

/-- Ordered child completion retains each actual generated inventory and all earlier slots. -/
theorem children_complete (inventory : Inventory) {entries offset values before}
    (ranges : ChildrenRanges (width := width) record originals entries offset values before)
    (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : Ready formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap values) (safe : ChildrenSafe entries offset values)
    (memos : Memos) (valid : Valid before.checked.native.machine.heap memos) :
    ∃ results after next final, ∃ actual : EditChildren record originals entries offset values before results after,
      ChildrenReads formulas solver base actual memos final ∧
      ChildrenReceipt formulas solver next record originals base values before results after memos final := by
  obtain ⟨results, after, final, actual, reads⟩ := (complete formulas solver record originals base known domains coherent active).2.1
    _ _ _ _ ranges populated allowed inventory ready available safe memos valid
  obtain ⟨next, receipt⟩ := children_effects reads populated allowed ready available safe valid
  exact ⟨results, after, next, final, actual, reads, receipt⟩

/-- The list root ignores a callback and constructs all actual below-edits otherwise. -/
theorem list_complete (inventory : Inventory) {edits values before}
    (ranges : ListRanges (width := width) record originals edits values before)
    (populated : Populated edits) (allowed : Allowed record edits)
    (ready : Ready formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap values) (safe : ListSafe edits values)
    (memos : Memos) (valid : Valid before.checked.native.machine.heap memos) :
    ∃ results after next final, ∃ actual : EditList record originals edits values before results after,
      ListReads formulas solver base actual memos final ∧
      ChildrenReceipt formulas solver next record originals base values before results after memos final := by
  cases edits with
  | editAt target =>
      have reads : ListReads formulas solver base (EditList.leaf (record := record) (originals := originals)
        (target := target) (values := values) (state := before)) memos memos := .leaf
      obtain ⟨next, receipt⟩ := list_effects reads populated allowed ready available safe valid
      exact ⟨values, before, next, memos, .leaf, reads, receipt⟩
  | editBelow entries =>
      obtain ⟨results, after, next, final, actual, reads, receipt⟩ := children_complete
        formulas solver record originals base known domains coherent active inventory ranges populated allowed ready available safe memos valid
      exact ⟨results, after, next, final, .children actual, .children reads, receipt⟩

end MicroCFTA.SourceCurrentAllocatedSharedEditComplete
