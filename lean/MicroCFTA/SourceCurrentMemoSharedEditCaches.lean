import MicroCFTA.SourceCurrentMemoSharedEditDomains

/-!
# Language cache coverage through actual shared edits

Each selected leaf derives its completed merge entries from the actual target.
Intermediate physical states follow the selected path domain effects.
Constructor and head steps retain the completed merge table.
-/
namespace MicroCFTA.SourceCurrentMemoSharedEditCaches
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityNativeScoped
open SourceEqualityEdits SourceEqualityEditLeafPaths SourceEqualitySharedEditEffects
open SourceCurrentMemoSharedEditGraph SourceCurrentMemoSharedTargetState SourceCurrentEditDomains
open SourceEqualityProjectionPathDomain
open SourceCurrentMemoMergeLanguage (CacheCovers)

/-- Child-list callbacks do not inspect a root leaf token. -/
def ListSafe (edits : Edits Action) (values : List (Value Symbol Guard)) : Prop :=
  match edits with
  | .editAt _ => True
  | .editBelow entries => ChildrenSafe entries 0 values

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
variable (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
variable (base : InternedConstructorTemplates.State Symbol Guard) (known : Values base originals)
variable (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) originals)
variable (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
variable (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true)
variable (topTrue : ∀ term, holds top term = true)
variable (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))

private def NodeCovered (edits : Edits EqualityNormalize.Path) (value : Value Symbol Guard)
    (before after : SharedState width Symbol Guard) : Prop :=
  Populated edits → HasLeaf edits → Allowed record edits → Ready emptyGuard conjoin clear top record originals base before →
    Available before.native.machine.heap value → Safe edits value → CacheCovers holds ambient before.memo → CacheCovers holds ambient after.memo

private def ChildrenCovered (entries : List (Int × Edits EqualityNormalize.Path)) (offset : Nat) (values : List (Value Symbol Guard))
    (before after : SharedState width Symbol Guard) : Prop :=
  Populated (.editBelow entries) → Allowed record (.editBelow entries) → Ready emptyGuard conjoin clear top record originals base before →
    Values before.native.machine.heap values → ChildrenSafe entries offset values → CacheCovers holds ambient before.memo → CacheCovers holds ambient after.memo

private def RowsCovered (entries : List (Int × Edits EqualityNormalize.Path)) (edges : List (EdgeValue Symbol Guard))
    (before after : SharedState width Symbol Guard) : Prop :=
  Populated (.editBelow entries) → Allowed record (.editBelow entries) → Ready emptyGuard conjoin clear top record originals base before →
    Edges before.native.machine.heap edges → RowsSafe entries edges → CacheCovers holds ambient before.memo → CacheCovers holds ambient after.memo

local notation "NodeLaw" => NodeCovered (width := width) emptyGuard conjoin clear top record originals base holds ambient
local notation "ChildrenLaw" => ChildrenCovered (width := width) emptyGuard conjoin clear top record originals base holds ambient
local notation "RowsLaw" => RowsCovered (width := width) emptyGuard conjoin clear top record originals base holds ambient

include known domains clearTrue topTrue conjoined

private theorem covered :
    (∀ edits (value : Value Symbol Guard) before result after,
      EditNode emptyGuard conjoin clear top record originals edits value before result after → NodeLaw edits value before after) ∧
    (∀ entries offset (values : List (Value Symbol Guard)) before results after,
      EditChildren emptyGuard conjoin clear top record originals entries offset values before results after → ChildrenLaw entries offset values before after) ∧
    (∀ entries (edges : List (EdgeValue Symbol Guard)) before results after,
      EditRows emptyGuard conjoin clear top record originals entries edges before results after → RowsLaw entries edges before after) := by
  have leafCase : ∀ {path value before result after},
      SourceCurrentMemoSharedTargetLeaf.Leaf emptyGuard conjoin clear top record originals path value before result after →
      NodeLaw (.editAt path) value before after := by
    intro path value before result after trace _ _ allowed ready _ _ initial
    have member : path ∈ record.paths := by simpa only [Allowed, All] using allowed
    exact trace.covered ready known domains member holds ambient initial clearTrue topTrue conjoined
  have emptyCase : ∀ {entries state}, NodeLaw (.editBelow entries) (.empty : Value Symbol Guard) state state := by
    intro entries state _ _ _ _ _ _ initial
    exact initial
  have ordinaryCase : ∀ {entries edges before rebuilt middle value heap entry depth free},
      EditRows emptyGuard conjoin clear top record originals entries edges before rebuilt middle →
      run (makeNode rebuilt) middle.native.machine.heap = (value, heap) → RowsLaw entries edges before middle →
      NodeLaw (.editBelow entries) (.node entry edges depth free) before (advanceHeap middle heap) := by
    intro entries edges before rebuilt middle value heap entry depth free _ _ ih populated _ allowed ready available safe initial
    exact ih populated allowed ready
      (InternedEdgeResidency.resident_edges _ ready.native.semantic.ready.semantic.1.normal.facts.linked _ available.resident)
      (ordinary_rows safe) initial
  have recursiveCase : ∀ {entries original before exposed heap result after},
      SourceEqualityRequiredGraph.Recursive original → SourceEqualityRequiredHead.Head original before.native.machine.heap exposed heap →
      EditNode emptyGuard conjoin clear top record originals (.editBelow entries) exposed (advanceHeap before heap) result after →
      NodeLaw (.editBelow entries) exposed (advanceHeap before heap) after → NodeLaw (.editBelow entries) original before after := by
    intro entries original before exposed heap result after recursive head _ ih populated nonempty allowed ready available safe initial
    have closed := recursive_closed recursive nonempty safe
    have checked := head.verified ready.native.semantic.ready available closed
    have semantic := SourceEqualityRequiredSemanticCache.head head ready.native.semantic available closed
    have physical := SourceCurrentRequiredHeapEffects.head (fun _ => True) head ready.native.semantic ready.costs (fun _ _ _ => trivial) available
    exact ih populated nonempty allowed (ready.heap heap checked.1 semantic physical.2.2.1) checked.2.1
      (closed_safe _ exposed heap semantic checked.2.1 checked.2.2.1) initial
  have nilChildren : ∀ {entries offset state}, ChildrenLaw entries offset ([] : List (Value Symbol Guard)) state state := by
    intro entries offset state _ _ _ _ _ initial
    exact initial
  have unselectedCase : ∀ {entries values before results after value} (offset : Nat),
      SourceEqualityNeededMap.lookup (offset : Int) entries = none →
      EditChildren emptyGuard conjoin clear top record originals entries (offset + 1) values before results after →
      ChildrenLaw entries (offset + 1) values before after → ChildrenLaw entries offset (value :: values) before after := by
    intro entries values before results after value offset _ _ ih populated allowed ready available safe initial
    exact ih populated allowed ready (fun original member => available original (List.mem_cons_of_mem _ member)) (children_tail safe) initial
  have selectedCase : ∀ {entries edits value before result middle values results after} (offset : Nat),
      SourceEqualityNeededMap.lookup (offset : Int) entries = some edits →
      EditNode emptyGuard conjoin clear top record originals edits value before result middle →
      EditChildren emptyGuard conjoin clear top record originals entries (offset + 1) values middle results after →
      NodeLaw edits value before middle → ChildrenLaw entries (offset + 1) values middle after →
      ChildrenLaw entries offset (value :: values) before after := by
    intro entries edits value before result middle values results after offset found first _ firstIH restIH populated allowed ready available safe initial
    have member := SourceEqualityNeededMap.lookup_mem _ _ _ found
    have childPopulated := (show ∀ index child, (index, child) ∈ entries → Populated child ∧ HasLeaf child from
      by simpa only [Populated] using populated) _ _ member
    have childAllowed : Allowed record edits := by rw [Allowed, All] at allowed; exact allowed _ _ member
    have childSafe := safe 0 _ (by simpa using found) value rfl
    have checked := SourceCurrentMemoSharedEditDomains.node_domains emptyGuard conjoin clear top record originals base known domains first
      childPopulated.1 childPopulated.2 childAllowed ready (available _ List.mem_cons_self) childSafe
    have current := firstIH childPopulated.1 childPopulated.2 childAllowed ready (available _ List.mem_cons_self) childSafe initial
    exact restIH populated allowed checked.1
      (fun original member => checked.2.1.available original (available original (List.mem_cons_of_mem _ member))) (children_tail safe) current
  have nilRows : ∀ {entries state}, RowsLaw entries ([] : List (EdgeValue Symbol Guard)) state state := by
    intro entries state _ _ _ _ _ initial
    exact initial
  have consCase : ∀ {entries before values middle result heap edges results after edge},
      EditChildren emptyGuard conjoin clear top record originals entries 0 edge.children before values middle →
      run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.native.machine.heap = (result, heap) →
      EditRows emptyGuard conjoin clear top record originals entries edges (advanceHeap middle heap) results after →
      ChildrenLaw entries 0 edge.children before middle → RowsLaw entries edges (advanceHeap middle heap) after →
      RowsLaw entries (edge :: edges) before after := by
    intro entries before values middle result heap edges results after edge children built _ firstIH restIH populated allowed ready resident safe initial
    have available := ready.native.semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident _ List.mem_cons_self)
    have first := SourceCurrentMemoSharedEditDomains.children_domains emptyGuard conjoin clear top record originals base known domains children
      populated allowed ready available (safe _ List.mem_cons_self)
    have current := firstIH populated allowed ready available (safe _ List.mem_cons_self) initial
    have rebuilt := SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle.native.machine.heap
      first.1.native.semantic.ready first.2.2.1
    have semantic := SourceEqualityRequiredSemanticCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle.native.machine.heap
      first.1.native.semantic first.2.2.1
    have edgeKept : Keeps middle.native.machine.heap heap := by simpa only [built] using rebuilt.1
    have edgeSemantic : SemanticReady heap := by simpa only [built] using semantic
    have firstKept := first.2.1.trans edgeKept
    exact restIH populated allowed (first.1.heap heap edgeKept edgeSemantic (by
      have costs : InternedFreshOrdinaryCostHeap.Heap (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.native.machine.heap).2 := first.1.costs
      simpa only [built] using costs))
      (fun original member => InternedEdgeResidency.edge_grows _ _ firstKept.growth original (resident original (List.mem_cons_of_mem _ member)))
      (fun original member => safe original (List.mem_cons_of_mem _ member)) current
  refine ⟨?_, ?_, ?_⟩
  · intro edits value before result after trace
    exact EditNode.rec (motive_1 := fun edits value before result after _ => NodeLaw edits value before after)
      (motive_2 := fun entries offset values before results after _ => ChildrenLaw entries offset values before after)
      (motive_3 := fun entries edges before results after _ => RowsLaw entries edges before after)
      leafCase emptyCase ordinaryCase recursiveCase nilChildren unselectedCase selectedCase nilRows consCase trace
  · intro entries offset values before results after trace
    exact EditChildren.rec (motive_1 := fun edits value before result after _ => NodeLaw edits value before after)
      (motive_2 := fun entries offset values before results after _ => ChildrenLaw entries offset values before after)
      (motive_3 := fun entries edges before results after _ => RowsLaw entries edges before after)
      leafCase emptyCase ordinaryCase recursiveCase nilChildren unselectedCase selectedCase nilRows consCase trace
  · intro entries edges before results after trace
    exact EditRows.rec (motive_1 := fun edits value before result after _ => NodeLaw edits value before after)
      (motive_2 := fun entries offset values before results after _ => ChildrenLaw entries offset values before after)
      (motive_3 := fun entries edges before results after _ => RowsLaw entries edges before after)
      leafCase emptyCase ordinaryCase recursiveCase nilChildren unselectedCase selectedCase nilRows consCase trace

/-- Actual node edits derive coverage at their returned completed merge table. -/
theorem node_covered {edits value before result after}
    (actual : EditNode (width := width) emptyGuard conjoin clear top record originals edits value before result after) :
    NodeLaw edits value before after :=
  (covered emptyGuard conjoin clear top record originals base known domains holds ambient clearTrue topTrue conjoined).1 _ _ _ _ _ actual

/-- Ordered child edits pass the derived cache coverage to the next selected subtree. -/
theorem children_covered {entries offset values before results after}
    (actual : EditChildren (width := width) emptyGuard conjoin clear top record originals entries offset values before results after) :
    ChildrenLaw entries offset values before after :=
  (covered emptyGuard conjoin clear top record originals base known domains holds ambient clearTrue topTrue conjoined).2.1 _ _ _ _ _ _ actual

/-- Ordered row edits retain cache coverage through their actual constructor states. -/
theorem rows_covered {entries edges before results after}
    (actual : EditRows (width := width) emptyGuard conjoin clear top record originals entries edges before results after) :
    RowsLaw entries edges before after :=
  (covered emptyGuard conjoin clear top record originals base known domains holds ambient clearTrue topTrue conjoined).2.2 _ _ _ _ _ actual

/-- Source list edits ignore root callbacks and derive coverage for below edits. -/
theorem list_covered {edits values before results after}
    (actual : EditList (width := width) emptyGuard conjoin clear top record originals edits values before results after)
    (populated : Populated edits) (allowed : Allowed record edits)
    (ready : Ready emptyGuard conjoin clear top record originals base before) (available : Values before.native.machine.heap values)
    (safe : ListSafe edits values)
    (initial : CacheCovers holds ambient before.memo) : CacheCovers holds ambient after.memo := by
  cases actual with
  | leaf => exact initial
  | children actual =>
      exact children_covered emptyGuard conjoin clear top record originals base known domains holds ambient clearTrue topTrue conjoined
        actual populated allowed ready available safe initial

end MicroCFTA.SourceCurrentMemoSharedEditCaches
