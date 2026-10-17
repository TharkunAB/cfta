import MicroCFTA.SourceCurrentRequiredExposureSafe
import MicroCFTA.SourceCurrentRequiredGuardOrigins
import MicroCFTA.SourceCurrentRequiredGuard

/-!
# Indexed structural guard origins through selected Required reads

An unchanged subtree keeps its original structural positions. An accepted
recursive exposure has only plain rows. Ordinary reconstruction maps each
returned row to an indexed original row and relates its ordered children.
Normalization can remove or reorder rows. The origin map is not injective.
These results verify actual completed reads. They do not assert progress.
-/
namespace MicroCFTA.SourceCurrentRequiredRowOrigins
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceEqualityNeeded SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityRequiredGraph
open SourceEqualityAnnotationLanguage
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Heap" => State Symbol Guard
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- An output retains an unchanged subtree, a zero-origin region, or indexed ordinary row origins. -/
inductive Origin : Node → Node → Prop where
  /-- An uninspected subtree retains every structural occurrence. -/
  | identity (value : Node) : Origin value value
  /-- A plain returned region contains no positive equality-row occurrence. -/
  | plain (original result : Node) (annotated : Annotated Plain result) : Origin original result
  /-- Each output root row names an original row and retains all ordered child origins. -/
  | ordinary (entry) (originals : List Edge) (level free) (result : Node)
      (ordinary : SourceEqualityRequiredCache.Ordinary result)
      (rows : ∀ index output, (nodeEdges result)[index]? = some output →
        ∃ sourceIndex original, originals[sourceIndex]? = some original ∧
          SourceCurrentRequiredGuardOrigins.RowOrigin original output ∧
          All₂ Origin original.children output.children) :
      Origin (.node entry originals level free) result

/-- Selected existing children retain their own initial requirement at the actual offset. -/
def ChildrenSafe (entries : List (Int × Needed)) (index : Nat) (values : List Node) : Prop :=
  ∀ offset needed, SourceEqualityNeededMap.lookup (Int.ofNat (index + offset)) entries = some needed →
    ∀ value, values[offset]? = some value → ExposureSafe needed value

/-- Each original row checks its selected existing children from offset zero. -/
def RowsSafe (entries : List (Int × Needed)) (rows : List Edge) : Prop :=
  ∀ row ∈ rows, ChildrenSafe entries 0 row.children

private theorem safe_tail {entries index value values}
    (safe : ChildrenSafe entries index (value :: values)) : ChildrenSafe entries (index + 1) values := by
  intro offset needed found child selected
  exact safe (offset + 1) needed (by simpa only [Nat.add_assoc, Nat.add_comm 1] using found) child
    (by simpa only [List.getElem?_cons_succ] using selected)

private def RowsOrigin (originals results : List Edge) : Prop :=
  ∀ output ∈ results, ∃ original ∈ originals,
    SourceCurrentRequiredGuardOrigins.RowOrigin original output ∧ All₂ Origin original.children output.children

private def NodeResult (needed : Needed) (value : Node) (before : Heap) (result : Node) (_after : Heap) : Prop :=
  SemanticReady before → CostHeap before → Available before value → GuardHeap Plain before →
    ExposureSafe needed value → Origin value result
private def ChildrenResult (entries : List (Int × Needed)) (index : Nat) (values : List Node)
    (before : Heap) (results : List Node) (_after : Heap) : Prop :=
  SemanticReady before → CostHeap before → Values before values → GuardHeap Plain before →
    ChildrenSafe entries index values → All₂ Origin values results
private def RowsResult (entries : List (Int × Needed)) (rows : List Edge)
    (before : Heap) (results : List Edge) (_after : Heap) : Prop :=
  SemanticReady before → CostHeap before → Edges before rows → GuardHeap Plain before →
    RowsSafe entries rows → RowsOrigin rows results

variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem accepted {needed value result before after}
    (actual : RequireNode needed value before result after) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Available before value) (guards : GuardHeap Plain before)
    (plain : SourceMemoGate.unconstrained value = true) : Origin value result :=
  .plain value result (SourceCurrentRequiredGuardOrigins.accepted_node actual semantic costs available guards plain).2.1

private theorem all_required :
    (∀ needed value before result after, RequireNode needed value before result after → NodeResult needed value before result after) ∧
    (∀ entries index values before results after, RequireChildren entries index values before results after → ChildrenResult entries index values before results after) ∧
    (∀ entries rows before results after, RequireRows entries rows before results after → RowsResult entries rows before results after) := by
  have identityCase : ∀ {value state}, NodeResult (.node []) value state value state := by
    intro value state _ _ _ _ _
    exact .identity value
  have emptyCase : ∀ {entries state}, entries ≠ [] → NodeResult (.node entries) .empty state .empty state := by
    intro entries state _ _ _ _ _ _
    exact .identity .empty
  have ordinaryCase : ∀ {entries edges before rebuilt middle result after entry level free},
      entries ≠ [] → RequireRows entries edges before rebuilt middle → run (makeNode rebuilt) middle = (result, after) →
      RowsResult entries edges before rebuilt middle → NodeResult (.node entries) (.node entry edges level free) before result after := by
    intro entries edges before rebuilt middle result after entry level free nonempty rows built ih semantic costs available guards safe
    cases safe with
    | identity => exact False.elim (nonempty rfl)
    | accepted needed value plain => exact accepted (.ordinary nonempty rows built) semantic costs available guards plain
    | ordinary entries entry edges level free children =>
        have resident := resident_edges before semantic.ready.semantic.1.normal.facts.linked _ available.resident
        have origins := ih semantic costs resident guards (fun edge member offset needed found child selected =>
          children edge member offset needed (by simpa only [Nat.zero_add] using found) child selected)
        have effects := SourceCurrentRequiredHeapEffects.rows (fun _ => True) rows semantic costs (fun _ _ _ => trivial) resident
        have fields := EqualityLeafProjectionPhysical.makeNode_edges rebuilt middle
          effects.2.1.ready.semantic.1.normal.facts.coherent effects.2.1.ready.semantic.1.normal.facts.linked effects.2.2.2.2
        have ordinary := SourceEqualityRequiredCache.node_ordinary rebuilt middle
          effects.2.1.ready.semantic.1.normal.facts effects.2.2.2.2
        refine .ordinary entry edges level free result (by simpa only [built] using ordinary) ?_
        intro index output selected
        have included : output ∈ nodeEdges (run (makeNode rebuilt) middle).1 := by
          simpa only [built] using List.mem_of_getElem? selected
        have normalized : output ∈ canonicalEdges (surviving rebuilt) := fields ▸ included
        obtain ⟨original, member, origin, children⟩ := origins output
          (List.mem_filter.mp (canonicalEdges_member _ output normalized)).1
        obtain ⟨sourceIndex, sourceFound⟩ := List.mem_iff_getElem?.mp member
        exact ⟨sourceIndex, original, sourceFound, origin, children⟩
  have recursiveCase : ∀ {entries original before exposed middle result after}, entries ≠ [] → Recursive original →
      SourceEqualityRequiredHead.Head original before exposed middle → RequireNode (.node entries) exposed middle result after →
      NodeResult (.node entries) exposed middle result after → NodeResult (.node entries) original before result after := by
    intro entries original before exposed middle result after nonempty recursive head body ih semantic costs available guards safe
    cases safe with
    | identity => exact False.elim (nonempty rfl)
    | empty => cases recursive
    | ordinary => cases recursive
    | accepted needed value plain => exact accepted (.recursive nonempty recursive head body) semantic costs available guards plain
  have nilChildren : ∀ {entries index state}, ChildrenResult entries index [] state [] state := by
    intro entries index state _ _ _ _ _
    exact .nil
  have unselectedCase : ∀ {entries values before results after value} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = none → RequireChildren entries (index + 1) values before results after →
      ChildrenResult entries (index + 1) values before results after → ChildrenResult entries index (value :: values) before (value :: results) after := by
    intro entries values before results after value index absent rest ih semantic costs available guards safe
    exact .cons (.identity value) (ih semantic costs (fun child member => available child (List.mem_cons_of_mem _ member)) guards (safe_tail safe))
  have selectedCase : ∀ {entries needed value before result middle values results after} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = some needed → RequireNode needed value before result middle →
      RequireChildren entries (index + 1) values middle results after → NodeResult needed value before result middle →
      ChildrenResult entries (index + 1) values middle results after → ChildrenResult entries index (value :: values) before (result :: results) after := by
    intro entries needed value before result middle values results after index found first rest firstIH restIH semantic costs available guards safe
    have firstAvailable := available value List.mem_cons_self
    have firstSafe := safe 0 needed (by simpa only [Nat.add_zero] using found) value rfl
    have firstOrigin := firstIH semantic costs firstAvailable guards firstSafe
    have effects := SourceCurrentRequiredHeapEffects.node (fun _ => True) first semantic costs (fun _ _ _ => trivial) firstAvailable
    have middleGuards := SourceCurrentRequiredGuard.node Plain first semantic costs firstAvailable guards
    have later := restIH effects.2.1 effects.2.2.1
      (fun child member => effects.1.available child (available child (List.mem_cons_of_mem _ member))) middleGuards (safe_tail safe)
    exact .cons firstOrigin later
  have nilRows : ∀ {entries state}, RowsResult entries [] state [] state := by
    intro entries state _ _ _ _ _ output impossible
    cases impossible
  have rejectedCase : ∀ {entries edges before results after edge}, fits (.node entries) edge.children.length = false →
      RequireRows entries edges before results after → RowsResult entries edges before results after →
      RowsResult entries (edge :: edges) before results after := by
    intro entries edges before results after edge rejected rest ih semantic costs resident guards safe output member
    obtain ⟨original, included, origin⟩ := ih semantic costs
      (fun row member => resident row (List.mem_cons_of_mem _ member)) guards
      (fun row member => safe row (List.mem_cons_of_mem _ member)) output member
    exact ⟨original, List.mem_cons_of_mem _ included, origin⟩
  have keptCase : ∀ {entries before values middle result afterEdge edges results after edge},
      fits (.node entries) edge.children.length = true → RequireChildren entries 0 edge.children before values middle →
      run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle = (result, afterEdge) →
      RequireRows entries edges afterEdge results after → ChildrenResult entries 0 edge.children before values middle →
      RowsResult entries edges afterEdge results after → RowsResult entries (edge :: edges) before (result :: results) after := by
    intro entries before values middle result afterEdge edges results after edge fits children built rest childIH restIH semantic costs resident guards safe
    have available : Values before edge.children := semantic.ready.semantic.1.normal.facts.cached.edges
      edge.entry.key edge (resident edge List.mem_cons_self)
    have origins := childIH semantic costs available guards (safe edge List.mem_cons_self)
    have effects := SourceCurrentRequiredHeapEffects.children (fun _ => True) children semantic costs (fun _ _ _ => trivial) available
    have middleGuards := SourceCurrentRequiredGuard.children Plain children semantic costs available guards
    have fields := MergedPhysicalGroupEdges.makeEdge_fields middle effects.2.1.ready.semantic.1.normal.facts
      edge.entry.key.symbol edge.entry.key.constraint values effects.2.2.2.2
    have exactChildren : result.children = values := by simpa only [built] using fields.2.2
    have rowOrigin : SourceCurrentRequiredGuardOrigins.RowOrigin edge result :=
      ⟨by simpa only [built] using fields.2.1, by simpa only [built] using fields.1,
        exactChildren ▸ children.length⟩
    have resultOrigins : All₂ Origin edge.children result.children := by simpa only [exactChildren] using origins
    have next := SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle effects.2.1.ready effects.2.2.2.2
    have afterKept : Keeps middle afterEdge := by simpa only [built] using next.1
    have afterSemantic : SemanticReady afterEdge := by
      simpa only [built] using SourceEqualityRequiredSemanticCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle effects.2.1 effects.2.2.2.2
    have afterCosts : CostHeap afterEdge := by
      simpa only [built] using (show CostHeap (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle).2 from effects.2.2.1)
    have afterGuards : GuardHeap Plain afterEdge := by
      simpa only [built] using SourceCurrentConstrainedCapGuardHeap.preserve Plain middle
        (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle).2 middleGuards
        (InternedShallowHeap.makeEdge_noNewMu edge.entry.key.symbol edge.entry.key.constraint values middle)
    have later := restIH afterSemantic afterCosts
      (fun row member => edge_grows before afterEdge (effects.1.trans afterKept).growth row (resident row (List.mem_cons_of_mem _ member))) afterGuards
      (fun row member => safe row (List.mem_cons_of_mem _ member))
    intro output member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨edge, List.mem_cons_self, rowOrigin, resultOrigins⟩
    · obtain ⟨original, included, origin⟩ := later output member
      exact ⟨original, List.mem_cons_of_mem _ included, origin⟩
  refine ⟨?_, ?_, ?_⟩
  · intro needed value before result after actual
    exact RequireNode.rec (motive_1 := fun needed value before result after _ => NodeResult needed value before result after)
      (motive_2 := fun entries index values before results after _ => ChildrenResult entries index values before results after)
      (motive_3 := fun entries rows before results after _ => RowsResult entries rows before results after)
      identityCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) rejectedCase keptCase actual
  · intro entries index values before results after actual
    exact RequireChildren.rec (motive_1 := fun needed value before result after _ => NodeResult needed value before result after)
      (motive_2 := fun entries index values before results after _ => ChildrenResult entries index values before results after)
      (motive_3 := fun entries rows before results after _ => RowsResult entries rows before results after)
      identityCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) rejectedCase keptCase actual
  · intro entries rows before results after actual
    exact RequireRows.rec (motive_1 := fun needed value before result after _ => NodeResult needed value before result after)
      (motive_2 := fun entries index values before results after _ => ChildrenResult entries index values before results after)
      (motive_3 := fun entries rows before results after _ => RowsResult entries rows before results after)
      identityCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) rejectedCase keptCase actual

/-- Actual Required maps every returned row and child to its initial structural origin or a plain region. -/
theorem node {needed value result before after}
    (actual : RequireNode needed value before result after) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before value) (guards : GuardHeap Plain before) (safe : ExposureSafe needed value) :
    Origin value result := all_required.1 _ _ _ _ _ actual semantic costs available guards safe

/-- Actual ordered child calls retain an origin relation at every original position. -/
theorem children {entries index values results before after}
    (actual : RequireChildren entries index values before results after) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (guards : GuardHeap Plain before) (safe : ChildrenSafe entries index values) :
    All₂ Origin values results := all_required.2.1 _ _ _ _ _ _ actual semantic costs available guards safe

/-- Each actual returned row names an original indexed row with the same guard and ordered child origins. -/
theorem rows {entries originals results before after}
    (actual : RequireRows entries originals before results after) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before originals) (guards : GuardHeap Plain before) (safe : RowsSafe entries originals) :
    ∀ index output, results[index]? = some output → ∃ sourceIndex original, originals[sourceIndex]? = some original ∧
      SourceCurrentRequiredGuardOrigins.RowOrigin original output ∧ All₂ Origin original.children output.children := by
  intro index output selected
  obtain ⟨original, member, origin⟩ := all_required.2.2 _ _ _ _ _ actual semantic costs resident guards safe
    output (List.mem_of_getElem? selected)
  obtain ⟨sourceIndex, found⟩ := List.mem_iff_getElem?.mp member
  exact ⟨sourceIndex, original, found, origin⟩

end MicroCFTA.SourceCurrentRequiredRowOrigins
