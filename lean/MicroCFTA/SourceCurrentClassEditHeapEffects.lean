import MicroCFTA.SourceCurrentTargetHeapEffects
import MicroCFTA.SourceCurrentClassFoldDomains
import MicroCFTA.SourceCurrentRequiredHeapEffects
import MicroCFTA.SourceEqualityNativeDemandFieldHeap

/-!
# Physical heaps through actual open class edits

Selected class paths derive every entered edit domain. Actual shared target
forces, native requests, head reads, and constructors retain stored unfolding
costs and physical annotations. Open unselected children remain permitted.
The right fold uses each actual tail forest as the next class capture.
-/
namespace MicroCFTA.SourceCurrentClassEditHeapEffects
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityNativeScoped
open SourceEqualityEdits SourceEqualityEditLeafPaths SourceEqualitySharedEditGraph SourceEqualitySharedEditEffects
open SourceEqualitySharedTargetState SourceEqualitySharedTargetLeaf SourceEqualityProjectionPathDomain
open SourceCurrentEditDomains
open SourceEqualityAnnotationHeap (Heap)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (annotation : Guard → Prop) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
variable (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) (base : InternedConstructorTemplates.State Symbol Guard)
variable (known : Values base originals) (domains : ∀ p ∈ record.paths, ForestClosed (p.map Int.ofNat) originals)
variable (emptyValid : annotation emptyGuard) (conjoinedValid : ∀ first second, annotation (conjoin first second)) (topValid : annotation top)

private def NodePhysical (edits : Edits EqualityNormalize.Path) (value : Value Symbol Guard)
    (before after : SharedState width Symbol Guard) : Prop :=
  Populated edits → HasLeaf edits → Allowed record edits →
    SourceEqualitySharedTargetState.Ready emptyGuard conjoin clear top record originals base before →
    Available before.native.machine.heap value → Safe edits value →
    CostHeap before.native.machine.heap → Heap annotation before.native.machine.heap →
      CostHeap after.native.machine.heap ∧ Heap annotation after.native.machine.heap

private def ChildrenPhysical (entries : List (Int × Edits EqualityNormalize.Path)) (offset : Nat) (values : List (Value Symbol Guard))
    (before after : SharedState width Symbol Guard) : Prop :=
  Populated (.editBelow entries) → Allowed record (.editBelow entries) →
    SourceEqualitySharedTargetState.Ready emptyGuard conjoin clear top record originals base before →
    Values before.native.machine.heap values → ChildrenSafe entries offset values →
    CostHeap before.native.machine.heap → Heap annotation before.native.machine.heap →
      CostHeap after.native.machine.heap ∧ Heap annotation after.native.machine.heap

private def RowsPhysical (entries : List (Int × Edits EqualityNormalize.Path)) (edges : List (EdgeValue Symbol Guard))
    (before after : SharedState width Symbol Guard) : Prop :=
  Populated (.editBelow entries) → Allowed record (.editBelow entries) →
    SourceEqualitySharedTargetState.Ready emptyGuard conjoin clear top record originals base before →
    Edges before.native.machine.heap edges → RowsSafe entries edges →
    CostHeap before.native.machine.heap → Heap annotation before.native.machine.heap →
      CostHeap after.native.machine.heap ∧ Heap annotation after.native.machine.heap

local notation "NodeLaw" => NodePhysical (width := width) annotation emptyGuard conjoin clear top record originals base
local notation "ChildrenLaw" => ChildrenPhysical (width := width) annotation emptyGuard conjoin clear top record originals base
local notation "RowsLaw" => RowsPhysical (width := width) annotation emptyGuard conjoin clear top record originals base

include known domains emptyValid conjoinedValid topValid

private theorem physical :
    (∀ edits (value : Value Symbol Guard) before result after,
      EditNode emptyGuard conjoin clear top record originals edits value before result after → NodeLaw edits value before after) ∧
    (∀ entries offset (values : List (Value Symbol Guard)) before results after,
      EditChildren emptyGuard conjoin clear top record originals entries offset values before results after → ChildrenLaw entries offset values before after) ∧
    (∀ entries (edges : List (EdgeValue Symbol Guard)) before results after,
      EditRows emptyGuard conjoin clear top record originals entries edges before results after → RowsLaw entries edges before after) := by
  have leafCase : ∀ {path value before result after}, Leaf emptyGuard conjoin clear top record originals path value before result after →
      NodeLaw (.editAt path) value before after := by
    intro path value before result after actual _ _ allowed ready available _ costs heap
    have member : path ∈ record.paths := by simpa only [Allowed, All] using allowed
    exact ⟨SourceCurrentTargetHeapEffects.leaf_cost_heap actual ready known domains member available costs,
      SourceCurrentTargetHeapEffects.leaf_heap annotation emptyValid conjoinedValid topValid actual ready known domains member available heap⟩
  have emptyCase : ∀ {entries state}, NodeLaw (.editBelow entries) (.empty : Value Symbol Guard) state state := by
    intro entries state _ _ _ _ _ _ costs heap
    exact ⟨costs, heap⟩
  have ordinaryCase : ∀ {entries edges before rebuilt middle value heap entry depth free},
      EditRows emptyGuard conjoin clear top record originals entries edges before rebuilt middle →
      run (makeNode rebuilt) middle.native.machine.heap = (value, heap) → RowsLaw entries edges before middle →
      NodeLaw (.editBelow entries) (.node entry edges depth free) before (advanceHeap middle heap) := by
    intro entries edges before rebuilt middle value heap entry depth free rows built ih populated _ allowed ready available safe costs annotations
    have resident := InternedEdgeResidency.resident_edges _ ready.native.semantic.ready.semantic.1.normal.facts.linked _ available.resident
    have checked := SourceCurrentClassEditDomains.rows_domains emptyGuard conjoin clear top record originals base known domains
      rows populated allowed ready resident (ordinary_rows safe)
    have first := ih populated allowed ready resident (ordinary_rows safe) costs annotations
    have constructor := SourceCurrentRequiredHeapEffects.node_constructor annotation rebuilt middle.native.machine.heap
      checked.1.native.semantic first.1 first.2 checked.2.2.1
    change CostHeap heap ∧ Heap annotation heap
    exact ⟨by simpa only [built] using constructor.2.2.1, by simpa only [built] using constructor.2.2.2.1⟩
  have recursiveCase : ∀ {entries original before exposed heap result after},
      SourceEqualityRequiredGraph.Recursive original → SourceEqualityRequiredHead.Head original before.native.machine.heap exposed heap →
      EditNode emptyGuard conjoin clear top record originals (.editBelow entries) exposed (advanceHeap before heap) result after →
      NodeLaw (.editBelow entries) exposed (advanceHeap before heap) after → NodeLaw (.editBelow entries) original before after := by
    intro entries original before exposed heap result after recursive head _ ih populated nonempty allowed ready available safe costs annotations
    have closed := recursive_closed recursive nonempty safe
    have first := head.verified ready.native.semantic.ready available closed
    have checked := SourceCurrentRequiredHeapEffects.head annotation head ready.native.semantic costs annotations available
    exact ih populated nonempty allowed (ready.heap heap first.1 checked.2.1) first.2.1
      (closed_safe _ exposed heap checked.2.1 first.2.1 first.2.2.1) checked.2.2.1 checked.2.2.2.1
  have nilChildren : ∀ {entries offset state}, ChildrenLaw entries offset ([] : List (Value Symbol Guard)) state state := by
    intro entries offset state _ _ _ _ _ costs heap
    exact ⟨costs, heap⟩
  have unselectedCase : ∀ {entries values before results after value} (offset : Nat),
      SourceEqualityNeededMap.lookup (offset : Int) entries = none →
      EditChildren emptyGuard conjoin clear top record originals entries (offset + 1) values before results after →
      ChildrenLaw entries (offset + 1) values before after → ChildrenLaw entries offset (value :: values) before after := by
    intro entries values before results after value offset _ _ ih populated allowed ready available safe costs heap
    exact ih populated allowed ready (fun original member => available original (List.mem_cons_of_mem _ member))
      (children_tail safe) costs heap
  have selectedCase : ∀ {entries edits value before result middle values results after} (offset : Nat),
      SourceEqualityNeededMap.lookup (offset : Int) entries = some edits →
      EditNode emptyGuard conjoin clear top record originals edits value before result middle →
      EditChildren emptyGuard conjoin clear top record originals entries (offset + 1) values middle results after →
      NodeLaw edits value before middle → ChildrenLaw entries (offset + 1) values middle after →
      ChildrenLaw entries offset (value :: values) before after := by
    intro entries edits value before result middle values results after offset found firstTrace _ firstIH restIH populated allowed ready available safe costs heap
    have member := SourceEqualityNeededMap.lookup_mem _ _ _ found
    have childPopulated := (show ∀ index child, (index, child) ∈ entries → Populated child ∧ HasLeaf child from
      by simpa only [Populated] using populated) _ _ member
    have childAllowed : Allowed record edits := by
      have allowed := allowed
      rw [Allowed, All] at allowed
      exact allowed _ _ member
    have childSafe := safe 0 _ (by simpa using found) value rfl
    have first := SourceCurrentClassEditDomains.node_domains emptyGuard conjoin clear top record originals base known domains
      firstTrace childPopulated.1 childPopulated.2 childAllowed ready (available _ List.mem_cons_self) childSafe
    have physical := firstIH childPopulated.1 childPopulated.2 childAllowed ready (available _ List.mem_cons_self) childSafe costs heap
    exact restIH populated allowed first.1
      (fun original member => first.2.1.available original (available original (List.mem_cons_of_mem _ member)))
      (children_tail safe) physical.1 physical.2
  have nilRows : ∀ {entries state}, RowsLaw entries ([] : List (EdgeValue Symbol Guard)) state state := by
    intro entries state _ _ _ _ _ costs heap
    exact ⟨costs, heap⟩
  have consCase : ∀ {entries before values middle result heap edges results after edge},
      EditChildren emptyGuard conjoin clear top record originals entries 0 edge.children before values middle →
      run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.native.machine.heap = (result, heap) →
      EditRows emptyGuard conjoin clear top record originals entries edges (advanceHeap middle heap) results after →
      ChildrenLaw entries 0 edge.children before middle → RowsLaw entries edges (advanceHeap middle heap) after →
      RowsLaw entries (edge :: edges) before after := by
    intro entries before values middle result heap edges results after edge children built _ childIH restIH populated allowed ready resident safe costs annotations
    have available := ready.native.semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident _ List.mem_cons_self)
    have first := SourceCurrentClassEditDomains.children_domains emptyGuard conjoin clear top record originals base known domains
      children populated allowed ready available (safe _ List.mem_cons_self)
    have physical := childIH populated allowed ready available (safe _ List.mem_cons_self) costs annotations
    have rebuilt := SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle.native.machine.heap
      first.1.native.semantic.ready first.2.2.1
    have semantic := SourceEqualityRequiredSemanticCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle.native.machine.heap
      first.1.native.semantic first.2.2.1
    have edgeKept : Keeps middle.native.machine.heap heap := by simpa only [built] using rebuilt.1
    have edgeSemantic : SemanticReady heap := by simpa only [built] using semantic
    have afterCosts : CostHeap heap := by
      have unchanged : CostHeap (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.native.machine.heap).2 := physical.1
      simpa only [built] using unchanged
    have afterHeap : Heap annotation heap := by
      simpa only [built] using SourceEqualityAnnotationHeap.run annotation _
        (SourceEqualityAnnotationHeap.makeEdge annotation edge.entry.key.symbol edge.entry.key.constraint values
          (annotations edge.entry.key edge (resident _ List.mem_cons_self))) middle.native.machine.heap physical.2
    exact restIH populated allowed (first.1.heap heap edgeKept edgeSemantic)
      (fun original member => InternedEdgeResidency.edge_grows _ _ (first.2.1.trans edgeKept).growth original
        (resident original (List.mem_cons_of_mem _ member)))
      (fun original member => safe original (List.mem_cons_of_mem _ member)) afterCosts afterHeap
  refine ⟨?_, ?_, ?_⟩
  · intro edits value before result after trace
    exact EditNode.rec (motive_1 := fun edits value before _ after _ => NodeLaw edits value before after)
      (motive_2 := fun entries offset values before _ after _ => ChildrenLaw entries offset values before after)
      (motive_3 := fun entries edges before _ after _ => RowsLaw entries edges before after)
      leafCase emptyCase ordinaryCase recursiveCase nilChildren unselectedCase selectedCase nilRows consCase trace
  · intro entries offset values before results after trace
    exact EditChildren.rec (motive_1 := fun edits value before _ after _ => NodeLaw edits value before after)
      (motive_2 := fun entries offset values before _ after _ => ChildrenLaw entries offset values before after)
      (motive_3 := fun entries edges before _ after _ => RowsLaw entries edges before after)
      leafCase emptyCase ordinaryCase recursiveCase nilChildren unselectedCase selectedCase nilRows consCase trace
  · intro entries edges before results after trace
    exact EditRows.rec (motive_1 := fun edits value before _ after _ => NodeLaw edits value before after)
      (motive_2 := fun entries offset values before _ after _ => ChildrenLaw entries offset values before after)
      (motive_3 := fun entries edges before _ after _ => RowsLaw entries edges before after)
      leafCase emptyCase ordinaryCase recursiveCase nilChildren unselectedCase selectedCase nilRows consCase trace

/-- Actual selected node edits retain stored costs and arbitrary physical annotations. -/
theorem node_effects {edits value before result after}
    (actual : EditNode (width := width) emptyGuard conjoin clear top record originals edits value before result after)
    (populated : Populated edits) (nonempty : HasLeaf edits) (allowed : Allowed record edits)
    (ready : SourceEqualitySharedTargetState.Ready emptyGuard conjoin clear top record originals base before)
    (available : Available before.native.machine.heap value) (safe : Safe edits value)
    (costs : CostHeap before.native.machine.heap) (heap : Heap annotation before.native.machine.heap) :
    CostHeap after.native.machine.heap ∧ Heap annotation after.native.machine.heap :=
  (physical annotation emptyGuard conjoin clear top record originals base known domains emptyValid conjoinedValid topValid).1
    _ _ _ _ _ actual populated nonempty allowed ready available safe costs heap

/-- Actual child scans retain both physical heap invariants at their exact returned state. -/
theorem children_effects {entries offset values before results after}
    (actual : EditChildren (width := width) emptyGuard conjoin clear top record originals entries offset values before results after)
    (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : SourceEqualitySharedTargetState.Ready emptyGuard conjoin clear top record originals base before)
    (available : Values before.native.machine.heap values) (safe : ChildrenSafe entries offset values)
    (costs : CostHeap before.native.machine.heap) (heap : Heap annotation before.native.machine.heap) :
    CostHeap after.native.machine.heap ∧ Heap annotation after.native.machine.heap :=
  (physical annotation emptyGuard conjoin clear top record originals base known domains emptyValid conjoinedValid topValid).2.1
    _ _ _ _ _ _ actual populated allowed ready available safe costs heap

/-- Actual full-guard row reconstruction derives stored costs and annotations from original physical rows. -/
theorem rows_effects {entries edges before results after}
    (actual : EditRows (width := width) emptyGuard conjoin clear top record originals entries edges before results after)
    (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : SourceEqualitySharedTargetState.Ready emptyGuard conjoin clear top record originals base before)
    (resident : Edges before.native.machine.heap edges) (safe : RowsSafe entries edges)
    (costs : CostHeap before.native.machine.heap) (heap : Heap annotation before.native.machine.heap) :
    CostHeap after.native.machine.heap ∧ Heap annotation after.native.machine.heap :=
  (physical annotation emptyGuard conjoin clear top record originals base known domains emptyValid conjoinedValid topValid).2.2
    _ _ _ _ _ actual populated allowed ready resident safe costs heap

end MicroCFTA.SourceCurrentClassEditHeapEffects



namespace MicroCFTA.SourceCurrentClassEditHeapEffects
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityEdits SourceEqualityEditLeafPaths
open SourceEqualitySharedEditGraph SourceEqualitySharedTargetState SourceEqualitySharedEditEffects SourceCurrentEditDomains
open SourceEqualityProjectionPathDomain SourceEqualityClassFoldGraph
open SourceEqualityAnnotationHeap (Heap)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
variable (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) (base : InternedConstructorTemplates.State Symbol Guard)
variable (known : Values base originals) (domains : ∀ p ∈ record.paths, ForestClosed (p.map Int.ofNat) originals)

include known domains

/-- Actual selected node edits retain stored costs without annotation premises. -/
theorem node_cost_heap {edits value before result after}
    (actual : EditNode (width := width) emptyGuard conjoin clear top record originals edits value before result after)
    (populated : Populated edits) (nonempty : HasLeaf edits) (allowed : Allowed record edits)
    (ready : SourceEqualitySharedTargetState.Ready emptyGuard conjoin clear top record originals base before)
    (available : Available before.native.machine.heap value) (safe : Safe edits value)
    (costs : CostHeap before.native.machine.heap) : CostHeap after.native.machine.heap :=
  (node_effects (fun _ => True) emptyGuard conjoin clear top record originals base known domains
    trivial (fun _ _ => trivial) trivial actual populated nonempty allowed ready available safe costs
    (by intro _ _ _; trivial)).1

/-- Actual selected child scans retain stored costs through every current returned heap. -/
theorem children_cost_heap {entries offset values before results after}
    (actual : EditChildren (width := width) emptyGuard conjoin clear top record originals entries offset values before results after)
    (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : SourceEqualitySharedTargetState.Ready emptyGuard conjoin clear top record originals base before)
    (available : Values before.native.machine.heap values) (safe : ChildrenSafe entries offset values)
    (costs : CostHeap before.native.machine.heap) : CostHeap after.native.machine.heap :=
  (children_effects (fun _ => True) emptyGuard conjoin clear top record originals base known domains
    trivial (fun _ _ => trivial) trivial actual populated allowed ready available safe costs
    (by intro _ _ _; trivial)).1

/-- Actual row reconstruction retains stored costs without closing unselected children. -/
theorem rows_cost_heap {entries edges before results after}
    (actual : EditRows (width := width) emptyGuard conjoin clear top record originals entries edges before results after)
    (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : SourceEqualitySharedTargetState.Ready emptyGuard conjoin clear top record originals base before)
    (resident : Edges before.native.machine.heap edges) (safe : RowsSafe entries edges)
    (costs : CostHeap before.native.machine.heap) : CostHeap after.native.machine.heap :=
  (rows_effects (fun _ => True) emptyGuard conjoin clear top record originals base known domains
    trivial (fun _ _ => trivial) trivial actual populated allowed ready resident safe costs
    (by intro _ _ _; trivial)).1

end MicroCFTA.SourceCurrentClassEditHeapEffects

namespace MicroCFTA.SourceCurrentClassEditHeapEffects
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityEdits SourceEqualityEditLeafPaths
open SourceEqualitySharedEditGraph SourceEqualitySharedTargetState SourceEqualitySharedEditEffects SourceCurrentEditDomains
open SourceEqualityProjectionPathDomain SourceEqualityClassFoldGraph
open SourceEqualityAnnotationHeap (Heap)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

private theorem compiled_safe (pairs : List (SourceEqualityEdits.Path × Action))
    (disjoint : pairs.Pairwise (fun first second => SourceEqualityEditCompiledPaths.Disjoint first.1 second.1))
    (values : List (Value Symbol Guard))
    (domains : ∀ path action, (path, action) ∈ pairs → ForestClosed path values)
    (entries : List (Int × Edits Action)) (compiled : build pairs = .editBelow entries) : ChildrenSafe entries 0 values := by
  intro query child found value selected path action retained
  have member : (Int.ofNat query :: path, action) ∈ leaves (build pairs) := by
    rw [compiled]
    exact below_member _ _ _ (SourceEqualityNeededMap.lookup_mem _ _ _ (by simpa using found)) _ _ retained
  have original := (SourceEqualityEditCompiledPaths.build_leaves pairs disjoint).mem_iff.mp member
  exact domains (Int.ofNat query :: path) action original value
    (by simpa only [SourceCurrentEditDomains.select_natural] using selected)

/-- A fresh actual class derives both physical heap invariants from its original selected path domains. -/
theorem class_effects (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    (emptyValid : annotation emptyGuard) (conjoinedValid : ∀ first second, annotation (conjoin first second)) (topValid : annotation top)
    {record : SourceEqualityClassOrder.Record} {values results : List (Value Symbol Guard)}
    {before after : NativeState width Symbol Guard}
    (actual : Class emptyGuard conjoin clear top record values before results after)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values)
    (domains : ∀ p ∈ record.paths, ForestClosed (p.map Int.ofNat) values)
    (costs : CostHeap before.machine.heap) (heap : Heap annotation before.machine.heap) :
    CostHeap after.machine.heap ∧ Heap annotation after.machine.heap := by
  have supported := SourceEqualityClassEdits.coherent_supported record coherent
  have disjoint := SourceEqualityClassEdits.edits_disjoint record.paths supported id
  have nonroot := SourceEqualityClassEdits.edits_nonroot record.paths
    (SourceEqualityClassEdits.supported_nonroot record.paths supported active) id
  have originalDomains : ∀ path action, (path, action) ∈ SourceEqualityClassEdits.edits record.paths id → ForestClosed path values := by
    intro path action member
    obtain ⟨original, included, same⟩ := List.mem_map.mp member
    cases same
    exact domains original included
  cases actual with
  | edit actual =>
      change EditList emptyGuard conjoin clear top record values
        (build (SourceEqualityClassEdits.edits record.paths id)) values (initial before) results _ at actual
      have initialReady := initial_ready emptyGuard conjoin clear top record values before.machine.heap before ready
        (pure_keeps _ ready.semantic.ready)
      have populated := build_populated (SourceEqualityClassEdits.edits record.paths id)
      have allowed := SourceEqualitySharedClassEdits.compiled_allowed record
      generalize compiled : build (SourceEqualityClassEdits.edits record.paths id) = edits at actual populated allowed
      cases actual with
      | leaf => exact False.elim (SourceEqualityEditCompiledPaths.build_not_leaf _ disjoint nonroot _ compiled)
      | @children entries _ _ _ _ children =>
          exact children_effects annotation emptyGuard conjoin clear top record values before.machine.heap available domains
            emptyValid conjoinedValid topValid children populated allowed initialReady available
            (compiled_safe _ disjoint values originalDomains entries compiled) costs heap

/-- Actual class right folds retain both physical heaps at every literal tail-returned state. -/
theorem fold_effects (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    (emptyValid : annotation emptyGuard) (conjoinedValid : ∀ first second, annotation (conjoin first second)) (topValid : annotation top)
    {records : List SourceEqualityClassOrder.Record} {values results : List (Value Symbol Guard)}
    {before after : NativeState width Symbol Guard}
    (actual : SourceEqualityClassFoldGraph.Fold emptyGuard conjoin clear top records values before results after)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values)
    (domains : ∀ record ∈ records, ∀ p ∈ record.paths, ForestClosed (p.map Int.ofNat) values)
    (costs : CostHeap before.machine.heap) (heap : Heap annotation before.machine.heap) :
    CostHeap after.machine.heap ∧ Heap annotation after.machine.heap := by
  induction actual with
  | nil => exact ⟨costs, heap⟩
  | cons tail head ih =>
      have first := SourceCurrentClassFoldDomains.fold_domains emptyGuard conjoin clear top tail
        (fun record member => coherent record (List.mem_cons_of_mem _ member))
        (fun record member => active record (List.mem_cons_of_mem _ member)) ready available
        (fun record member => domains record (List.mem_cons_of_mem _ member))
      have physical := ih (fun record member => coherent record (List.mem_cons_of_mem _ member))
        (fun record member => active record (List.mem_cons_of_mem _ member)) ready available
        (fun record member => domains record (List.mem_cons_of_mem _ member)) costs heap
      exact class_effects annotation emptyValid conjoinedValid topValid head (coherent _ List.mem_cons_self) (active _ List.mem_cons_self)
        first.1 first.2.2.1 (fun path member => first.2.2.2 _ (domains _ List.mem_cons_self path member)) physical.1 physical.2

/-- Final empty propagation retains the actual class fold's stored costs and physical annotations. -/
theorem pass_effects (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    (emptyValid : annotation emptyGuard) (conjoinedValid : ∀ first second, annotation (conjoin first second)) (topValid : annotation top)
    {records : List SourceEqualityClassOrder.Record} {values results : List (Value Symbol Guard)}
    {before after : NativeState width Symbol Guard}
    (actual : Pass emptyGuard conjoin clear top records values before results after)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values)
    (domains : ∀ record ∈ records, ∀ p ∈ record.paths, ForestClosed (p.map Int.ofNat) values)
    (costs : CostHeap before.machine.heap) (heap : Heap annotation before.machine.heap) :
    CostHeap after.machine.heap ∧ Heap annotation after.machine.heap := by
  cases actual with
  | done fold => exact fold_effects annotation emptyValid conjoinedValid topValid fold coherent active ready available domains costs heap

/-- A fresh actual class retains stored costs without an annotation premise. -/
theorem class_cost_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values results : List (Value Symbol Guard)} {before after : NativeState width Symbol Guard}
    (actual : Class emptyGuard conjoin clear top record values before results after)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values)
    (domains : ∀ p ∈ record.paths, ForestClosed (p.map Int.ofNat) values) (costs : CostHeap before.machine.heap) :
    CostHeap after.machine.heap :=
  (class_effects (fun _ => True) trivial (fun _ _ => trivial) trivial actual coherent active ready available domains costs
    (by intro _ _ _; trivial)).1

/-- An actual class right fold retains stored costs at every reached heap. -/
theorem fold_cost_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {records : List SourceEqualityClassOrder.Record} {values results : List (Value Symbol Guard)} {before after : NativeState width Symbol Guard}
    (actual : SourceEqualityClassFoldGraph.Fold emptyGuard conjoin clear top records values before results after)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values)
    (domains : ∀ record ∈ records, ∀ p ∈ record.paths, ForestClosed (p.map Int.ofNat) values) (costs : CostHeap before.machine.heap) :
    CostHeap after.machine.heap :=
  (fold_effects (fun _ => True) trivial (fun _ _ => trivial) trivial actual coherent active ready available domains costs
    (by intro _ _ _; trivial)).1

/-- A completed source pass retains stored costs through final literal empty propagation. -/
theorem pass_cost_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {records : List SourceEqualityClassOrder.Record} {values results : List (Value Symbol Guard)} {before after : NativeState width Symbol Guard}
    (actual : Pass emptyGuard conjoin clear top records values before results after)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values)
    (domains : ∀ record ∈ records, ∀ p ∈ record.paths, ForestClosed (p.map Int.ofNat) values) (costs : CostHeap before.machine.heap) :
    CostHeap after.machine.heap :=
  (pass_effects (fun _ => True) trivial (fun _ _ => trivial) trivial actual coherent active ready available domains costs
    (by intro _ _ _; trivial)).1

end MicroCFTA.SourceCurrentClassEditHeapEffects

namespace MicroCFTA.SourceCurrentClassEditHeapEffects
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityNativeScoped SourceEqualityClassFoldGraph SourceEqualityProjectionPathDomain
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "FieldHeap" => SourceEqualityNativeDemandFieldHeap.Heap

/-- The concrete current source pass derives stored costs and normalized physical equality fields. -/
theorem pass_fields [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {records : List SourceEqualityClassOrder.Record} {values results : List (Value Symbol Guard)}
    {before after : NativeState width Symbol Guard}
    (actual : Pass top conjoin SourceMemoGate.plain top records values before results after)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady top conjoin before) (available : Values before.machine.heap values)
    (domains : ∀ record ∈ records, ∀ p ∈ record.paths, ForestClosed (p.map Int.ofNat) values)
    (costs : CostHeap before.machine.heap) (fields : FieldHeap before.machine.heap) :
    CostHeap after.machine.heap ∧ FieldHeap after.machine.heap := by
  letI : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
  exact pass_effects (fun guard : Guard => SourceEqualityGuardReadback.Cached guard.equalities)
    SourceEqualityConstraintConstructors.top_cached (SourceEqualityConstraintConstructors.conjoin_cached GuardStructuralOrder.le)
    SourceEqualityConstraintConstructors.top_cached actual coherent active ready available domains costs fields

end MicroCFTA.SourceCurrentClassEditHeapEffects
