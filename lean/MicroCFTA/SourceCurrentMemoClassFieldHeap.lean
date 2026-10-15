import MicroCFTA.SourceCurrentMemoTargetFieldHeap
import MicroCFTA.SourceCurrentMemoClassPass
import MicroCFTA.SourceEqualityNativeDemandFieldHeap

/-!
# Physical annotation heaps through memo-aware edits and class passes

The original selected path domains derive every reached physical state.
Leaf forces, native requests, head exposure, and constructors retain their
checked annotations. Unselected ordinary siblings may remain open.
-/
namespace MicroCFTA.SourceCurrentMemoClassFieldHeap
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityNativeScoped
open SourceEqualityEdits SourceEqualityEditLeafPaths SourceEqualitySharedEditEffects
open SourceCurrentMemoSharedEditGraph SourceCurrentMemoSharedTargetState SourceCurrentEditDomains
open SourceEqualityProjectionPathDomain
open SourceEqualityAnnotationHeap (Heap)
open SourceCurrentMemoMergeGraph (Memo)
open SourceCurrentMemoMergeEffects (Stored)

/-- Child-list callbacks do not inspect a root leaf token. -/
def ListSafe (edits : Edits Action) (values : List (Value Symbol Guard)) : Prop :=
  match edits with
  | .editAt _ => True
  | .editBelow entries => ChildrenSafe entries 0 values

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (annotation : Guard → Prop) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
variable (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
variable (base : InternedConstructorTemplates.State Symbol Guard) (known : Values base originals)
variable (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) originals)
variable (emptyValid : annotation emptyGuard) (conjoinedValid : ∀ first second, annotation (conjoin first second)) (topValid : annotation top)

private def NodeFields (edits : Edits EqualityNormalize.Path) (value : Value Symbol Guard)
    (before after : SharedState width Symbol Guard) : Prop :=
  Populated edits → HasLeaf edits → Allowed record edits → Ready emptyGuard conjoin clear top record originals base before →
    Available before.native.machine.heap value → Safe edits value → Heap annotation before.native.machine.heap → Heap annotation after.native.machine.heap

private def ChildrenFields (entries : List (Int × Edits EqualityNormalize.Path)) (offset : Nat) (values : List (Value Symbol Guard))
    (before after : SharedState width Symbol Guard) : Prop :=
  Populated (.editBelow entries) → Allowed record (.editBelow entries) → Ready emptyGuard conjoin clear top record originals base before →
    Values before.native.machine.heap values → ChildrenSafe entries offset values → Heap annotation before.native.machine.heap → Heap annotation after.native.machine.heap

private def RowsFields (entries : List (Int × Edits EqualityNormalize.Path)) (edges : List (EdgeValue Symbol Guard))
    (before after : SharedState width Symbol Guard) : Prop :=
  Populated (.editBelow entries) → Allowed record (.editBelow entries) → Ready emptyGuard conjoin clear top record originals base before →
    Edges before.native.machine.heap edges → RowsSafe entries edges → Heap annotation before.native.machine.heap → Heap annotation after.native.machine.heap

local notation "NodeLaw" => NodeFields (width := width) annotation emptyGuard conjoin clear top record originals base
local notation "ChildrenLaw" => ChildrenFields (width := width) annotation emptyGuard conjoin clear top record originals base
local notation "RowsLaw" => RowsFields (width := width) annotation emptyGuard conjoin clear top record originals base

include known domains emptyValid conjoinedValid topValid

private theorem fields :
    (∀ edits (value : Value Symbol Guard) before result after,
      EditNode emptyGuard conjoin clear top record originals edits value before result after → NodeLaw edits value before after) ∧
    (∀ entries offset (values : List (Value Symbol Guard)) before results after,
      EditChildren emptyGuard conjoin clear top record originals entries offset values before results after → ChildrenLaw entries offset values before after) ∧
    (∀ entries (edges : List (EdgeValue Symbol Guard)) before results after,
      EditRows emptyGuard conjoin clear top record originals entries edges before results after → RowsLaw entries edges before after) := by
  have leafCase : ∀ {path value before result after},
      SourceCurrentMemoSharedTargetLeaf.Leaf emptyGuard conjoin clear top record originals path value before result after →
      NodeLaw (.editAt path) value before after := by
    intro path value before result after trace _ _ allowed ready available _ annotations
    have member : path ∈ record.paths := by simpa only [Allowed, All] using allowed
    exact SourceCurrentMemoTargetFieldHeap.leaf_heap annotation emptyValid conjoinedValid topValid trace ready known domains member available annotations
  have emptyCase : ∀ {entries state}, NodeLaw (.editBelow entries) (.empty : Value Symbol Guard) state state := by
    intro entries state _ _ _ _ _ _ annotations
    exact annotations
  have ordinaryCase : ∀ {entries edges before rebuilt middle value heap entry depth free},
      EditRows emptyGuard conjoin clear top record originals entries edges before rebuilt middle →
      run (makeNode rebuilt) middle.native.machine.heap = (value, heap) → RowsLaw entries edges before middle →
      NodeLaw (.editBelow entries) (.node entry edges depth free) before (advanceHeap middle heap) := by
    intro entries edges before rebuilt middle value heap entry depth free _ built ih populated _ allowed ready available safe annotations
    have middleFields := ih populated allowed ready
      (InternedEdgeResidency.resident_edges _ ready.native.semantic.ready.semantic.1.normal.facts.linked _ available.resident)
      (ordinary_rows safe) annotations
    change Heap annotation heap
    simpa only [built] using SourceEqualityAnnotationHeap.run annotation _ (SourceEqualityAnnotationHeap.makeNode annotation rebuilt)
      middle.native.machine.heap middleFields
  have recursiveCase : ∀ {entries original before exposed heap result after},
      SourceEqualityRequiredGraph.Recursive original → SourceEqualityRequiredHead.Head original before.native.machine.heap exposed heap →
      EditNode emptyGuard conjoin clear top record originals (.editBelow entries) exposed (advanceHeap before heap) result after →
      NodeLaw (.editBelow entries) exposed (advanceHeap before heap) after → NodeLaw (.editBelow entries) original before after := by
    intro entries original before exposed heap result after recursive head _ ih populated nonempty allowed ready available safe annotations
    have closed := recursive_closed recursive nonempty safe
    have checked := head.verified ready.native.semantic.ready available closed
    have semantic := SourceEqualityRequiredSemanticCache.head head ready.native.semantic available closed
    have physical := SourceCurrentRequiredHeapEffects.head annotation head ready.native.semantic ready.costs annotations available
    exact ih populated nonempty allowed (ready.heap heap checked.1 semantic physical.2.2.1) checked.2.1
      (closed_safe _ exposed heap semantic checked.2.1 checked.2.2.1) physical.2.2.2.1
  have nilChildren : ∀ {entries offset state}, ChildrenLaw entries offset ([] : List (Value Symbol Guard)) state state := by
    intro entries offset state _ _ _ _ _ annotations
    exact annotations
  have unselectedCase : ∀ {entries values before results after value} (offset : Nat),
      SourceEqualityNeededMap.lookup (offset : Int) entries = none →
      EditChildren emptyGuard conjoin clear top record originals entries (offset + 1) values before results after →
      ChildrenLaw entries (offset + 1) values before after → ChildrenLaw entries offset (value :: values) before after := by
    intro entries values before results after value offset _ _ ih populated allowed ready available safe annotations
    exact ih populated allowed ready (fun original member => available original (List.mem_cons_of_mem _ member)) (children_tail safe) annotations
  have selectedCase : ∀ {entries edits value before result middle values results after} (offset : Nat),
      SourceEqualityNeededMap.lookup (offset : Int) entries = some edits →
      EditNode emptyGuard conjoin clear top record originals edits value before result middle →
      EditChildren emptyGuard conjoin clear top record originals entries (offset + 1) values middle results after →
      NodeLaw edits value before middle → ChildrenLaw entries (offset + 1) values middle after →
      ChildrenLaw entries offset (value :: values) before after := by
    intro entries edits value before result middle values results after offset found first _ firstIH restIH populated allowed ready available safe annotations
    have member := SourceEqualityNeededMap.lookup_mem _ _ _ found
    have childPopulated := (show ∀ index child, (index, child) ∈ entries → Populated child ∧ HasLeaf child from
      by simpa only [Populated] using populated) _ _ member
    have childAllowed : Allowed record edits := by rw [Allowed, All] at allowed; exact allowed _ _ member
    have childSafe := safe 0 _ (by simpa using found) value rfl
    have checked := SourceCurrentMemoSharedEditDomains.node_domains emptyGuard conjoin clear top record originals base known domains first
      childPopulated.1 childPopulated.2 childAllowed ready (available _ List.mem_cons_self) childSafe
    have current := firstIH childPopulated.1 childPopulated.2 childAllowed ready (available _ List.mem_cons_self) childSafe annotations
    exact restIH populated allowed checked.1
      (fun original member => checked.2.1.available original (available original (List.mem_cons_of_mem _ member))) (children_tail safe) current
  have nilRows : ∀ {entries state}, RowsLaw entries ([] : List (EdgeValue Symbol Guard)) state state := by
    intro entries state _ _ _ _ _ annotations
    exact annotations
  have consCase : ∀ {entries before values middle result heap edges results after edge},
      EditChildren emptyGuard conjoin clear top record originals entries 0 edge.children before values middle →
      run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.native.machine.heap = (result, heap) →
      EditRows emptyGuard conjoin clear top record originals entries edges (advanceHeap middle heap) results after →
      ChildrenLaw entries 0 edge.children before middle → RowsLaw entries edges (advanceHeap middle heap) after →
      RowsLaw entries (edge :: edges) before after := by
    intro entries before values middle result heap edges results after edge children built _ firstIH restIH populated allowed ready resident safe annotations
    have available := ready.native.semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident _ List.mem_cons_self)
    have first := SourceCurrentMemoSharedEditDomains.children_domains emptyGuard conjoin clear top record originals base known domains children
      populated allowed ready available (safe _ List.mem_cons_self)
    have current := firstIH populated allowed ready available (safe _ List.mem_cons_self) annotations
    have rebuilt := SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle.native.machine.heap
      first.1.native.semantic.ready first.2.2.1
    have semantic := SourceEqualityRequiredSemanticCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle.native.machine.heap
      first.1.native.semantic first.2.2.1
    have edgeKept : Keeps middle.native.machine.heap heap := by simpa only [built] using rebuilt.1
    have edgeSemantic : SemanticReady heap := by simpa only [built] using semantic
    have firstKept := first.2.1.trans edgeKept
    have edgeFields : Heap annotation heap := by
      simpa only [built] using SourceEqualityAnnotationHeap.run annotation _
        (SourceEqualityAnnotationHeap.makeEdge annotation edge.entry.key.symbol edge.entry.key.constraint values
          (annotations _ _ (resident _ List.mem_cons_self))) middle.native.machine.heap current
    exact restIH populated allowed (first.1.heap heap edgeKept edgeSemantic (by
      have costs : InternedFreshOrdinaryCostHeap.Heap (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.native.machine.heap).2 := first.1.costs
      simpa only [built] using costs))
      (fun original member => InternedEdgeResidency.edge_grows _ _ firstKept.growth original (resident original (List.mem_cons_of_mem _ member)))
      (fun original member => safe original (List.mem_cons_of_mem _ member)) edgeFields
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

/-- Actual node edits derive annotations at their returned physical heap. -/
theorem node_heap {edits value before result after}
    (actual : EditNode (width := width) emptyGuard conjoin clear top record originals edits value before result after) :
    NodeLaw edits value before after :=
  (fields annotation emptyGuard conjoin clear top record originals base known domains emptyValid conjoinedValid topValid).1 _ _ _ _ _ actual

/-- Ordered child edits pass derived annotations to the next selected subtree. -/
theorem children_heap {entries offset values before results after}
    (actual : EditChildren (width := width) emptyGuard conjoin clear top record originals entries offset values before results after) :
    ChildrenLaw entries offset values before after :=
  (fields annotation emptyGuard conjoin clear top record originals base known domains emptyValid conjoinedValid topValid).2.1 _ _ _ _ _ _ actual

/-- Ordered row edits retain annotations through their actual constructor states. -/
theorem rows_heap {entries edges before results after}
    (actual : EditRows (width := width) emptyGuard conjoin clear top record originals entries edges before results after) :
    RowsLaw entries edges before after :=
  (fields annotation emptyGuard conjoin clear top record originals base known domains emptyValid conjoinedValid topValid).2.2 _ _ _ _ _ actual

/-- Source list edits ignore root callbacks and retain annotations for below edits. -/
theorem list_heap {edits values before results after}
    (actual : EditList (width := width) emptyGuard conjoin clear top record originals edits values before results after)
    (populated : Populated edits) (allowed : Allowed record edits)
    (ready : Ready emptyGuard conjoin clear top record originals base before) (available : Values before.native.machine.heap values)
    (safe : ListSafe edits values)
    (annotations : Heap annotation before.native.machine.heap) : Heap annotation after.native.machine.heap := by
  cases actual with
  | leaf => exact annotations
  | children actual =>
      exact children_heap annotation emptyGuard conjoin clear top record originals base known domains emptyValid conjoinedValid topValid
        actual populated allowed ready available safe annotations

end MicroCFTA.SourceCurrentMemoClassFieldHeap

namespace MicroCFTA.SourceCurrentMemoClassFieldHeap
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityProjectionPathDomain
open SourceEqualityEdits SourceEqualityEditLeafPaths SourceEqualitySharedEditEffects SourceCurrentEditDomains
open SourceCurrentMemoSharedTargetState SourceCurrentMemoSharedEditGraph SourceCurrentMemoClassPass
open SourceCurrentMemoMergeGraph (Memo)
open SourceCurrentMemoMergeEffects (Stored)
open SourceEqualityAnnotationHeap (Heap)
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (annotation : Guard → Prop) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
variable (emptyValid : annotation emptyGuard) (conjoinedValid : ∀ first second, annotation (conjoin first second)) (topValid : annotation top)

include emptyValid conjoinedValid topValid

/-- A class derives physical annotations from its captured selected path domains and actual merge table. -/
theorem class_heap {record values results} {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Class emptyGuard conjoin clear top record values before memo results after saved)
    (coherent : SourceEqualityClassOrder.Coherent record) (_active : EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap) (stored : Stored before.machine.heap memo)
    (available : Values before.machine.heap values)
    (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (annotations : Heap annotation before.machine.heap) : Heap annotation after.machine.heap := by
  have supported := SourceEqualityClassEdits.coherent_supported record coherent
  have disjoint := SourceEqualityClassEdits.edits_disjoint record.paths supported id
  have safe : ListSafe (build (SourceEqualityClassEdits.edits record.paths id)) values := by
    cases compiled : build (SourceEqualityClassEdits.edits record.paths id) with
    | editAt target => trivial
    | editBelow entries =>
        intro query child found value selected path action retained
        have member : (Int.ofNat query :: path, action) ∈ leaves (build (SourceEqualityClassEdits.edits record.paths id)) := by
          rw [compiled]
          exact below_member _ _ _ (SourceEqualityNeededMap.lookup_mem _ _ _ (by simpa using found)) _ _ retained
        obtain ⟨original, included, same⟩ := List.mem_map.mp ((SourceEqualityEditCompiledPaths.build_leaves _ disjoint).mem_iff.mp member)
        have domain := domains original included
        have same := congrArg Prod.fst same
        dsimp at same
        rw [same] at domain
        apply domain value
        change SourceEqualityProjectionGraph.select values (Int.ofNat query) = some value
        rw [select_natural]
        exact selected
  cases actual with
  | edit actual =>
      change EditList emptyGuard conjoin clear top record values
        (build (SourceEqualityClassEdits.edits record.paths id)) values (initial before memo) results _ at actual
      have initialReady := initial_ready emptyGuard conjoin clear top record values before.machine.heap before memo ready
        (pure_keeps _ ready.semantic.ready) costs stored
      exact list_heap annotation emptyGuard conjoin clear top record values before.machine.heap available domains
        emptyValid conjoinedValid topValid actual (build_populated _) (SourceEqualitySharedClassEdits.compiled_allowed record)
        initialReady available safe annotations

/-- Each head class receives fields and original path domains derived from its actual completed tail. -/
theorem fold_heap {records values results} {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : SourceCurrentMemoClassPass.Fold emptyGuard conjoin clear top records values before memo results after saved)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap) (stored : Stored before.machine.heap memo)
    (available : Values before.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (annotations : Heap annotation before.machine.heap) : Heap annotation after.machine.heap := by
  induction actual with
  | nil => exact annotations
  | cons tail head ih =>
      obtain ⟨nextReady, nextCosts, nextStored, _, firstAvailable, firstDomains, _⟩ :=
        SourceCurrentMemoClassPass.fold_effects emptyGuard conjoin clear top tail
          (fun record member => coherent record (List.mem_cons_of_mem _ member))
          (fun record member => active record (List.mem_cons_of_mem _ member)) ready costs stored available
          (fun record member => domains record (List.mem_cons_of_mem _ member))
      have firstFields := ih (fun record member => coherent record (List.mem_cons_of_mem _ member))
        (fun record member => active record (List.mem_cons_of_mem _ member)) ready costs stored available
        (fun record member => domains record (List.mem_cons_of_mem _ member)) annotations
      exact class_heap annotation emptyGuard conjoin clear top emptyValid conjoinedValid topValid head
        (coherent _ List.mem_cons_self) (active _ List.mem_cons_self) nextReady nextCosts nextStored firstAvailable
        (fun path member => firstDomains _ (domains _ List.mem_cons_self path member)) firstFields

/-- Final empty propagation retains the actual pass's physical annotation heap. -/
theorem pass_heap {records values results} {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Pass emptyGuard conjoin clear top records values before memo results after saved)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap) (stored : Stored before.machine.heap memo)
    (available : Values before.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (annotations : Heap annotation before.machine.heap) : Heap annotation after.machine.heap := by
  cases actual with
  | done fold =>
      exact fold_heap annotation emptyGuard conjoin clear top emptyValid conjoinedValid topValid
        fold coherent active ready costs stored available domains annotations

end MicroCFTA.SourceCurrentMemoClassFieldHeap

namespace MicroCFTA.SourceCurrentMemoClassFieldHeap
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityNativeScoped SourceEqualityProjectionPathDomain SourceCurrentMemoClassPass
open SourceCurrentMemoMergeGraph (Memo)
open SourceCurrentMemoMergeEffects (Stored)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "FieldHeap" => SourceEqualityNativeDemandFieldHeap.Heap

/-- The concrete source pass derives normalized stored equality fields through its actual memo-aware workers. -/
theorem pass_fields [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {records : List SourceEqualityClassOrder.Record} {values results : List (Value Symbol Guard)}
    {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Pass top conjoin SourceMemoGate.plain top records values before memo results after saved)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady top conjoin before) (costs : CostHeap before.machine.heap) (stored : Stored before.machine.heap memo)
    (available : Values before.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (fields : FieldHeap before.machine.heap) : FieldHeap after.machine.heap := by
  letI : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
  exact pass_heap (fun guard : Guard => SourceEqualityGuardReadback.Cached guard.equalities)
    top conjoin SourceMemoGate.plain top SourceEqualityConstraintConstructors.top_cached
    (SourceEqualityConstraintConstructors.conjoin_cached GuardStructuralOrder.le) SourceEqualityConstraintConstructors.top_cached
    actual coherent active ready costs stored available domains fields

end MicroCFTA.SourceCurrentMemoClassFieldHeap
