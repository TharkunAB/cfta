import MicroCFTA.SourceCurrentTargetQueryMemos
import MicroCFTA.SourceCurrentClassEditDomains

/-!
# Actual global reads through simultaneous shared class edits

Each receipt follows its actual shared edit graph. Leaf force, native calls,
recursive head reads, and ordered child and row calls retain their exact
returned memo bundles. Constructor work retains the query bundle. Selected
path domains permit unrelated open children. Runtime publication is separate.
-/
namespace MicroCFTA.SourceCurrentClassEditQueryMemos
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityNativeScoped
open SourceEqualityEdits SourceEqualityEditLeafPaths SourceEqualitySharedEditGraph SourceEqualitySharedEditEffects
open SourceEqualitySharedTargetState SourceEqualityProjectionPathDomain SourceCurrentEditDomains
open SourceCurrentSubsumesQueryMemos (Effect)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "HeapState" => InternedConstructorTemplates.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

mutual
  /-- Node receipts retain concrete leaf or head calls and literal reconstruction. -/
  inductive NodeReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
      (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
      (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) :
      {edits : Edits EqualityNormalize.Path} → {value : Value Symbol Guard} → {before : SharedState width Symbol Guard} →
      {result : Value Symbol Guard} → {after : SharedState width Symbol Guard} →
      EditNode emptyGuard conjoin clear top record originals edits value before result after → Memos → Memos → Prop where
    | leaf (read : SourceCurrentTargetQueryMemos.LeafReads actual memos saved) :
        NodeReads emptyGuard conjoin clear top record originals (.leaf actual) memos saved
    | empty : NodeReads emptyGuard conjoin clear top record originals .empty memos memos
    | ordinary {entries edges before rebuilt middle value heap entry depth free}
        {actual : EditRows emptyGuard conjoin clear top record originals entries edges before rebuilt middle}
        {built : run (makeNode rebuilt) middle.native.machine.heap = (value, heap)}
        (read : RowsReads emptyGuard conjoin clear top record originals actual memos saved) :
        NodeReads emptyGuard conjoin clear top record originals
          (.ordinary (entry := entry) (depth := depth) (free := free) actual built) memos saved
    | recursive {entries original before exposed heap value after}
        {recursive : SourceEqualityRequiredGraph.Recursive original}
        {head : SourceEqualityRequiredHead.Head original before.native.machine.heap exposed heap}
        {body : EditNode emptyGuard conjoin clear top record originals (.editBelow entries) exposed (advanceHeap before heap) value after}
        (headRead : SourceCurrentRequiredQueryMemos.HeadReads head memos middle)
        (bodyRead : NodeReads emptyGuard conjoin clear top record originals body middle saved) :
        NodeReads emptyGuard conjoin clear top record originals (.recursive recursive head body) memos saved

  /-- Child receipts retain exact selected offsets and source order. -/
  inductive ChildrenReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
      (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
      (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) :
      {entries : List (Int × Edits EqualityNormalize.Path)} → {offset : Nat} → {values : List (Value Symbol Guard)} →
      {before : SharedState width Symbol Guard} → {results : List (Value Symbol Guard)} → {after : SharedState width Symbol Guard} →
      EditChildren emptyGuard conjoin clear top record originals entries offset values before results after → Memos → Memos → Prop where
    | nil : ChildrenReads emptyGuard conjoin clear top record originals .nil memos memos
    | unselected {entries values before results after value} {offset : Nat}
        {absent : SourceEqualityNeededMap.lookup (offset : Int) entries = none}
        {rest : EditChildren emptyGuard conjoin clear top record originals entries (offset + 1) values before results after}
        (read : ChildrenReads emptyGuard conjoin clear top record originals rest memos saved) :
        ChildrenReads emptyGuard conjoin clear top record originals (.unselected (value := value) offset absent rest) memos saved
    | selected {entries edits value before result middle values results after} {offset : Nat}
        {found : SourceEqualityNeededMap.lookup (offset : Int) entries = some edits}
        {first : EditNode emptyGuard conjoin clear top record originals edits value before result middle}
        {rest : EditChildren emptyGuard conjoin clear top record originals entries (offset + 1) values middle results after}
        (own : NodeReads emptyGuard conjoin clear top record originals first memos next)
        (tail : ChildrenReads emptyGuard conjoin clear top record originals rest next saved) :
        ChildrenReads emptyGuard conjoin clear top record originals (.selected offset found first rest) memos saved

  /-- Rows retain child calls, actual guard-preserving construction, and later rows. -/
  inductive RowsReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
      (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
      (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) :
      {entries : List (Int × Edits EqualityNormalize.Path)} → {edges : List (EdgeValue Symbol Guard)} →
      {before : SharedState width Symbol Guard} → {results : List (EdgeValue Symbol Guard)} → {after : SharedState width Symbol Guard} →
      EditRows emptyGuard conjoin clear top record originals entries edges before results after → Memos → Memos → Prop where
    | nil : RowsReads emptyGuard conjoin clear top record originals .nil memos memos
    | cons {entries before values middle result heap edges results after} {edge : EdgeValue Symbol Guard}
        {children : EditChildren emptyGuard conjoin clear top record originals entries 0 edge.children before values middle}
        {rebuilt : run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.native.machine.heap = (result, heap)}
        {rest : EditRows emptyGuard conjoin clear top record originals entries edges (advanceHeap middle heap) results after}
        (own : ChildrenReads emptyGuard conjoin clear top record originals children memos next)
        (tail : RowsReads emptyGuard conjoin clear top record originals rest next saved) :
        RowsReads emptyGuard conjoin clear top record originals (.cons children rebuilt rest) memos saved
end

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
variable (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
variable (base : HeapState Symbol Guard) (known : Values base originals)
variable (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) originals)

private def NodeWitness {edits value before result after}
    (trace : EditNode (width := width) emptyGuard conjoin clear top record originals edits value before result after) : Prop :=
  Populated edits → HasLeaf edits → Allowed record edits → Ready emptyGuard conjoin clear top record originals base before →
    Available before.native.machine.heap value → Safe edits value → CostHeap before.native.machine.heap →
    ∀ memos, Valid before.native.machine.heap memos →
      ∃ saved, NodeReads emptyGuard conjoin clear top record originals trace memos saved ∧
        Valid after.native.machine.heap saved ∧ CostHeap after.native.machine.heap ∧
        Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query

private def ChildrenWitness {entries offset values before results after}
    (trace : EditChildren (width := width) emptyGuard conjoin clear top record originals entries offset values before results after) : Prop :=
  Populated (.editBelow entries) → Allowed record (.editBelow entries) → Ready emptyGuard conjoin clear top record originals base before →
    Values before.native.machine.heap values → ChildrenSafe entries offset values → CostHeap before.native.machine.heap →
    ∀ memos, Valid before.native.machine.heap memos →
      ∃ saved, ChildrenReads emptyGuard conjoin clear top record originals trace memos saved ∧
        Valid after.native.machine.heap saved ∧ CostHeap after.native.machine.heap ∧
        Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query

private def RowsWitness {entries edges before results after}
    (trace : EditRows (width := width) emptyGuard conjoin clear top record originals entries edges before results after) : Prop :=
  Populated (.editBelow entries) → Allowed record (.editBelow entries) → Ready emptyGuard conjoin clear top record originals base before →
    Edges before.native.machine.heap edges → RowsSafe entries edges → CostHeap before.native.machine.heap →
    ∀ memos, Valid before.native.machine.heap memos →
      ∃ saved, RowsReads emptyGuard conjoin clear top record originals trace memos saved ∧
        Valid after.native.machine.heap saved ∧ CostHeap after.native.machine.heap ∧
        Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query

local notation "NodeLaw" => NodeWitness (width := width) emptyGuard conjoin clear top record originals base
local notation "ChildrenLaw" => ChildrenWitness (width := width) emptyGuard conjoin clear top record originals base
local notation "RowsLaw" => RowsWitness (width := width) emptyGuard conjoin clear top record originals base

include known domains

private theorem witnesses :
    (∀ edits (value : Value Symbol Guard) before result after
      (trace : EditNode emptyGuard conjoin clear top record originals edits value before result after), NodeLaw trace) ∧
    (∀ entries offset (values : List (Value Symbol Guard)) before results after
      (trace : EditChildren emptyGuard conjoin clear top record originals entries offset values before results after), ChildrenLaw trace) ∧
    (∀ entries (edges : List (EdgeValue Symbol Guard)) before results after
      (trace : EditRows emptyGuard conjoin clear top record originals entries edges before results after), RowsLaw trace) := by
  have leafCase : ∀ {path value before result after}
      (trace : SourceEqualitySharedTargetLeaf.Leaf emptyGuard conjoin clear top record originals path value before result after), NodeLaw (.leaf trace) := by
    intro path value before result after trace _ _ allowed ready available safe costs memos valid
    have member : path ∈ record.paths := by simpa only [Allowed, All] using allowed
    have closed : value.free = [] := by simpa only [NodeClosed] using safe [] path (by simp [leaves])
    obtain ⟨saved, read, effects⟩ := SourceCurrentTargetQueryMemos.leaf_memos trace ready known domains member available closed costs memos valid
    exact ⟨saved, .leaf read, effects.valid, effects.costs, effects.retained, effects.query⟩
  have emptyCase : ∀ {entries state}, NodeLaw (EditNode.empty (entries := entries) (state := state)) := by
    intro entries state _ _ _ _ _ _ costs memos valid
    exact ⟨memos, .empty, valid, costs, extends_refl _, rfl⟩
  have ordinaryCase : ∀ {entries edges before rebuilt middle value heap entry depth free}
      (rows : EditRows emptyGuard conjoin clear top record originals entries edges before rebuilt middle)
      (built : run (makeNode rebuilt) middle.native.machine.heap = (value, heap)), RowsLaw rows →
      NodeLaw (.ordinary (entry := entry) (depth := depth) (free := free) rows built) := by
    intro entries edges before rebuilt middle value heap entry depth free rows built ih populated _ allowed ready available safe costs memos valid
    have resident := InternedEdgeResidency.resident_edges _ ready.native.semantic.ready.semantic.1.normal.facts.linked _ available.resident
    obtain ⟨saved, read, coherent, middleCosts, retained, query⟩ := ih populated allowed ready resident (ordinary_rows safe) costs memos valid
    have effects := SourceCurrentClassEditDomains.rows_domains emptyGuard conjoin clear top record originals base known domains
      rows populated allowed ready resident (ordinary_rows safe)
    have constructor := SourceEqualityOpenOrdinaryHead.node rebuilt middle.native.machine.heap effects.1.native.semantic effects.2.2.1
    have finalValid := SourceQueryUnfoldMemo.valid_grows middle.native.machine.heap _ effects.1.native.semantic constructor.1 saved coherent
    have finalCosts := InternedFreshOrdinaryCostHeap.preserve middle.native.machine.heap _ middleCosts
      (InternedShallowHeap.makeNode_noNewMu rebuilt middle.native.machine.heap)
    have checkedValid : Valid heap saved := by simpa only [built] using finalValid
    have checkedCosts : CostHeap heap := by simpa only [built] using finalCosts
    exact ⟨saved, .ordinary (built := built) read, checkedValid, checkedCosts, retained, query⟩
  have recursiveCase : ∀ {entries original before exposed heap result after}
      (recursive : SourceEqualityRequiredGraph.Recursive original)
      (head : SourceEqualityRequiredHead.Head original before.native.machine.heap exposed heap)
      (body : EditNode emptyGuard conjoin clear top record originals (.editBelow entries) exposed (advanceHeap before heap) result after),
      NodeLaw body → NodeLaw (.recursive recursive head body) := by
    intro entries original before exposed heap result after recursive head body ih populated nonempty allowed ready available safe costs memos valid
    have closed := recursive_closed recursive nonempty safe
    have first := head.verified ready.native.semantic.ready available closed
    have semantic := SourceEqualityRequiredSemanticCache.head head ready.native.semantic available closed
    have physical := SourceCurrentRequiredHeapEffects.head (fun _ => True) head ready.native.semantic costs
      (by intro _ _ _; trivial) available
    obtain ⟨middle, headReads, coherent, retained, query⟩ :=
      SourceCurrentRequiredQueryMemos.head_memos head ready.native.semantic costs available memos valid
    obtain ⟨saved, bodyReads, finalValid, finalCosts, later, finalQuery⟩ := ih populated nonempty allowed
      (ready.heap heap first.1 semantic) first.2.1 (closed_safe _ exposed heap semantic first.2.1 first.2.2.1)
      physical.2.2.1 middle coherent
    exact ⟨saved, .recursive (recursive := recursive) headReads bodyReads, finalValid, finalCosts,
      extends_trans retained later, finalQuery.trans query⟩
  have nilChildren : ∀ {entries offset state}, ChildrenLaw (EditChildren.nil (entries := entries) (index := offset) (state := state)) := by
    intro entries offset state _ _ _ _ _ costs memos valid
    exact ⟨memos, .nil, valid, costs, extends_refl _, rfl⟩
  have unselectedCase : ∀ {entries values before results after value} (offset : Nat)
      (absent : SourceEqualityNeededMap.lookup (offset : Int) entries = none)
      (rest : EditChildren emptyGuard conjoin clear top record originals entries (offset + 1) values before results after),
      ChildrenLaw rest → ChildrenLaw (.unselected (value := value) offset absent rest) := by
    intro entries values before results after value offset absent rest ih populated allowed ready available safe costs memos valid
    obtain ⟨saved, read, coherent, finalCosts, retained, query⟩ := ih populated allowed ready
      (fun value member => available value (List.mem_cons_of_mem _ member)) (children_tail safe) costs memos valid
    exact ⟨saved, .unselected (absent := absent) read, coherent, finalCosts, retained, query⟩
  have selectedCase : ∀ {entries edits value before result middle values results after} (offset : Nat)
      (found : SourceEqualityNeededMap.lookup (offset : Int) entries = some edits)
      (first : EditNode emptyGuard conjoin clear top record originals edits value before result middle)
      (rest : EditChildren emptyGuard conjoin clear top record originals entries (offset + 1) values middle results after),
      NodeLaw first → ChildrenLaw rest → ChildrenLaw (.selected offset found first rest) := by
    intro entries edits value before result middle values results after offset found first rest firstIH restIH populated allowed ready available safe costs memos valid
    have member := SourceEqualityNeededMap.lookup_mem _ _ _ found
    have children := (show ∀ index child, (index, child) ∈ entries → Populated child ∧ HasLeaf child from by simpa only [Populated] using populated)
    have childAllowed : Allowed record edits := by
      have original := allowed
      rw [Allowed, All] at original
      exact original _ _ member
    have childSafe := safe 0 _ (by simpa using found) value rfl
    obtain ⟨middleMemo, own, coherent, middleCosts, retained, query⟩ := firstIH
      (children _ _ member).1 (children _ _ member).2 childAllowed ready (available _ List.mem_cons_self) childSafe costs memos valid
    have effects := SourceCurrentClassEditDomains.node_domains emptyGuard conjoin clear top record originals base known domains
      first (children _ _ member).1 (children _ _ member).2 childAllowed ready (available _ List.mem_cons_self) childSafe
    obtain ⟨saved, tail, finalValid, finalCosts, later, finalQuery⟩ := restIH populated allowed effects.1
      (fun value member => effects.2.1.available value (available value (List.mem_cons_of_mem _ member)))
      (children_tail safe) middleCosts middleMemo coherent
    exact ⟨saved, .selected (found := found) own tail, finalValid, finalCosts, extends_trans retained later, finalQuery.trans query⟩
  have nilRows : ∀ {entries state}, RowsLaw (EditRows.nil (entries := entries) (state := state)) := by
    intro entries state _ _ _ _ _ costs memos valid
    exact ⟨memos, .nil, valid, costs, extends_refl _, rfl⟩
  have consCase : ∀ {entries before values middle result heap edges results after} {edge : EdgeValue Symbol Guard}
      (children : EditChildren emptyGuard conjoin clear top record originals entries 0 edge.children before values middle)
      (rebuilt : run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.native.machine.heap = (result, heap))
      (rest : EditRows emptyGuard conjoin clear top record originals entries edges (advanceHeap middle heap) results after),
      ChildrenLaw children → RowsLaw rest → RowsLaw (.cons children rebuilt rest) := by
    intro entries before values middle result heap edges results after edge children rebuilt rest childIH restIH populated allowed ready resident safe costs memos valid
    have available := ready.native.semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident _ List.mem_cons_self)
    obtain ⟨middleMemo, own, coherent, middleCosts, retained, query⟩ := childIH populated allowed ready available (safe _ List.mem_cons_self) costs memos valid
    have effects := SourceCurrentClassEditDomains.children_domains emptyGuard conjoin clear top record originals base known domains
      children populated allowed ready available (safe _ List.mem_cons_self)
    have constructor := SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle.native.machine.heap
      effects.1.native.semantic.ready effects.2.2.1
    have semantic := SourceEqualityRequiredSemanticCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle.native.machine.heap
      effects.1.native.semantic effects.2.2.1
    have kept : Keeps middle.native.machine.heap heap := by simpa only [rebuilt] using constructor.1
    have heapSemantic : SemanticReady heap := by simpa only [rebuilt] using semantic
    have heapCosts : CostHeap heap := by
      have same : CostHeap (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.native.machine.heap).2 := middleCosts
      simpa only [rebuilt] using same
    have heapValid := SourceQueryUnfoldMemo.valid_grows _ heap effects.1.native.semantic kept middleMemo coherent
    obtain ⟨saved, tail, finalValid, finalCosts, later, finalQuery⟩ := restIH populated allowed (effects.1.heap heap kept heapSemantic)
      (fun edge member => InternedEdgeResidency.edge_grows _ _ (effects.2.1.trans kept).growth edge
        (resident edge (List.mem_cons_of_mem _ member)))
      (fun edge member => safe edge (List.mem_cons_of_mem _ member)) heapCosts middleMemo heapValid
    exact ⟨saved, .cons (rebuilt := rebuilt) own tail, finalValid, finalCosts, extends_trans retained later, finalQuery.trans query⟩
  refine ⟨?_, ?_, ?_⟩
  · intro edits value before result after trace
    exact EditNode.rec
      (motive_1 := fun _ _ _ _ _ trace => NodeLaw trace)
      (motive_2 := fun _ _ _ _ _ _ trace => ChildrenLaw trace)
      (motive_3 := fun _ _ _ _ _ trace => RowsLaw trace)
      leafCase emptyCase ordinaryCase recursiveCase nilChildren unselectedCase selectedCase nilRows consCase trace
  · intro entries offset values before results after trace
    exact EditChildren.rec
      (motive_1 := fun _ _ _ _ _ trace => NodeLaw trace)
      (motive_2 := fun _ _ _ _ _ _ trace => ChildrenLaw trace)
      (motive_3 := fun _ _ _ _ _ trace => RowsLaw trace)
      leafCase emptyCase ordinaryCase recursiveCase nilChildren unselectedCase selectedCase nilRows consCase trace
  · intro entries edges before results after trace
    exact EditRows.rec
      (motive_1 := fun _ _ _ _ _ trace => NodeLaw trace)
      (motive_2 := fun _ _ _ _ _ _ trace => ChildrenLaw trace)
      (motive_3 := fun _ _ _ _ _ trace => RowsLaw trace)
      leafCase emptyCase ordinaryCase recursiveCase nilChildren unselectedCase selectedCase nilRows consCase trace

/-- Every actual shared node edit derives exact global reads and final coherence from its original path domains. -/
theorem node_memos {edits value before result after}
    (trace : EditNode (width := width) emptyGuard conjoin clear top record originals edits value before result after) : NodeLaw trace :=
  (witnesses emptyGuard conjoin clear top record originals base known domains).1 _ _ _ _ _ trace

/-- Ordered actual child edits derive coherent final tables without closing unselected children. -/
theorem children_memos {entries offset values before results after}
    (trace : EditChildren (width := width) emptyGuard conjoin clear top record originals entries offset values before results after) : ChildrenLaw trace :=
  (witnesses emptyGuard conjoin clear top record originals base known domains).2.1 _ _ _ _ _ _ trace

/-- Actual row reconstruction derives each ordered memo receipt and retains the final cost invariant. -/
theorem rows_memos {entries edges before results after}
    (trace : EditRows (width := width) emptyGuard conjoin clear top record originals entries edges before results after) : RowsLaw trace :=
  (witnesses emptyGuard conjoin clear top record originals base known domains).2.2 _ _ _ _ _ trace

end MicroCFTA.SourceCurrentClassEditQueryMemos

namespace MicroCFTA.SourceCurrentClassEditQueryMemos
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityEdits SourceEqualityEditLeafPaths
open SourceEqualitySharedEditGraph SourceEqualitySharedTargetState SourceEqualitySharedEditEffects SourceCurrentEditDomains
open SourceEqualityProjectionPathDomain SourceEqualityClassFoldGraph
open SourceCurrentSubsumesQueryMemos (Effect)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- Child-list receipts retain the source ignored-leaf and actual selected-child branches. -/
inductive ListReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) :
    {edits : Edits EqualityNormalize.Path} → {values : List (Value Symbol Guard)} → {before : SharedState width Symbol Guard} →
    {results : List (Value Symbol Guard)} → {after : SharedState width Symbol Guard} →
    EditList emptyGuard conjoin clear top record originals edits values before results after → Memos → Memos → Prop where
  | leaf : ListReads emptyGuard conjoin clear top record originals .leaf memos memos
  | children (read : ChildrenReads emptyGuard conjoin clear top record originals actual memos saved) :
      ListReads emptyGuard conjoin clear top record originals (.children actual) memos saved

/-- A class receipt retains its actual current capture and fresh unforced target slots. -/
inductive ClassReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat} :
    {emptyGuard : Guard} → {conjoin : Guard → Guard → Guard} → {clear : Guard → Bool} → {top : Guard} →
    {record : SourceEqualityClassOrder.Record} → {values results : List (Value Symbol Guard)} →
    {before after : NativeState width Symbol Guard} →
    Class emptyGuard conjoin clear top record values before results after → Memos → Memos → Prop where
  | edit {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
      {record : SourceEqualityClassOrder.Record} {values results : List (Value Symbol Guard)}
      {before : NativeState width Symbol Guard} {shared : SharedState width Symbol Guard}
      {actual : EditList emptyGuard conjoin clear top record values (SourceEqualityClassFoldGraph.edits record)
        values (initial before) results shared} {memos saved : Memos}
      (read : ListReads emptyGuard conjoin clear top record values actual memos saved) :
      ClassReads (.edit actual) memos saved

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

/-- Actual list edits derive their reads from original selected child domains. -/
theorem list_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
    (base : InternedConstructorTemplates.State Symbol Guard) (known : Values base originals)
    (domains : ∀ p ∈ record.paths, ForestClosed (p.map Int.ofNat) originals)
    {edits : Edits EqualityNormalize.Path} {values results : List (Value Symbol Guard)}
    {before after : SharedState width Symbol Guard}
    (actual : EditList emptyGuard conjoin clear top record originals edits values before results after)
    (populated : Populated edits) (allowed : Allowed record edits)
    (ready : Ready emptyGuard conjoin clear top record originals base before) (available : Values before.native.machine.heap values)
    (safe : ∀ entries, edits = .editBelow entries → ChildrenSafe entries 0 values)
    (costs : CostHeap before.native.machine.heap) (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ saved, ListReads emptyGuard conjoin clear top record originals actual memos saved ∧
      Valid after.native.machine.heap saved ∧ CostHeap after.native.machine.heap ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  cases actual with
  | leaf => exact ⟨memos, .leaf, valid, costs, extends_refl _, rfl⟩
  | children actual =>
      obtain ⟨saved, reads, coherent, retainedCosts, retained, query⟩ :=
        children_memos emptyGuard conjoin clear top record originals base known domains actual
          populated allowed ready available (safe _ rfl) costs memos valid
      exact ⟨saved, .children reads, coherent, retainedCosts, retained, query⟩

/-- An actual class derives ordered global reads and coherent tables from its original selected paths. -/
theorem class_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values results : List (Value Symbol Guard)}
    {before after : NativeState width Symbol Guard}
    (actual : Class emptyGuard conjoin clear top record values before results after)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap)
    (available : Values before.machine.heap values) (domains : ∀ p ∈ record.paths, ForestClosed (p.map Int.ofNat) values)
    (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∃ saved, ClassReads actual memos saved ∧ Effect before.machine.heap after.machine.heap memos saved := by
  have supported := SourceEqualityClassEdits.coherent_supported record coherent
  have disjoint := SourceEqualityClassEdits.edits_disjoint record.paths supported id
  have originalDomains : ∀ path action, (path, action) ∈ SourceEqualityClassEdits.edits record.paths id → ForestClosed path values := by
    intro path action member
    obtain ⟨original, included, same⟩ := List.mem_map.mp member
    cases same
    exact domains original included
  have checked := SourceCurrentClassEditDomains.class_domains actual coherent active ready available domains
  cases actual with
  | edit actual =>
      have initialReady := initial_ready emptyGuard conjoin clear top record values before.machine.heap before ready
        (pure_keeps _ ready.semantic.ready)
      obtain ⟨saved, reads, finalValid, finalCosts, retained, query⟩ := list_memos record values before.machine.heap available domains actual
        (build_populated (SourceEqualityClassEdits.edits record.paths id)) (SourceEqualitySharedClassEdits.compiled_allowed record)
        initialReady available (fun entries compiled => compiled_safe _ disjoint values originalDomains entries compiled) costs memos valid
      exact ⟨saved, .edit reads, checked.2.1, checked.1.semantic, finalCosts, finalValid, retained, query⟩

end MicroCFTA.SourceCurrentClassEditQueryMemos
