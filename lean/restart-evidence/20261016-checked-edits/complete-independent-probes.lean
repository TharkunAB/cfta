import MicroCFTA.SourceCurrentAllocatedSharedEditComplete

#print axioms MicroCFTA.SourceCurrentAllocatedSharedEditComplete.node_complete
#print axioms MicroCFTA.SourceCurrentAllocatedSharedEditComplete.children_complete
#print axioms MicroCFTA.SourceCurrentAllocatedSharedEditComplete.list_complete
#check @MicroCFTA.SourceCurrentAllocatedSharedEditComplete.node_complete
#check @MicroCFTA.SourceCurrentAllocatedSharedEditComplete.children_complete
#check @MicroCFTA.SourceCurrentAllocatedSharedEditComplete.list_complete

namespace MicroCFTA.CheckedEditCompleteIndependentProbe
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityEdits SourceEqualityEditLeafPaths SourceEqualityProjectionPathDomain
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentEditDomains SourceCurrentAllocatedSharedEditGraph
open SourceCurrentAllocatedSharedEditRanges SourceCurrentAllocatedSharedEditEffects
open SourceCurrentAllocatedSharedEditComplete
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Inventory" => SourceCurrentAllocatedNativeInventoryState.Inventory
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "ValidMemo" => EndpointMemoGateTrace.Valid
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula)
variable (solver : SourceGuards.Entailment FullSyntax.Formula)
variable (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) (base : Heap)
variable (known : Values base originals)
variable (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) originals)
variable (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
variable (inventory : Inventory) (before : SharedState width)
variable (ready : Ready formulas solver inventory record originals base before)
variable (memos : Memos) (valid : ValidMemo before.checked.native.machine.heap memos)

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem leaf_safe (path : EqualityNormalize.Path) (value : Value Symbol Guard)
    (closed : value.free = []) : Safe (.editAt path) value := by
  intro suffix action member
  have same : suffix = [] ∧ action = path := by simpa only [leaves, List.mem_singleton, Prod.mk.injEq] using member
  rcases same with ⟨rfl, rfl⟩
  simpa only [NodeClosed] using closed

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem leaf_nonempty (path : EqualityNormalize.Path) : HasLeaf (.editAt path) :=
  ⟨[], path, by simp only [leaves, List.mem_singleton]⟩

include known domains coherent active inventory ready valid

-- Completion takes only actual target/leaf range checks and initial invariants.
theorem selected_leaf (path : EqualityNormalize.Path) (member : path ∈ record.paths)
    (value : Value Symbol Guard) (available : Available before.checked.native.machine.heap value)
    (closed : value.free = [])
    (ranges : SourceCurrentAllocatedSharedTargetLeaf.Ranges record originals path value before) :
    ∃ result after next final, ∃ actual : EditNode record originals (.editAt path) value before result after,
      NodeReads formulas solver base actual memos final ∧
      NodeReceipt formulas solver next record originals base value before result after memos final := by
  exact node_complete formulas solver record originals base known domains coherent active inventory
    (.leaf ranges) (by simp only [Populated]) (leaf_nonempty path)
    (by simpa only [Allowed, All] using member) ready available (leaf_safe path value closed) memos valid

-- A selected ordinary child can finish beside an unchanged open sibling.
theorem ordinary_child_open_sibling (path : EqualityNormalize.Path) (member : path ∈ record.paths)
    (entry : Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (available : Available before.checked.native.machine.heap (.node entry edges depth free))
    (closed : (Value.node entry edges depth free : Value Symbol Guard).free = [])
    (sibling : Value Symbol Guard) (openSibling : sibling.free ≠ [])
    (ranges : SourceCurrentAllocatedSharedTargetLeaf.Ranges record originals path (.node entry edges depth free) before) :
    ∃ result after next final,
      NodeReceipt formulas solver next record originals base (.node entry edges depth free) before result after memos final ∧
      ∃ actual : EditChildren record originals [(1, .editAt path)] 0
        [sibling, .node entry edges depth free] before [sibling, result] after,
        ChildrenReads formulas solver base actual memos final ∧ sibling.free ≠ [] := by
  obtain ⟨result, after, next, final, actual, read, receipt⟩ := selected_leaf formulas solver record originals base
    known domains coherent active inventory before ready memos valid path member _ available closed ranges
  have tail : EditChildren record originals [(1, .editAt path)] 1 [Value.node entry edges depth free] before [result] after :=
    .selected 1 (by simp [SourceEqualityNeededMap.lookup]) actual .nil
  have tailRead : ChildrenReads formulas solver base tail memos final :=
    .selected (found := by simp [SourceEqualityNeededMap.lookup]) (first := actual) (rest := .nil) read .nil
  have whole : EditChildren record originals [(1, .editAt path)] 0
      [sibling, .node entry edges depth free] before [sibling, result] after :=
    .unselected 0 (by simp [SourceEqualityNeededMap.lookup]) tail
  exact ⟨result, after, next, final, receipt, whole,
    .unselected (absent := by simp [SourceEqualityNeededMap.lookup]) (rest := tail) tailRead, openSibling⟩

-- Recursive exposure constructs the actual head events before the body at that heap.
theorem recursive_head_globals (entries : List (Int × Edits EqualityNormalize.Path))
    (original : Value Symbol Guard) (recursive : SourceEqualityRequiredGraph.Recursive original)
    (populated : Populated (.editBelow entries)) (nonempty : HasLeaf (.editBelow entries))
    (allowed : Allowed record (.editBelow entries))
    (available : Available before.checked.native.machine.heap original) (safe : Safe (.editBelow entries) original)
    (bodyRanges : ∀ exposed heap, SourceEqualityRequiredHead.Head original before.checked.native.machine.heap exposed heap →
      NodeRanges record originals (.editBelow entries) exposed (advanceHeap before heap)) :
    ∃ exposed heap current result after next final,
      ∃ head : SourceEqualityRequiredHead.Head original before.checked.native.machine.heap exposed heap,
      ∃ body : EditNode record originals (.editBelow entries) exposed (advanceHeap before heap) result after,
      SourceCurrentRequiredQueryMemos.HeadReads head memos current ∧
      SourceCurrentSubsumesQueryMemos.Effect before.checked.native.machine.heap heap memos current ∧
      NodeReads formulas solver base body current final ∧
      NodeReceipt formulas solver next record originals base original before result after memos final := by
  have closed := recursive_closed recursive nonempty safe
  obtain ⟨exposed, heap, head, _, exposedAvailable, exposedClosed, _⟩ :=
    SourceEqualityRequiredHead.complete original before.checked.native.machine.heap ready.checked.semantic.ready available closed
  have physical := head_physical ready head available
  obtain ⟨current, headRead, headValid, retained, queries⟩ := SourceCurrentRequiredQueryMemos.head_memos
    head ready.checked.semantic ready.checked.costs available memos valid
  have headGlobal : SourceCurrentSubsumesQueryMemos.Effect before.checked.native.machine.heap heap memos current :=
    ⟨physical.2.1.keeps, physical.1.checked.semantic, physical.1.checked.costs, headValid, retained, queries⟩
  obtain ⟨result, after, _, final, body, bodyRead, _⟩ := node_complete
    formulas solver record originals base known domains coherent active inventory (bodyRanges exposed heap head)
    populated nonempty allowed physical.1 exposedAvailable
    (closed_safe _ exposed heap physical.1.checked.semantic exposedAvailable exposedClosed) current headValid
  have whole : EditNode record originals (.editBelow entries) original before result after := .recursive recursive head body
  have read : NodeReads formulas solver base whole memos final :=
    .recursive (recursive := recursive) (head := head) (body := body) headRead headGlobal bodyRead
  obtain ⟨next, receipt⟩ := node_effects read populated nonempty allowed ready available safe valid
  exact ⟨exposed, heap, current, result, after, next, final, head, body, headRead, headGlobal, bodyRead, receipt⟩

-- The public finite list endpoint needs no native word-range check for a root callback.
theorem list_root_no_native_ranges (path : EqualityNormalize.Path) (member : path ∈ record.paths)
    (values : List (Value Symbol Guard)) (available : Values before.checked.native.machine.heap values) :
    ∃ next, ∃ actual : EditList record originals (.editAt path) values before values before,
      ListReads formulas solver base actual memos memos ∧
      ChildrenReceipt formulas solver next record originals base values before values before memos memos := by
  obtain ⟨results, after, next, final, actual, read, receipt⟩ := list_complete
    formulas solver record originals base known domains coherent active inventory
    (edits := .editAt path) (by trivial) (by simp only [Populated])
    (by simpa only [Allowed, All] using member) ready available trivial memos valid
  cases actual with
  | leaf =>
      cases read with
      | leaf => exact ⟨next, .leaf, .leaf, receipt⟩

-- A second selected call uses the first call's computed inventory and global bundle.
theorem two_selected_inventories (firstPath secondPath : EqualityNormalize.Path)
    (firstMember : firstPath ∈ record.paths) (secondMember : secondPath ∈ record.paths)
    (first second : Value Symbol Guard)
    (firstAvailable : Available before.checked.native.machine.heap first)
    (secondAvailable : Available before.checked.native.machine.heap second)
    (firstClosed : first.free = []) (secondClosed : second.free = [])
    (firstRanges : SourceCurrentAllocatedSharedTargetLeaf.Ranges record originals firstPath first before)
    (secondRanges : ∀ result middle, EditNode record originals (.editAt firstPath) first before result middle →
      SourceCurrentAllocatedSharedTargetLeaf.Ranges record originals secondPath second middle) :
    ∃ firstResult middle firstInventory current secondResult after next final,
      NodeReceipt formulas solver firstInventory record originals base first before firstResult middle memos current ∧
      NodeReceipt formulas solver next record originals base second middle secondResult after current final ∧
      ∃ actual : EditChildren record originals [(0, .editAt firstPath), (1, .editAt secondPath)] 0
        [first, second] before [firstResult, secondResult] after,
        ChildrenReads formulas solver base actual memos final := by
  obtain ⟨firstResult, middle, firstInventory, current, firstActual, firstRead, firstReceipt⟩ :=
    selected_leaf formulas solver record originals base known domains coherent active inventory before ready memos valid
      firstPath firstMember first firstAvailable firstClosed firstRanges
  obtain ⟨secondResult, after, next, final, secondActual, secondRead, secondReceipt⟩ :=
    selected_leaf formulas solver record originals base known domains coherent active firstInventory middle firstReceipt.ready current
      firstReceipt.globals.valid secondPath secondMember second
      (firstReceipt.effects.keeps.available second secondAvailable) secondClosed
      (secondRanges firstResult middle firstActual)
  have tail : EditChildren record originals [(0, .editAt firstPath), (1, .editAt secondPath)] 1
      [second] middle [secondResult] after :=
    .selected 1 (by simp [SourceEqualityNeededMap.lookup]) secondActual .nil
  have tailRead : ChildrenReads formulas solver base tail current final :=
    .selected (found := by simp [SourceEqualityNeededMap.lookup]) (first := secondActual) (rest := .nil) secondRead .nil
  have whole : EditChildren record originals [(0, .editAt firstPath), (1, .editAt secondPath)] 0
      [first, second] before [firstResult, secondResult] after :=
    .selected 0 (by simp [SourceEqualityNeededMap.lookup]) firstActual tail
  exact ⟨firstResult, middle, firstInventory, current, secondResult, after, next, final,
    firstReceipt, secondReceipt, whole,
    .selected (found := by simp [SourceEqualityNeededMap.lookup]) (first := firstActual) (rest := tail) firstRead tailRead⟩

end MicroCFTA.CheckedEditCompleteIndependentProbe

#print axioms MicroCFTA.CheckedEditCompleteIndependentProbe.selected_leaf
#print axioms MicroCFTA.CheckedEditCompleteIndependentProbe.ordinary_child_open_sibling
#print axioms MicroCFTA.CheckedEditCompleteIndependentProbe.recursive_head_globals
#print axioms MicroCFTA.CheckedEditCompleteIndependentProbe.list_root_no_native_ranges
#print axioms MicroCFTA.CheckedEditCompleteIndependentProbe.two_selected_inventories
