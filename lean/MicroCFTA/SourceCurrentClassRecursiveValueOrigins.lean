import MicroCFTA.SourceCurrentClassStructuralOrigins

/-!
# Exact recursive values through actual node edits

Literal ordinary children retain the same child path and complete value,
or an actual native or Head event supplies that value. The relation does
not follow stored Mu bodies, union members or observational unfolding.
It does not assert a complete selected-reader continuation or a rank.
-/
namespace MicroCFTA.SourceCurrentClassRecursiveValueOrigins
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceEqualityEdits SourceEqualityEditLeafPaths SourceCurrentEditDomains
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentAllocatedSharedEditGraph SourceCurrentAllocatedSharedEditEffects
open SourceCurrentNativeEdgeWriterGrowth (History)
open SourceCurrentClassStructuralOrigins (Event ChildEvent RowEvent)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "SharedReady" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Inventory" => SourceCurrentAllocatedNativeInventoryState.Inventory
local notation "Memos" => EndpointMemoGateTrace.Memos

/-- A literal value lies at this child path through ordinary rows only. -/
inductive Occurs : Node → List Nat → Node → Prop where
  /-- The root retains the complete value. -/
  | root (value : Node) : Occurs value [] value
  /-- A child retains its exact canonical row and natural child position. -/
  | child {entry edges depth free} (rowIndex childIndex : Nat) (row : Edge) (child : Node)
      (selected : edges[rowIndex]? = some row) (chosen : row.children[childIndex]? = some child)
      {path needle} (rest : Occurs child path needle) :
      Occurs (.node entry edges depth free) (childIndex :: path) needle

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

private def NodeLaw (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (base : Heap)
    {record originals edits input before result after}
    (actual : EditNode (width := width) record originals edits input before result after) (memos : Memos) : Prop :=
  ∀ inventory, Populated edits → HasLeaf edits → Allowed record edits →
    SharedReady formulas solver inventory record originals base before → Available before.checked.native.machine.heap input →
    Safe edits input → EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos → History before.checked →
    ∀ path needle, SourceEqualityRequiredGraph.Recursive needle → Occurs result path needle →
      Occurs input path needle ∨ ∃ event suffix, Event formulas solver base actual event ∧ Occurs event suffix needle

private def ChildrenLaw (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (base : Heap)
    {record originals entries offset inputs before results after}
    (actual : EditChildren (width := width) record originals entries offset inputs before results after) (memos : Memos) : Prop :=
  ∀ inventory, Populated (.editBelow entries) → Allowed record (.editBelow entries) →
    SharedReady formulas solver inventory record originals base before → Values before.checked.native.machine.heap inputs →
    ChildrenSafe entries offset inputs → EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos → History before.checked →
    ∀ childIndex child, results[childIndex]? = some child → ∀ path needle,
      SourceEqualityRequiredGraph.Recursive needle → Occurs child path needle →
      (∃ original, inputs[childIndex]? = some original ∧ Occurs original path needle) ∨
        ∃ event suffix, ChildEvent formulas solver base actual childIndex event ∧ Occurs event suffix needle

private def RowsLaw (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (base : Heap)
    {record originals entries inputs before results after}
    (actual : EditRows (width := width) record originals entries inputs before results after) (memos : Memos) : Prop :=
  ∀ inventory, Populated (.editBelow entries) → Allowed record (.editBelow entries) →
    SharedReady formulas solver inventory record originals base before → Edges before.checked.native.machine.heap inputs →
    RowsSafe entries inputs → EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos → History before.checked →
    ∀ rawIndex output, results[rawIndex]? = some output →
    ∃ original, inputs[rawIndex]? = some original ∧
      ∀ childIndex child, output.children[childIndex]? = some child → ∀ path needle,
        SourceEqualityRequiredGraph.Recursive needle → Occurs child path needle →
        (∃ inputChild, original.children[childIndex]? = some inputChild ∧ Occurs inputChild path needle) ∨
          ∃ event suffix, RowEvent formulas solver base actual rawIndex childIndex event ∧ Occurs event suffix needle

set_option maxHeartbeats 2400000 in
private theorem node_law {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {base : Heap}
    {record originals edits input before result after memos final}
    {actual : EditNode (width := width) record originals edits input before result after}
    (reads : NodeReads formulas solver base actual memos final) : NodeLaw formulas solver base actual memos := by
  refine NodeReads.rec
    (motive_1 := fun {record originals edits input before result after} actual memos _ _ =>
      NodeLaw formulas solver base actual memos)
    (motive_2 := fun {record originals entries offset inputs before results after} actual memos _ _ =>
      ChildrenLaw formulas solver base actual memos)
    (motive_3 := fun {record originals entries inputs before results after} actual memos _ _ =>
      RowsLaw formulas solver base actual memos)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ reads
  · intro next record originals path input before result after memos saved receipt
      inventory populated nonempty allowed ready available safe valid history positions needle recursive occurrence
    exact .inr ⟨result,positions,.leaf receipt.reads history,occurrence⟩
  · intro record originals entries state memos inventory populated nonempty allowed ready available safe valid history
      positions needle recursive occurrence
    cases occurrence with
    | root => cases recursive
  · intro record originals memos saved entries edges before rebuilt middle value heap entry depth free actual built read ih
      inventory populated nonempty allowed ready available safe valid history positions needle recursive occurrence
    have facts := ready.checked.semantic.ready.semantic.1.normal.facts
    have resident := resident_edges _ facts.linked _ available.resident
    obtain ⟨next,receipt⟩ := rows_effects read populated allowed ready resident (ordinary_rows safe) valid
    have nextFacts := receipt.ready.checked.semantic.ready.semantic.1.normal.facts
    have equalEdges : nodeEdges value = canonicalEdges (surviving rebuilt) := by
      simpa only [built] using EqualityLeafProjectionPhysical.makeNode_edges rebuilt middle.checked.native.machine.heap
        nextFacts.coherent nextFacts.linked receipt.available
    have ordinary : SourceEqualityRequiredCache.Ordinary value := by
      simpa only [built] using SourceEqualityRequiredCache.node_ordinary rebuilt middle.checked.native.machine.heap
        nextFacts receipt.available
    cases occurrence with
    | root =>
      cases value with
      | empty | node => cases recursive
      | reference | union | mu => cases ordinary
    | @child outEntry outEdges outDepth outFree outputIndex childIndex parent child selected chosen path needle rest =>
      have present : parent ∈ outEdges := List.mem_of_getElem? selected
      have normalized : outEdges = canonicalEdges (surviving rebuilt) := by
        simpa only [nodeEdges] using equalEdges
      rw [normalized] at present
      obtain ⟨rawIndex,raw⟩ := List.mem_iff_getElem?.mp
        (List.mem_filter.mp (canonicalEdges_member _ parent present)).1
      obtain ⟨original,found,children⟩ := ih inventory populated allowed ready resident (ordinary_rows safe)
        valid history rawIndex parent raw
      rcases children childIndex child chosen _ needle recursive rest with source | event
      · obtain ⟨inputChild,inputFound,sourceAt⟩ := source
        exact .inl (.child rawIndex childIndex original inputChild found inputFound sourceAt)
      · obtain ⟨event,suffix,eventAt,sourceAt⟩ := event
        exact .inr ⟨event,suffix,
          .ordinary (built := built) read outputIndex rawIndex childIndex parent selected raw eventAt,sourceAt⟩
  · intro record originals memos current saved entries original before exposed heap value after recursiveInput head body
      headRead headGlobal bodyRead ih inventory populated nonempty allowed ready available safe valid history
      positions needle recursive occurrence
    have closed := recursive_closed recursiveInput nonempty safe
    have first := head_physical ready head available
    have checked := head.verified ready.checked.semantic.ready available closed
    have found := ih inventory populated nonempty allowed first.1 first.2.2
      (closed_safe _ exposed heap first.1.checked.semantic first.2.2 checked.2.2.1) headGlobal.valid
      (history.advance _ headGlobal.keeps.growth) positions needle recursive occurrence
    rcases found with source | event
    · exact .inr ⟨exposed,positions,.head (recursive := recursiveInput) headRead bodyRead history,source⟩
    · obtain ⟨event,path,eventAt,sourceAt⟩ := event
      exact .inr ⟨event,path,.recursive (recursive := recursiveInput) (head := head) eventAt,sourceAt⟩
  · intro record originals entries offset state memos inventory populated allowed ready available safe valid history
      childIndex child selected path needle recursive occurrence
    simp at selected
  · intro record originals memos saved entries values before results after original offset absent rest read ih
      inventory populated allowed ready available safe valid history childIndex child selected path needle recursive occurrence
    cases childIndex with
    | zero =>
      have same : original = child := by simpa using selected
      subst child
      exact .inl ⟨original,rfl,occurrence⟩
    | succ childIndex =>
      have found := ih inventory populated allowed ready
        (fun value present => available value (List.mem_cons_of_mem _ present)) (children_tail safe) valid history
        childIndex child (by simpa using selected) path needle recursive occurrence
      rcases found with source | event
      · obtain ⟨original,present,source⟩ := source
        exact .inl ⟨original,by simpa using present,source⟩
      · obtain ⟨event,suffix,eventAt,sourceAt⟩ := event
        exact .inr ⟨event,suffix,.unselected (absent := absent) eventAt,sourceAt⟩
  · intro record originals memos current saved entries edits original before result middle values results after offset found first rest
      firstRead restRead firstIH ih inventory populated allowed ready available safe valid history
      childIndex child selected path needle recursive occurrence
    have present := SourceEqualityNeededMap.lookup_mem _ _ _ found
    have support := (show ∀ index child, (index,child) ∈ entries → Populated child ∧ HasLeaf child from
      by simpa only [Populated] using populated) _ _ present
    have childAllowed : Allowed record edits := by
      rw [Allowed,All] at allowed
      exact allowed _ _ present
    have childSafe : Safe edits original := safe 0 _ (by simpa using found) original rfl
    cases childIndex with
    | zero =>
      have same : result = child := by simpa using selected
      subst child
      have childResult := firstIH inventory support.1 support.2 childAllowed ready
        (available _ List.mem_cons_self) childSafe valid history path needle recursive occurrence
      rcases childResult with source | event
      · exact .inl ⟨original,rfl,source⟩
      · obtain ⟨event,suffix,eventAt,sourceAt⟩ := event
        exact .inr ⟨event,suffix,.here (rest := rest) (found := found) eventAt,sourceAt⟩
    | succ childIndex =>
      obtain ⟨next,receipt⟩ := node_effects firstRead support.1 support.2 childAllowed ready
        (available _ List.mem_cons_self) childSafe valid
      have oneRead : ChildrenReads formulas solver base
          (EditChildren.selected offset found first EditChildren.nil) memos current :=
        .selected (found := found) firstRead .nil
      have nextHistory := (SourceCurrentParentNativeHistory.edit_children oneRead history
        ready.checked.semantic.ready.semantic.1.normal.facts.coherent.valid).1
      have childResult := ih next populated allowed receipt.ready
        (fun value present => receipt.effects.keeps.available value (available value (List.mem_cons_of_mem _ present)))
        (children_tail safe) receipt.globals.valid nextHistory childIndex child (by simpa using selected)
        path needle recursive occurrence
      rcases childResult with source | event
      · obtain ⟨original,present,source⟩ := source
        exact .inl ⟨original,by simpa using present,source⟩
      · obtain ⟨event,suffix,eventAt,sourceAt⟩ := event
        exact .inr ⟨event,suffix,.selected (first := first) (found := found) eventAt,sourceAt⟩
  · intro record originals entries state memos inventory populated allowed ready resident safe valid history rawIndex output selected
    simp at selected
  · intro record originals memos current saved entries before values middle result heap edges results after edge children built rest
      firstRead restRead firstIH ih inventory populated allowed ready resident safe valid history rawIndex output selected
    have facts := ready.checked.semantic.ready.semantic.1.normal.facts
    have childAvailable := facts.cached.edges edge.entry.key edge (resident _ List.mem_cons_self)
    obtain ⟨middleInventory,receipt⟩ := children_effects firstRead populated allowed ready childAvailable
      (safe _ List.mem_cons_self) valid
    have fields := MergedPhysicalGroupEdges.makeEdge_fields middle.checked.native.machine.heap
      receipt.ready.checked.semantic.ready.semantic.1.normal.facts edge.entry.key.symbol edge.entry.key.constraint values receipt.available
    have sameChildren : result.children = values := by simpa only [built] using fields.2.2
    cases rawIndex with
    | zero =>
      have same : result = output := by simpa using selected
      subst output
      refine ⟨edge,rfl,?_⟩
      intro childIndex child childSelected path needle recursive occurrence
      have chosen : values[childIndex]? = some child := by simpa only [sameChildren] using childSelected
      have childResult := firstIH inventory populated allowed ready childAvailable (safe _ List.mem_cons_self)
        valid history childIndex child chosen path needle recursive occurrence
      rcases childResult with source | event
      · exact .inl source
      · obtain ⟨event,suffix,eventAt,sourceAt⟩ := event
        exact .inr ⟨event,suffix,
          .here (built := built) (rest := rest) firstRead childIndex child chosen
            (SourceCurrentSharedEditChildLineage.indexed firstRead chosen) eventAt,sourceAt⟩
    | succ rawIndex =>
      have oneRead : RowsReads formulas solver base (EditRows.cons children built EditRows.nil) memos current :=
        .cons (rebuilt := built) firstRead .nil
      obtain ⟨next,firstReceipt⟩ := rows_effects oneRead populated allowed ready
        (fun row present => resident row (List.mem_cons.mpr (.inl (by simpa using present))))
        (fun row present => safe row (List.mem_cons.mpr (.inl (by simpa using present)))) valid
      have nextHistory := (SourceCurrentParentNativeHistory.edit_rows oneRead history facts.coherent.valid).1
      obtain ⟨original,present,childrenResult⟩ := ih next populated allowed firstReceipt.ready
        (fun row present => edge_grows _ _ firstReceipt.effects.keeps.growth row (resident row (List.mem_cons_of_mem _ present)))
        (fun row present => safe row (List.mem_cons_of_mem _ present)) firstReceipt.globals.valid nextHistory
        rawIndex output (by simpa using selected)
      refine ⟨original,by simpa using present,?_⟩
      intro childIndex child chosen path needle recursive occurrence
      rcases childrenResult childIndex child chosen path needle recursive occurrence with source | event
      · exact .inl source
      · obtain ⟨event,suffix,eventAt,sourceAt⟩ := event
        exact .inr ⟨event,suffix,.later (children := children) (built := built) eventAt,sourceAt⟩

/-- A recursive output value retains its exact source at the same child path or an actual event. -/
theorem node {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {base : Heap}
    {record originals edits input before result after memos final}
    {actual : EditNode (width := width) record originals edits input before result after}
    (reads : NodeReads formulas solver base actual memos final)
    (inventory : Inventory) (populated : Populated edits) (nonempty : HasLeaf edits) (allowed : Allowed record edits)
    (ready : SharedReady formulas solver inventory record originals base before)
    (available : Available before.checked.native.machine.heap input) (safe : Safe edits input)
    (valid : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos) (history : History before.checked)
    {positions needle} (recursive : SourceEqualityRequiredGraph.Recursive needle)
    (occurrence : Occurs result positions needle) :
    Occurs input positions needle ∨
      ∃ event suffix, Event formulas solver base actual event ∧ Occurs event suffix needle :=
  node_law reads inventory populated nonempty allowed ready available safe valid history positions needle recursive occurrence

end MicroCFTA.SourceCurrentClassRecursiveValueOrigins
