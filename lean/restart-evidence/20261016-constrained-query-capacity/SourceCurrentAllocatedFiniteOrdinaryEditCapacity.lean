import MicroCFTA.SourceCurrentAllocatedFiniteOrdinarySharedCapacity
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEdits
import MicroCFTA.SourceCurrentAllocatedSharedEditComplete
import MicroCFTA.SourceCurrentAllocatedSharedEditWorkerCompletion

/-!
# Numeric capacity at actual edit prefixes

Plans inspect only earlier completed children and rows. The first range
plan is derived before its finite prefix is constructed. Exact worker
returns align that prefix with the supplied earlier graph. Its receipts
then derive the state facts for the suffix. No enclosing execution or
future returned-state invariant is a plan premise.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEditCapacity
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityEdits SourceEqualityEditLeafPaths SourceEqualityProjectionPathDomain
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentEditDomains SourceCurrentAllocatedSharedEditGraph
open SourceCurrentAllocatedSharedEditRanges SourceCurrentAllocatedSharedEditEffects
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Stored" => SourceCurrentAllocatedFiniteOrdinaryShared.Stored
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
local notation "DRows" => SourceCurrentAllocatedFiniteOrdinaryDomain.Rows
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "GlobalValid" => EndpointMemoGateTrace.Valid
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

mutual
  /-- Each selected leaf checks numeric capacity at its actual force and query entries. -/
  inductive NodeCapacity (bits : Nat) (record : SourceEqualityClassOrder.Record)
      (originals : List (Value Symbol Guard)) :
      Edits EqualityNormalize.Path → Value Symbol Guard → SharedState (bits + 2) → Prop where
    | leaf (capacity : SourceCurrentAllocatedFiniteOrdinarySharedCapacity.LeafCapacity
        bits record originals target value before) :
        NodeCapacity bits record originals (.editAt target) value before
    | empty : NodeCapacity bits record originals (.editBelow entries) .empty before
    | ordinary (rows : RowsCapacity bits record originals entries edges before) :
        NodeCapacity bits record originals (.editBelow entries) (.node entry edges depth free) before

  /-- A later child plan starts at the exact return of its earlier selected child. -/
  inductive ChildrenCapacity (bits : Nat) (record : SourceEqualityClassOrder.Record)
      (originals : List (Value Symbol Guard)) :
      List (Int × Edits EqualityNormalize.Path) → Nat → List (Value Symbol Guard) → SharedState (bits + 2) → Prop where
    | nil : ChildrenCapacity bits record originals entries index [] before
    | unselected (index : Nat) (absent : SourceEqualityNeededMap.lookup (index : Int) entries = none)
        (rest : ChildrenCapacity bits record originals entries (index + 1) values before) :
        ChildrenCapacity bits record originals entries index (value :: values) before
    | selected (index : Nat) (found : SourceEqualityNeededMap.lookup (index : Int) entries = some edits)
        (first : NodeCapacity bits record originals edits value before)
        (rest : ∀ result middle, EditNode record originals edits value before result middle →
          ChildrenCapacity bits record originals entries (index + 1) values middle) :
        ChildrenCapacity bits record originals entries index (value :: values) before

  /-- A later row plan includes the literal edge allocation after its earlier child edits. -/
  inductive RowsCapacity (bits : Nat) (record : SourceEqualityClassOrder.Record)
      (originals : List (Value Symbol Guard)) :
      List (Int × Edits EqualityNormalize.Path) → List (EdgeValue Symbol Guard) → SharedState (bits + 2) → Prop where
    | nil : RowsCapacity bits record originals entries [] before
    | cons (children : ChildrenCapacity bits record originals entries 0 edge.children before)
        (rest : ∀ values middle, EditChildren record originals entries 0 edge.children before values middle →
          RowsCapacity bits record originals entries edges (advanceHeap middle
            (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.checked.native.machine.heap).2)) :
        RowsCapacity bits record originals entries (edge :: edges) before
end

/-- The source ignores list-root callbacks. Only below-edits enter child capacity plans. -/
def ListCapacity (bits : Nat) (record : SourceEqualityClassOrder.Record)
    (originals : List (Value Symbol Guard)) (edits : Edits EqualityNormalize.Path)
    (values : List (Value Symbol Guard)) (before : SharedState (bits + 2)) : Prop :=
  match edits with
  | .editAt _ => True
  | .editBelow entries => ChildrenCapacity bits record originals entries 0 values before

private theorem node_unique {width : Nat} {record originals edits value before first after second later}
    (one : EditNode (width := width) record originals edits value before first after)
    (two : EditNode record originals edits value before second later) : first = second ∧ after = later := by
  obtain ⟨a, ha⟩ := SourceCurrentAllocatedSharedEditWorkerCompletion.stable_uniform
    (SourceCurrentAllocatedSharedEditWorkerCompletion.node_complete one)
  obtain ⟨b, hb⟩ := SourceCurrentAllocatedSharedEditWorkerCompletion.stable_uniform
    (SourceCurrentAllocatedSharedEditWorkerCompletion.node_complete two)
  exact SourceCurrentAllocatedSharedEditWorker.Outcome.done.inj
    ((ha (max a b) (Nat.le_max_left _ _)).symm.trans (hb (max a b) (Nat.le_max_right _ _)))

private theorem children_unique {width : Nat} {record originals entries index values before first after second later}
    (one : EditChildren (width := width) record originals entries index values before first after)
    (two : EditChildren record originals entries index values before second later) : first = second ∧ after = later := by
  obtain ⟨a, ha⟩ := SourceCurrentAllocatedSharedEditWorkerCompletion.stable_uniform
    (SourceCurrentAllocatedSharedEditWorkerCompletion.children_complete one)
  obtain ⟨b, hb⟩ := SourceCurrentAllocatedSharedEditWorkerCompletion.stable_uniform
    (SourceCurrentAllocatedSharedEditWorkerCompletion.children_complete two)
  exact SourceCurrentAllocatedSharedEditWorker.Outcome.done.inj
    ((ha (max a b) (Nat.le_max_left _ _)).symm.trans (hb (max a b) (Nat.le_max_right _ _)))

variable (bits : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
variable (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) (base : Heap)
variable (known : Values base originals) (capturedDomain : DChildren originals)
variable (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)

private def NodeLaw (edits : Edits EqualityNormalize.Path) (value : Value Symbol Guard)
    (before : SharedState (bits + 2)) : Prop :=
  Populated edits → HasLeaf edits → Allowed record edits → ∀ inventory,
    Ready formulas solver inventory record originals base before →
    Available before.checked.native.machine.heap value → Safe edits value → Stored before → DNode value →
    ∀ memos, GlobalValid before.checked.native.machine.heap memos → NodeRanges record originals edits value before

private def ChildrenLaw (entries : List (Int × Edits EqualityNormalize.Path)) (index : Nat)
    (values : List (Value Symbol Guard)) (before : SharedState (bits + 2)) : Prop :=
  Populated (.editBelow entries) → Allowed record (.editBelow entries) → ∀ inventory,
    Ready formulas solver inventory record originals base before →
    Values before.checked.native.machine.heap values → ChildrenSafe entries index values → Stored before → DChildren values →
    ∀ memos, GlobalValid before.checked.native.machine.heap memos → ChildrenRanges record originals entries index values before

private def RowsLaw (entries : List (Int × Edits EqualityNormalize.Path))
    (edges : List (EdgeValue Symbol Guard)) (before : SharedState (bits + 2)) : Prop :=
  Populated (.editBelow entries) → Allowed record (.editBelow entries) → ∀ inventory,
    Ready formulas solver inventory record originals base before →
    Edges before.checked.native.machine.heap edges → RowsSafe entries edges → Stored before → DRows edges →
    ∀ memos, GlobalValid before.checked.native.machine.heap memos → RowsRanges record originals entries edges before

local notation "NL" => NodeLaw bits formulas solver record originals base
local notation "CL" => ChildrenLaw bits formulas solver record originals base
local notation "RL" => RowsLaw bits formulas solver record originals base

include known capturedDomain coherent active

private theorem derive :
    (∀ edits value before, NodeCapacity bits record originals edits value before → NL edits value before) ∧
    (∀ entries index values before, ChildrenCapacity bits record originals entries index values before → CL entries index values before) ∧
    (∀ entries edges before, RowsCapacity bits record originals entries edges before → RL entries edges before) := by
  have leafCase : ∀ {target value before},
      SourceCurrentAllocatedFiniteOrdinarySharedCapacity.LeafCapacity bits record originals target value before →
      NL (.editAt target) value before := by
    intro target value before capacity _ _ allowed inventory ready available _ stored domain memos valid
    have member : target ∈ record.paths := by simpa only [Allowed, All] using allowed
    exact .leaf (SourceCurrentAllocatedFiniteOrdinarySharedCapacity.leaf_ranges bits formulas solver inventory
      ready known capturedDomain stored coherent active member available domain capacity memos valid)
  have emptyCase : ∀ {entries before}, NL (.editBelow entries) (.empty : Value Symbol Guard) before := by
    intro entries before _ _ _ _ _ _ _ _ _ _ _
    exact .empty
  have ordinaryCase : ∀ {entries edges before entry depth free},
      RowsCapacity bits record originals entries edges before → RL entries edges before →
      NL (.editBelow entries) (.node entry edges depth free) before := by
    intro entries edges before entry depth free _ ih populated _ allowed inventory ready available safe stored domain memos valid
    exact .ordinary (ih populated allowed inventory ready
      (InternedEdgeResidency.resident_edges _ ready.checked.semantic.ready.semantic.1.normal.facts.linked _ available.resident)
      (ordinary_rows safe) stored domain.rows memos valid)
  have nilChildren : ∀ {entries index before}, CL entries index ([] : List (Value Symbol Guard)) before := by
    intro entries index before _ _ _ _ _ _ _ _ _ _
    exact .nil
  have unselectedCase : ∀ {entries values before value} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = none →
      ChildrenCapacity bits record originals entries (index + 1) values before →
      CL entries (index + 1) values before → CL entries index (value :: values) before := by
    intro entries values before value index absent _ ih populated allowed inventory ready available safe stored domain memos valid
    cases domain with
    | cons first rest => exact .unselected index absent (ih populated allowed inventory ready
        (fun child member => available child (List.mem_cons_of_mem _ member)) (children_tail safe) stored rest memos valid)
  have selectedCase : ∀ {entries edits value before values} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = some edits →
      NodeCapacity bits record originals edits value before →
      (∀ result middle, EditNode record originals edits value before result middle →
        ChildrenCapacity bits record originals entries (index + 1) values middle) →
      NL edits value before →
      (∀ result middle, EditNode record originals edits value before result middle → CL entries (index + 1) values middle) →
      CL entries index (value :: values) before := by
    intro entries edits value before values index found _ _ firstIH restIH populated allowed inventory ready available safe stored domain memos valid
    have member := SourceEqualityNeededMap.lookup_mem _ _ _ found
    have childPopulated := (show ∀ index child, (index, child) ∈ entries → Populated child ∧ HasLeaf child from
      by simpa only [Populated] using populated) _ _ member
    have childAllowed : Allowed record edits := by rw [Allowed, All] at allowed; exact allowed _ _ member
    have firstSafe := safe 0 _ (by simpa using found) value rfl
    have valueDomain := domain.member value List.mem_cons_self
    have firstRanges := firstIH childPopulated.1 childPopulated.2 childAllowed inventory ready
      (available _ List.mem_cons_self) firstSafe stored valueDomain memos valid
    refine .selected index found firstRanges ?_
    intro result middle actual
    have domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) originals := fun path _ =>
      SourceCurrentAllocatedFiniteOrdinaryTarget.forest_closed _ ready.checked.semantic originals
        (fun value member => ready.captured.available value (known value member)) capturedDomain _
    obtain ⟨result', middle', next, current, constructed, reads, receipt⟩ :=
      SourceCurrentAllocatedSharedEditComplete.node_complete formulas solver record originals base known domains coherent active
        inventory firstRanges childPopulated.1 childPopulated.2 childAllowed ready
        (available _ List.mem_cons_self) firstSafe memos valid
    obtain ⟨rfl, rfl⟩ := node_unique actual constructed
    have returned := SourceCurrentAllocatedFiniteOrdinaryEdits.node reads childPopulated.1 childPopulated.2 childAllowed ready
      (available _ List.mem_cons_self) firstSafe valid known capturedDomain stored valueDomain
    cases domain with
    | cons _ rest =>
      exact restIH result middle actual populated allowed next receipt.ready
        (fun value member => receipt.effects.keeps.available value (available value (List.mem_cons_of_mem _ member)))
        (children_tail safe) returned.1 rest current receipt.globals.valid
  have nilRows : ∀ {entries before}, RL entries ([] : List (EdgeValue Symbol Guard)) before := by
    intro entries before _ _ _ _ _ _ _ _ _ _
    exact .nil
  have consCase : ∀ {entries edges before} {edge : EdgeValue Symbol Guard},
      ChildrenCapacity bits record originals entries 0 edge.children before →
      (∀ values middle, EditChildren record originals entries 0 edge.children before values middle →
        RowsCapacity bits record originals entries edges (advanceHeap middle
          (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.checked.native.machine.heap).2)) →
      CL entries 0 edge.children before →
      (∀ values middle, EditChildren record originals entries 0 edge.children before values middle →
        RL entries edges (advanceHeap middle
          (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.checked.native.machine.heap).2)) →
      RL entries (edge :: edges) before := by
    intro entries edges before edge _ _ firstIH restIH populated allowed inventory ready resident safe stored domain memos valid
    have original := resident edge List.mem_cons_self
    have available := ready.checked.semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge original
    have childDomain := domain.member edge List.mem_cons_self
    have firstRanges := firstIH populated allowed inventory ready available (safe _ List.mem_cons_self) stored childDomain memos valid
    refine .cons firstRanges ?_
    intro values middle actual
    have domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) originals := fun path _ =>
      SourceCurrentAllocatedFiniteOrdinaryTarget.forest_closed _ ready.checked.semantic originals
        (fun value member => ready.captured.available value (known value member)) capturedDomain _
    obtain ⟨values', middle', next, current, constructed, reads, receipt⟩ :=
      SourceCurrentAllocatedSharedEditComplete.children_complete formulas solver record originals base known domains coherent active
        inventory firstRanges populated allowed ready available (safe _ List.mem_cons_self) memos valid
    obtain ⟨rfl, rfl⟩ := children_unique actual constructed
    have returned := SourceCurrentAllocatedFiniteOrdinaryEdits.children reads populated allowed ready available
      (safe _ List.mem_cons_self) valid known capturedDomain stored childDomain
    have field := (ready.checked.good.fields edge.entry.key edge original).grows receipt.effects.grows
    have built := edge_physical receipt.ready edge.entry.key.symbol edge.entry.key.constraint values field receipt.available
    have globalValid := SourceQueryUnfoldMemo.valid_grows middle.checked.native.machine.heap _ receipt.ready.checked.semantic
      built.2.1.keeps current receipt.globals.valid
    have kept := receipt.effects.keeps.trans built.2.1.keeps
    cases domain with
    | cons _ rest =>
      exact restIH values middle actual populated allowed next built.1
        (fun original member => InternedEdgeResidency.edge_grows _ _ kept.growth original (resident original (List.mem_cons_of_mem _ member)))
        (fun original member => safe original (List.mem_cons_of_mem _ member))
        (SourceCurrentAllocatedFiniteOrdinaryShared.advance_heap_stored _ _ returned.1) rest current globalValid
  refine ⟨?_, ?_, ?_⟩
  · intro edits value before capacity
    exact NodeCapacity.rec (motive_1 := fun edits value before _ => NL edits value before)
      (motive_2 := fun entries index values before _ => CL entries index values before)
      (motive_3 := fun entries edges before _ => RL entries edges before)
      leafCase emptyCase ordinaryCase nilChildren unselectedCase selectedCase nilRows consCase capacity
  · intro entries index values before capacity
    exact ChildrenCapacity.rec (motive_1 := fun edits value before _ => NL edits value before)
      (motive_2 := fun entries index values before _ => CL entries index values before)
      (motive_3 := fun entries edges before _ => RL entries edges before)
      leafCase emptyCase ordinaryCase nilChildren unselectedCase selectedCase nilRows consCase capacity
  · intro entries edges before capacity
    exact RowsCapacity.rec (motive_1 := fun edits value before _ => NL edits value before)
      (motive_2 := fun entries index values before _ => CL entries index values before)
      (motive_3 := fun entries edges before _ => RL entries edges before)
      leafCase emptyCase ordinaryCase nilChildren unselectedCase selectedCase nilRows consCase capacity

/-- Initial state facts and numeric entries derive all reached node checks. -/
theorem node_ranges {edits value before} (capacity : NodeCapacity bits record originals edits value before)
    (populated : Populated edits) (nonempty : HasLeaf edits) (allowed : Allowed record edits) (inventory : Inventory)
    (ready : Ready formulas solver inventory record originals base before)
    (available : Available before.checked.native.machine.heap value) (safe : Safe edits value)
    (stored : Stored before) (domain : DNode value) (memos : Memos) (valid : GlobalValid before.checked.native.machine.heap memos) :
    NodeRanges record originals edits value before :=
  (derive bits formulas solver record originals base known capturedDomain coherent active).1 _ _ _ capacity
    populated nonempty allowed inventory ready available safe stored domain memos valid

/-- Only earlier selected child returns determine the later child checks. -/
theorem children_ranges {entries index values before} (capacity : ChildrenCapacity bits record originals entries index values before)
    (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries)) (inventory : Inventory)
    (ready : Ready formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap values) (safe : ChildrenSafe entries index values)
    (stored : Stored before) (domain : DChildren values) (memos : Memos) (valid : GlobalValid before.checked.native.machine.heap memos) :
    ChildrenRanges record originals entries index values before :=
  (derive bits formulas solver record originals base known capturedDomain coherent active).2.1 _ _ _ _ capacity
    populated allowed inventory ready available safe stored domain memos valid

/-- Literal child and edge prefixes derive each later row's checks. -/
theorem rows_ranges {entries edges before} (capacity : RowsCapacity bits record originals entries edges before)
    (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries)) (inventory : Inventory)
    (ready : Ready formulas solver inventory record originals base before)
    (available : Edges before.checked.native.machine.heap edges) (safe : RowsSafe entries edges)
    (stored : Stored before) (domain : DRows edges) (memos : Memos) (valid : GlobalValid before.checked.native.machine.heap memos) :
    RowsRanges record originals entries edges before :=
  (derive bits formulas solver record originals base known capturedDomain coherent active).2.2 _ _ _ capacity
    populated allowed inventory ready available safe stored domain memos valid

/-- The list root derives its existing range plan from numeric capacity and initial facts. -/
theorem list_ranges {edits values before} (capacity : ListCapacity bits record originals edits values before)
    (populated : Populated edits) (allowed : Allowed record edits) (inventory : Inventory)
    (ready : Ready formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap values) (safe : ListSafe edits values)
    (stored : Stored before) (domain : DChildren values) (memos : Memos) (valid : GlobalValid before.checked.native.machine.heap memos) :
    ListRanges record originals edits values before := by
  cases edits with
  | editAt _ => trivial
  | editBelow entries =>
    exact children_ranges bits formulas solver record originals base known capturedDomain coherent active
      capacity populated allowed inventory ready available safe stored domain memos valid

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEditCapacity
