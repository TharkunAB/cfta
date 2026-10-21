import MicroCFTA.SourceCurrentAllocatedSharedEditGraph
import MicroCFTA.SourceCurrentEditDomains
import MicroCFTA.SourceEqualitySharedEditEffects
import MicroCFTA.SourceCurrentRequiredHeapEffects

/-!
# Physical effects of checked simultaneous class edits

Actual read receipts retain the returned checked states and global tables.
Each leaf can change the current input inventory. Rebuilt rows retain their
original raw fields. Their positional child edits preserve the source arity.
The result does not assert a GHC demand schedule.
-/
namespace MicroCFTA.SourceCurrentAllocatedSharedEditEffects
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityEdits SourceEqualityEditLeafPaths SourceEqualityProjectionPathDomain
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentEditDomains
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedSharedTargetForce (Retains)
open SourceCurrentAllocatedSharedEditGraph
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "HeapState" => InternedConstructorTemplates.State Symbol Guard
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
local notation "GlobalEffect" => SourceCurrentSubsumesQueryMemos.Effect
local notation "FieldAvailable" => SourceCurrentConjunctionEquality.FieldAvailable
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- List-root leaves are ignored; below-edits check their selected child domains. -/
def ListSafe (edits : Edits Action) (values : List (Value Symbol Guard)) : Prop :=
  match edits with
  | .editAt _ => True
  | .editBelow entries => ChildrenSafe entries 0 values

/-- The exact returned state retains every live physical and memo component. -/
structure Receipt (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) (base : HeapState)
    (before after : SharedState width) (memos final : Memos) : Prop where
  ready : Ready formulas solver inventory record originals base after
  effects : Effects (physical before.checked) (physical after.checked)
  extension : SourceRecursiveIntersectionKernel.Extension before.checked.native.machine after.checked.native.machine
  slots : Retains before after
  retained : Extends before.memo after.memo
  globals : GlobalEffect before.checked.native.machine.heap after.checked.native.machine.heap memos final

/-- One node edit also retains its selected path domains. -/
structure NodeReceipt (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) (base : HeapState)
    (input : Value Symbol Guard) (before : SharedState width) (result : Value Symbol Guard)
    (after : SharedState width) (memos final : Memos) : Prop
    extends Receipt formulas solver inventory record originals base before after memos final where
  available : Available after.checked.native.machine.heap result
  transport : Transport input result

/-- Child edits preserve every original position and its path domains. -/
structure ChildrenReceipt (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) (base : HeapState)
    (inputs : List (Value Symbol Guard)) (before : SharedState width) (results : List (Value Symbol Guard))
    (after : SharedState width) (memos final : Memos) : Prop
    extends Receipt formulas solver inventory record originals base before after memos final where
  available : Values after.checked.native.machine.heap results
  transport : All₂ Transport inputs results

/-- Row edits retain resident raw edges and aligned child domains. -/
structure RowsReceipt (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) (base : HeapState)
    (inputs : List (EdgeValue Symbol Guard)) (before : SharedState width) (results : List (EdgeValue Symbol Guard))
    (after : SharedState width) (memos final : Memos) : Prop
    extends Receipt formulas solver inventory record originals base before after memos final where
  available : Edges after.checked.native.machine.heap results
  transport : All₂ (fun edge result => All₂ Transport edge.children result.children) inputs results

variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {inventory next : Inventory} {record : SourceEqualityClassOrder.Record}
variable {originals : List (Value Symbol Guard)} {base : HeapState}

/-- Ordinary node construction retains open rows and the same operation state. -/
theorem node_physical {before : SharedState width}
    (ready : Ready formulas solver inventory record originals base before)
    (edges : List (EdgeValue Symbol Guard)) (resident : Edges before.checked.native.machine.heap edges) :
    Ready formulas solver inventory record originals base
        (advanceHeap before (run (makeNode edges) before.checked.native.machine.heap).2) ∧
      Effects (physical before.checked)
        (physical (advanceHeap before (run (makeNode edges) before.checked.native.machine.heap).2).checked) ∧
      Available (run (makeNode edges) before.checked.native.machine.heap).2
        (run (makeNode edges) before.checked.native.machine.heap).1 := by
  have actual := SourceCurrentRequiredHeapEffects.node_constructor
    (FieldAvailable before.checked.operations) edges before.checked.native.machine.heap
    ready.checked.semantic ready.checked.costs ready.checked.good.fields resident
  have effects : Effects (physical before.checked)
      ⟨(run (makeNode edges) before.checked.native.machine.heap).2, before.checked.operations⟩ :=
    ⟨actual.1, ⟨actual.2.1, actual.2.2.1, ready.checked.good.operations, actual.2.2.2.1⟩,
      SourceEqualityConstraintMemoAllocation.grows_refl _⟩
  exact ⟨ready.physical _ effects, effects, actual.2.2.2.2⟩

/-- Raw row construction preserves its stored guard and exact ordered children. -/
theorem edge_physical {before : SharedState width}
    (ready : Ready formulas solver inventory record originals base before)
    (symbol : Symbol) (guard : Guard) (children : List (Value Symbol Guard))
    (field : FieldAvailable before.checked.operations guard)
    (available : Values before.checked.native.machine.heap children) :
    Ready formulas solver inventory record originals base
        (advanceHeap before (run (makeEdge symbol guard children) before.checked.native.machine.heap).2) ∧
      Effects (physical before.checked)
        (physical (advanceHeap before (run (makeEdge symbol guard children) before.checked.native.machine.heap).2).checked) ∧
      InternedEdgeResidency.EdgeResident (run (makeEdge symbol guard children) before.checked.native.machine.heap).2
        (run (makeEdge symbol guard children) before.checked.native.machine.heap).1 ∧
      (run (makeEdge symbol guard children) before.checked.native.machine.heap).1.children = children := by
  have actual := SourceEqualityRequiredCache.edge symbol guard children before.checked.native.machine.heap
    ready.checked.semantic.ready available
  have semantic := SourceEqualityRequiredSemanticCache.edge symbol guard children before.checked.native.machine.heap
    ready.checked.semantic available
  have fields := SourceEqualityAnnotationHeap.run (FieldAvailable before.checked.operations) _
    (SourceEqualityAnnotationHeap.makeEdge (FieldAvailable before.checked.operations) symbol guard children field)
    before.checked.native.machine.heap ready.checked.good.fields
  have effects : Effects (physical before.checked)
      ⟨(run (makeEdge symbol guard children) before.checked.native.machine.heap).2, before.checked.operations⟩ :=
    ⟨actual.1, ⟨semantic, ready.checked.costs, ready.checked.good.operations, fields⟩,
      SourceEqualityConstraintMemoAllocation.grows_refl _⟩
  exact ⟨ready.physical _ effects, effects, actual.2⟩

/-- Actual head exposure retains open physical fields and the same operation state. -/
theorem head_physical {before : SharedState width} {input exposed : Value Symbol Guard} {heap : HeapState}
    (ready : Ready formulas solver inventory record originals base before)
    (head : SourceEqualityRequiredHead.Head input before.checked.native.machine.heap exposed heap)
    (available : Available before.checked.native.machine.heap input) :
    Ready formulas solver inventory record originals base (advanceHeap before heap) ∧
      Effects (physical before.checked) (physical (advanceHeap before heap).checked) ∧ Available heap exposed := by
  have actual := SourceCurrentRequiredHeapEffects.head (FieldAvailable before.checked.operations) head
    ready.checked.semantic ready.checked.costs ready.checked.good.fields available
  have effects : Effects (physical before.checked) ⟨heap, before.checked.operations⟩ :=
    ⟨actual.1, ⟨actual.2.1, actual.2.2.1, ready.checked.good.operations, actual.2.2.2.1⟩,
      SourceEqualityConstraintMemoAllocation.grows_refl _⟩
  exact ⟨ready.physical _ effects, effects, actual.2.2.2.2⟩

private theorem receipt_refl {before : SharedState width} {memos : Memos}
    (ready : Ready formulas solver inventory record originals base before)
    (valid : Valid before.checked.native.machine.heap memos) :
    Receipt formulas solver inventory record originals base before before memos memos := by
  have physicalReady := SourceCurrentAllocatedConjunctionMemo.ready before.checked
    ready.checked.good ready.checked.semantic ready.checked.costs
  exact ⟨ready, SourceCurrentConjunctionRowsAllocation.Effects.refl _ physicalReady, .refl _,
    .refl _, extends_refl _,
    ⟨pure_keeps _ ready.checked.semantic.ready, ready.checked.semantic, ready.checked.costs,
      valid, extends_refl _, rfl⟩⟩

private theorem receipt_trans {before middle after : SharedState width} {memos current final : Memos}
    (first : Receipt formulas solver inventory record originals base before middle memos current)
    (rest : Receipt formulas solver next record originals base middle after current final) :
    Receipt formulas solver next record originals base before after memos final :=
  ⟨rest.ready, first.effects.trans rest.effects, first.extension.trans rest.extension,
    first.slots.trans rest.slots, extends_trans first.retained rest.retained,
    SourceCurrentMemoMergeQueryMemos.effect_trans first.globals rest.globals⟩

private theorem receipt_heap {before : SharedState width} {heap : HeapState} {memos final : Memos}
    (ready : Ready formulas solver inventory record originals base before)
    (effects : Effects (physical before.checked) (physical (advanceHeap before heap).checked))
    (globals : GlobalEffect before.checked.native.machine.heap heap memos final) :
    Receipt formulas solver inventory record originals base before (advanceHeap before heap) memos final :=
  ⟨ready.physical _ effects, effects,
    SourceCurrentAllocatedQueryMemo.advance_extension before.checked _ effects,
    SourceCurrentAllocatedSharedTargetForce.advance_retains _ _, extends_refl _, globals⟩

private theorem heap_global {before : SharedState width} {heap : HeapState} {memos : Memos}
    (ready : Ready formulas solver inventory record originals base before)
    (effects : Effects (physical before.checked) (physical (advanceHeap before heap).checked))
    (valid : Valid before.checked.native.machine.heap memos) :
    GlobalEffect before.checked.native.machine.heap heap memos memos :=
  ⟨effects.keeps, effects.ready.semantic, effects.ready.costs,
    SourceQueryUnfoldMemo.valid_grows _ _ ready.checked.semantic effects.keeps memos valid,
    extends_refl _, rfl⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem aligned_rows_closed {edges results : List (EdgeValue Symbol Guard)}
    (aligned : All₂ (fun edge result => All₂ Transport edge.children result.children) edges results)
    (closed : ClosedEdges edges) : ClosedEdges results := by
  induction aligned with
  | nil => intro edge member; cases member
  | cons first rest ih =>
      intro edge member
      rcases List.mem_cons.mp member with rfl | member
      · exact transport_forest first [] (closed _ List.mem_cons_self)
      · exact ih (fun original included => closed original (List.mem_cons_of_mem _ included)) edge member

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem aligned_rows_path {edges results : List (EdgeValue Symbol Guard)}
    (aligned : All₂ (fun edge result => All₂ Transport edge.children result.children) edges results)
    (index : Int) (path : List Int) (domain : RowsClosed path index edges) : RowsClosed path index results := by
  induction aligned with
  | nil => intro edge member; cases member
  | cons first rest ih =>
      intro edge member
      rcases List.mem_cons.mp member with rfl | member
      · exact transport_forest first (index :: path) (domain _ List.mem_cons_self)
      · exact ih (fun original included => domain original (List.mem_cons_of_mem _ included)) edge member

omit [DecidableEq Symbol] in
private theorem makeNode_path
    (index : Int) (path : List Int) (edges : List (EdgeValue Symbol Guard)) (state : HeapState)
    (facts : InternedNestedFacts.Facts state) (resident : Edges state edges) (domain : RowsClosed path index edges) :
    NodeClosed (index :: path) (run (makeNode edges) state).1 := by
  have ordinary := SourceEqualityRequiredCache.node_ordinary edges state facts resident
  generalize same : (run (makeNode edges) state).1 = value at ordinary ⊢
  cases value with
  | empty => simp only [NodeClosed]
  | reference | union | mu => cases ordinary
  | node entry rows depth free =>
      rw [NodeClosed]
      intro edge member child selected
      have origin : edge ∈ edges := by
        have present : edge ∈ InternedEdgeResidency.nodeEdges (run (makeNode edges) state).1 := by
          rw [same]
          exact member
        rw [EqualityLeafProjectionPhysical.makeNode_edges edges state facts.coherent facts.linked resident] at present
        exact (List.mem_filter.mp (canonicalEdges_member _ edge present)).1
      exact domain edge origin child selected

private def NodeLaw (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
    (edits : Edits EqualityNormalize.Path) (input : Value Symbol Guard) (before : SharedState width)
    (result : Value Symbol Guard) (after : SharedState width) (memos final : Memos) : Prop :=
  ∀ inventory, Populated edits → HasLeaf edits → Allowed record edits →
    Ready formulas solver inventory record originals base before → Available before.checked.native.machine.heap input →
    Safe edits input → Valid before.checked.native.machine.heap memos →
    ∃ next, NodeReceipt formulas solver next record originals base input before result after memos final

private def ChildrenLaw (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
    (entries : List (Int × Edits EqualityNormalize.Path)) (offset : Nat) (inputs : List (Value Symbol Guard))
    (before : SharedState width) (results : List (Value Symbol Guard)) (after : SharedState width) (memos final : Memos) : Prop :=
  ∀ inventory, Populated (.editBelow entries) → Allowed record (.editBelow entries) →
    Ready formulas solver inventory record originals base before → Values before.checked.native.machine.heap inputs →
    ChildrenSafe entries offset inputs → Valid before.checked.native.machine.heap memos →
    ∃ next, ChildrenReceipt formulas solver next record originals base inputs before results after memos final

private def RowsLaw (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
    (entries : List (Int × Edits EqualityNormalize.Path)) (inputs : List (EdgeValue Symbol Guard))
    (before : SharedState width) (results : List (EdgeValue Symbol Guard)) (after : SharedState width) (memos final : Memos) : Prop :=
  ∀ inventory, Populated (.editBelow entries) → Allowed record (.editBelow entries) →
    Ready formulas solver inventory record originals base before → Edges before.checked.native.machine.heap inputs →
    RowsSafe entries inputs → Valid before.checked.native.machine.heap memos →
    ∃ next, RowsReceipt formulas solver next record originals base inputs before results after memos final

set_option maxHeartbeats 1600000 in
private theorem effects :
    (∀ {record originals edits value before result after} {memos final : Memos}
      {actual : EditNode (width := width) record originals edits value before result after},
      NodeReads formulas solver base actual memos final →
        NodeLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals edits value before result after memos final) ∧
    (∀ {record originals entries offset values before results after} {memos final : Memos}
      {actual : EditChildren (width := width) record originals entries offset values before results after},
      ChildrenReads formulas solver base actual memos final →
        ChildrenLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries offset values before results after memos final) ∧
    (∀ {record originals entries edges before results after} {memos final : Memos}
      {actual : EditRows (width := width) record originals entries edges before results after},
      RowsReads formulas solver base actual memos final →
        RowsLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries edges before results after memos final) := by
  have leafCase : ∀ {next record originals path value before result after memos saved},
      SourceCurrentAllocatedSharedTargetLeaf.Receipt formulas solver next record originals base path value before result after memos saved →
      NodeLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals (.editAt path) value before result after memos saved := by
    intro next record originals path value before result after memos saved receipt _ _ _ _ _ _ _ _
    refine ⟨next, ⟨⟨receipt.ready, receipt.effects, receipt.extension, receipt.slots, receipt.retained, receipt.globals⟩,
      receipt.available, ?_⟩⟩
    intro query _
    exact SourceCurrentRequiredEndpoints.closed_path query result after.checked.native.machine.heap
      receipt.ready.checked.semantic receipt.available receipt.closed
  have emptyCase : ∀ {record originals entries state memos},
      NodeLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals
        (.editBelow entries) (.empty : Value Symbol Guard) state .empty state memos memos := by
    intro record originals entries state memos inventory _ _ _ ready available _ valid
    exact ⟨inventory, ⟨receipt_refl ready valid, available, fun _ domain => domain⟩⟩
  have ordinaryCase : ∀ {record originals memos saved entries edges before rebuilt middle value heap entry depth free}
      {actual : EditRows record originals entries edges before rebuilt middle}
      {built : run (makeNode rebuilt) middle.checked.native.machine.heap = (value, heap)},
      RowsReads formulas solver base actual memos saved →
      RowsLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries edges before rebuilt middle memos saved →
      NodeLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals
        (.editBelow entries) (.node entry edges depth free) before value (advanceHeap middle heap) memos saved := by
    intro record originals memos saved entries edges before rebuilt middle value heap entry depth free actual built _ ih
      inventory populated _ allowed ready available safe valid
    have facts := ready.checked.semantic.ready.semantic.1.normal.facts
    obtain ⟨next, rows⟩ := ih inventory populated allowed ready
      (InternedEdgeResidency.resident_edges _ facts.linked _ available.resident) (ordinary_rows safe) valid
    have finish := node_physical rows.ready rebuilt rows.available
    have finished : Ready formulas solver next record originals base (advanceHeap middle heap) ∧
        Effects (physical middle.checked) (physical (advanceHeap middle heap).checked) ∧ Available heap value :=
      by simpa only [built] using finish
    have pure := receipt_heap rows.ready finished.2.1 (heap_global rows.ready finished.2.1 rows.globals.valid)
    refine ⟨next, ⟨receipt_trans rows.toReceipt pure, finished.2.2, ?_⟩⟩
    intro query domain
    cases query with
    | nil =>
        have inputClosed : (.node entry edges depth free : Value Symbol Guard).free = [] := by simpa only [NodeClosed] using domain
        have originalClosed := MergedColdReaderClosed.node_children_closed _ facts entry edges depth free available inputClosed
        have closed := SourceEqualityRequiredCache.node rebuilt middle.checked.native.machine.heap
          rows.ready.checked.semantic.ready rows.available (aligned_rows_closed rows.transport originalClosed)
        simpa only [NodeClosed, built] using closed.2.2.1
    | cons index path =>
        have inputDomain : RowsClosed path index edges := by simpa only [NodeClosed, RowsClosed] using domain
        have resultDomain := makeNode_path index path rebuilt middle.checked.native.machine.heap
          rows.ready.checked.semantic.ready.semantic.1.normal.facts rows.available
          (aligned_rows_path rows.transport index path inputDomain)
        simpa only [built] using resultDomain
  have recursiveCase : ∀ {record originals memos current saved entries original before exposed heap value after}
      {recursive : SourceEqualityRequiredGraph.Recursive original}
      {head : SourceEqualityRequiredHead.Head original before.checked.native.machine.heap exposed heap}
      {body : EditNode record originals (.editBelow entries) exposed (advanceHeap before heap) value after},
      SourceCurrentRequiredQueryMemos.HeadReads head memos current →
      GlobalEffect before.checked.native.machine.heap heap memos current →
      NodeReads formulas solver base body current saved →
      NodeLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals
        (.editBelow entries) exposed (advanceHeap before heap) value after current saved →
      NodeLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals
        (.editBelow entries) original before value after memos saved := by
    intro record originals memos current saved entries original before exposed heap value after recursive head body
      _ headGlobal _ ih inventory populated nonempty allowed ready available safe _
    have closed := recursive_closed recursive nonempty safe
    have first := head_physical ready head available
    have checked := head.verified ready.checked.semantic.ready available closed
    obtain ⟨next, later⟩ := ih inventory populated nonempty allowed first.1 first.2.2
      (closed_safe _ exposed heap first.1.checked.semantic first.2.2 checked.2.2.1) headGlobal.valid
    refine ⟨next, ⟨receipt_trans (receipt_heap ready first.2.1 headGlobal) later.toReceipt, later.available, ?_⟩⟩
    intro query _
    exact later.transport query (SourceCurrentRequiredEndpoints.closed_path query exposed heap
      first.1.checked.semantic first.2.2 checked.2.2.1)
  have nilChildren : ∀ {record originals entries offset state memos},
      ChildrenLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries offset
        ([] : List (Value Symbol Guard)) state [] state memos memos := by
    intro record originals entries offset state memos inventory _ _ ready _ _ valid
    exact ⟨inventory, ⟨receipt_refl ready valid, by simp [Values], .nil⟩⟩
  have unselectedCase : ∀ {record originals memos saved entries values before results after value} {offset : Nat}
      {absent : SourceEqualityNeededMap.lookup (offset : Int) entries = none}
      {rest : EditChildren record originals entries (offset + 1) values before results after},
      ChildrenReads formulas solver base rest memos saved →
      ChildrenLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries (offset + 1) values before results after memos saved →
      ChildrenLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries offset (value :: values) before (value :: results) after memos saved := by
    intro record originals memos saved entries values before results after value offset absent rest _ ih
      inventory populated allowed ready available safe valid
    obtain ⟨next, later⟩ := ih inventory populated allowed ready
      (fun original member => available original (List.mem_cons_of_mem _ member)) (children_tail safe) valid
    refine ⟨next, ⟨later.toReceipt, ?_, .cons (fun _ domain => domain) later.transport⟩⟩
    intro original member
    rcases List.mem_cons.mp member with rfl | member
    · exact later.effects.keeps.available _ (available _ List.mem_cons_self)
    · exact later.available original member
  have selectedCase : ∀ {record originals memos current saved entries edits value before result middle values results after} {offset : Nat}
      {found : SourceEqualityNeededMap.lookup (offset : Int) entries = some edits}
      {first : EditNode record originals edits value before result middle}
      {rest : EditChildren record originals entries (offset + 1) values middle results after},
      NodeReads formulas solver base first memos current → ChildrenReads formulas solver base rest current saved →
      NodeLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals edits value before result middle memos current →
      ChildrenLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries (offset + 1) values middle results after current saved →
      ChildrenLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries offset (value :: values) before (result :: results) after memos saved := by
    intro record originals memos current saved entries edits value before result middle values results after offset found first rest
      _ _ firstIH restIH inventory populated allowed ready available safe valid
    have member := SourceEqualityNeededMap.lookup_mem _ _ _ found
    have children := (show ∀ index child, (index, child) ∈ entries → Populated child ∧ HasLeaf child from
      by simpa only [Populated] using populated)
    have childAllowed : Allowed record edits := by
      rw [Allowed, All] at allowed
      exact allowed _ _ member
    obtain ⟨middleInventory, firstReceipt⟩ := firstIH inventory (children _ _ member).1 (children _ _ member).2 childAllowed
      ready (available _ List.mem_cons_self) (safe 0 _ (by simpa using found) value rfl) valid
    obtain ⟨next, later⟩ := restIH middleInventory populated allowed firstReceipt.ready
      (fun original member => firstReceipt.effects.keeps.available original (available original (List.mem_cons_of_mem _ member)))
      (children_tail safe) firstReceipt.globals.valid
    refine ⟨next, ⟨receipt_trans firstReceipt.toReceipt later.toReceipt, ?_, .cons firstReceipt.transport later.transport⟩⟩
    intro original member
    rcases List.mem_cons.mp member with rfl | member
    · exact later.effects.keeps.available _ firstReceipt.available
    · exact later.available original member
  have nilRows : ∀ {record originals entries state memos},
      RowsLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries
        ([] : List (EdgeValue Symbol Guard)) state [] state memos memos := by
    intro record originals entries state memos inventory _ _ ready _ _ valid
    exact ⟨inventory, ⟨receipt_refl ready valid, by simp [Edges], .nil⟩⟩
  have consCase : ∀ {record originals memos current saved entries before values middle result heap edges results after edge}
      {children : EditChildren record originals entries 0 edge.children before values middle}
      {rebuilt : run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.checked.native.machine.heap = (result, heap)}
      {rest : EditRows record originals entries edges (advanceHeap middle heap) results after},
      ChildrenReads formulas solver base children memos current → RowsReads formulas solver base rest current saved →
      ChildrenLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries 0 edge.children before values middle memos current →
      RowsLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries edges (advanceHeap middle heap) results after current saved →
      RowsLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries (edge :: edges) before (result :: results) after memos saved := by
    intro record originals memos current saved entries before values middle result heap edges results after edge children rebuilt rest
      _ _ firstIH restIH inventory populated allowed ready resident safe valid
    have facts := ready.checked.semantic.ready.semantic.1.normal.facts
    obtain ⟨middleInventory, first⟩ := firstIH inventory populated allowed ready
      (facts.cached.edges edge.entry.key edge (resident _ List.mem_cons_self)) (safe _ List.mem_cons_self) valid
    have field := (ready.checked.good.fields _ _ (resident _ List.mem_cons_self)).grows first.effects.grows
    have rebuiltPhysical := edge_physical first.ready edge.entry.key.symbol edge.entry.key.constraint values field first.available
    have edgeResult : Ready formulas solver middleInventory record originals base (advanceHeap middle heap) ∧
        Effects (physical middle.checked) (physical (advanceHeap middle heap).checked) ∧
        InternedEdgeResidency.EdgeResident heap result ∧ result.children = values := by
      simpa only [rebuilt] using rebuiltPhysical
    have pure := receipt_heap first.ready edgeResult.2.1 (heap_global first.ready edgeResult.2.1 first.globals.valid)
    have preceding := receipt_trans first.toReceipt pure
    obtain ⟨next, later⟩ := restIH middleInventory populated allowed edgeResult.1
      (fun original member => InternedEdgeResidency.edge_grows _ _ preceding.effects.keeps.growth original
        (resident original (List.mem_cons_of_mem _ member)))
      (fun original member => safe original (List.mem_cons_of_mem _ member)) preceding.globals.valid
    refine ⟨next, ⟨receipt_trans preceding later.toReceipt, ?_, .cons ?_ later.transport⟩⟩
    · intro original member
      rcases List.mem_cons.mp member with rfl | member
      · exact InternedEdgeResidency.edge_grows _ _ later.effects.keeps.growth _ edgeResult.2.2.1
      · exact later.available original member
    · simpa only [edgeResult.2.2.2] using first.transport
  refine ⟨?_, ?_, ?_⟩
  · intro record originals edits value before result after memos final actual reads
    exact NodeReads.rec
      (motive_1 := fun {record originals edits value before result after} _ memos final _ =>
        NodeLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals edits value before result after memos final)
      (motive_2 := fun {record originals entries offset values before results after} _ memos final _ =>
        ChildrenLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries offset values before results after memos final)
      (motive_3 := fun {record originals entries edges before results after} _ memos final _ =>
        RowsLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries edges before results after memos final)
      @leafCase @emptyCase @ordinaryCase @recursiveCase @nilChildren @unselectedCase @selectedCase @nilRows @consCase reads
  · intro record originals entries offset values before results after memos final actual reads
    exact ChildrenReads.rec
      (motive_1 := fun {record originals edits value before result after} _ memos final _ =>
        NodeLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals edits value before result after memos final)
      (motive_2 := fun {record originals entries offset values before results after} _ memos final _ =>
        ChildrenLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries offset values before results after memos final)
      (motive_3 := fun {record originals entries edges before results after} _ memos final _ =>
        RowsLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries edges before results after memos final)
      @leafCase @emptyCase @ordinaryCase @recursiveCase @nilChildren @unselectedCase @selectedCase @nilRows @consCase reads
  · intro record originals entries edges before results after memos final actual reads
    exact RowsReads.rec
      (motive_1 := fun {record originals edits value before result after} _ memos final _ =>
        NodeLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals edits value before result after memos final)
      (motive_2 := fun {record originals entries offset values before results after} _ memos final _ =>
        ChildrenLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries offset values before results after memos final)
      (motive_3 := fun {record originals entries edges before results after} _ memos final _ =>
        RowsLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries edges before results after memos final)
      @leafCase @emptyCase @ordinaryCase @recursiveCase @nilChildren @unselectedCase @selectedCase @nilRows @consCase reads

/-- Actual node reads derive physical effects and selected path transport. -/
theorem node_effects {edits value before result after memos final}
    {actual : EditNode (width := width) record originals edits value before result after}
    (reads : NodeReads formulas solver base actual memos final)
    (populated : Populated edits) (nonempty : HasLeaf edits) (allowed : Allowed record edits)
    (ready : Ready formulas solver inventory record originals base before)
    (available : Available before.checked.native.machine.heap value) (safe : Safe edits value)
    (valid : Valid before.checked.native.machine.heap memos) :
    ∃ next, NodeReceipt formulas solver next record originals base value before result after memos final :=
  effects.1 reads inventory populated nonempty allowed ready available safe valid

/-- Actual child reads retain every original position and the returned inventory. -/
theorem children_effects {entries offset values before results after memos final}
    {actual : EditChildren (width := width) record originals entries offset values before results after}
    (reads : ChildrenReads formulas solver base actual memos final)
    (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : Ready formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap values) (safe : ChildrenSafe entries offset values)
    (valid : Valid before.checked.native.machine.heap memos) :
    ∃ next, ChildrenReceipt formulas solver next record originals base values before results after memos final :=
  effects.2.1 reads inventory populated allowed ready available safe valid

/-- Actual row reads retain resident edges and every selected child domain. -/
theorem rows_effects {entries edges before results after memos final}
    {actual : EditRows (width := width) record originals entries edges before results after}
    (reads : RowsReads formulas solver base actual memos final)
    (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : Ready formulas solver inventory record originals base before)
    (available : Edges before.checked.native.machine.heap edges) (safe : RowsSafe entries edges)
    (valid : Valid before.checked.native.machine.heap memos) :
    ∃ next, RowsReceipt formulas solver next record originals base edges before results after memos final :=
  effects.2.2 reads inventory populated allowed ready available safe valid

/-- A child-list root leaf makes no call; below-edits retain actual child effects. -/
theorem list_effects {edits values before results after memos final}
    {actual : EditList (width := width) record originals edits values before results after}
    (reads : ListReads formulas solver base actual memos final)
    (populated : Populated edits) (allowed : Allowed record edits)
    (ready : Ready formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap values)
    (safe : ListSafe edits values)
    (valid : Valid before.checked.native.machine.heap memos) :
    ∃ next, ChildrenReceipt formulas solver next record originals base values before results after memos final := by
  cases reads with
  | leaf =>
      refine ⟨inventory, ⟨receipt_refl ready valid, available, ?_⟩⟩
      clear available safe
      induction values with
      | nil => exact .nil
      | cons value values ih => exact .cons (fun _ domain => domain) ih
  | children read => exact children_effects read populated allowed ready available safe valid

end MicroCFTA.SourceCurrentAllocatedSharedEditEffects
