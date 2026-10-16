import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryReceiptStructure
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNarrow
import MicroCFTA.SourceCurrentAllocatedSharedEditEffects

/-!
# Structural narrowing through current simultaneous edits

Actual annotated reads determine each returned state and inventory.
The proof retains native, merge, and target-slot structural certificates.
Selected children retain positional domain and height bounds. Raw row and
node reconstruction use their actual resident records and full guards.
No range plan or future result law is an input to these read endpoints.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEdits
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityEdits SourceEqualityEditLeafPaths
open SourceEqualitySharedEditEffects (Allowed)
open SourceEqualityRequiredCache (Keeps)
open SourceCurrentEditDomains
open SourceCurrentAllocatedSharedEditGraph
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow EdgeNarrow)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "HeapState" => InternedConstructorTemplates.State Symbol Guard
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "GlobalEffect" => SourceCurrentSubsumesQueryMemos.Effect
local notation "SharedStored" => SourceCurrentAllocatedFiniteOrdinaryShared.Stored
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
local notation "DRows" => SourceCurrentAllocatedFiniteOrdinaryDomain.Rows
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula} {base : HeapState}

private def NodeLaw (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
    (edits : Edits EqualityNormalize.Path) (input : Value Symbol Guard) (before : SharedState width)
    (result : Value Symbol Guard) (after : SharedState width) (memos _final : Memos) : Prop :=
  ∀ inventory, Populated edits → HasLeaf edits → Allowed record edits →
    Ready formulas solver inventory record originals base before → Available before.checked.native.machine.heap input →
    Safe edits input → Valid before.checked.native.machine.heap memos →
    Values base originals → DChildren originals → SharedStored before → DNode input →
      SharedStored after ∧ NodeNarrow input result

private def ChildrenLaw (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
    (entries : List (Int × Edits EqualityNormalize.Path)) (offset : Nat) (inputs : List (Value Symbol Guard))
    (before : SharedState width) (results : List (Value Symbol Guard)) (after : SharedState width) (memos _final : Memos) : Prop :=
  ∀ inventory, Populated (.editBelow entries) → Allowed record (.editBelow entries) →
    Ready formulas solver inventory record originals base before → Values before.checked.native.machine.heap inputs →
    ChildrenSafe entries offset inputs → Valid before.checked.native.machine.heap memos →
    Values base originals → DChildren originals → SharedStored before → DChildren inputs →
      SharedStored after ∧ All₂ NodeNarrow inputs results

private def RowsLaw (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
    (entries : List (Int × Edits EqualityNormalize.Path)) (inputs : List (EdgeValue Symbol Guard))
    (before : SharedState width) (results : List (EdgeValue Symbol Guard)) (after : SharedState width) (memos _final : Memos) : Prop :=
  ∀ inventory, Populated (.editBelow entries) → Allowed record (.editBelow entries) →
    Ready formulas solver inventory record originals base before → Edges before.checked.native.machine.heap inputs →
    RowsSafe entries inputs → Valid before.checked.native.machine.heap memos →
    Values base originals → DChildren originals → SharedStored before → DRows inputs →
      SharedStored after ∧ All₂ EdgeNarrow inputs results

set_option maxHeartbeats 1600000 in
private theorem narrowing :
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
    intro next record originals path value before result after memos saved receipt inventory _ _ _ ready _ _ _ known capturedDomain stored domain
    exact SourceCurrentAllocatedFiniteOrdinaryReceiptStructure.leaf_receipt receipt ready known capturedDomain stored domain
  have emptyCase : ∀ {record originals entries state memos},
      NodeLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals
        (.editBelow entries) (.empty : Value Symbol Guard) state .empty state memos memos := by
    intro record originals entries state memos inventory _ _ _ _ _ _ _ _ _ stored domain
    exact ⟨stored, SourceCurrentAllocatedFiniteOrdinaryNarrow.node_refl domain⟩
  have ordinaryCase : ∀ {record originals memos saved entries edges before rebuilt middle value heap entry depth free}
      {actual : EditRows record originals entries edges before rebuilt middle}
      {built : run (makeNode rebuilt) middle.checked.native.machine.heap = (value, heap)},
      RowsReads formulas solver base actual memos saved →
      RowsLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries edges before rebuilt middle memos saved →
      NodeLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals
        (.editBelow entries) (.node entry edges depth free) before value (advanceHeap middle heap) memos saved := by
    intro record originals memos saved entries edges before rebuilt middle value heap entry depth free actual built reads ih
      inventory populated _ allowed ready available safe valid known capturedDomain stored domain
    have facts := ready.checked.semantic.ready.semantic.1.normal.facts
    have resident := InternedEdgeResidency.resident_edges _ facts.linked _ available.resident
    have related := ih inventory populated allowed ready resident (ordinary_rows safe) valid known capturedDomain stored domain.rows
    obtain ⟨next, checked⟩ := SourceCurrentAllocatedSharedEditEffects.rows_effects reads populated allowed ready resident (ordinary_rows safe) valid
    have currentFacts := checked.ready.checked.semantic.ready.semantic.1.normal.facts
    have resultBound := SourceCurrentAllocatedFiniteOrdinaryNarrow.makeNode entry edges rebuilt depth free
      middle.checked.native.machine.heap currentFacts.coherent currentFacts.linked checked.available related.2
    exact ⟨SourceCurrentAllocatedFiniteOrdinaryShared.advance_heap_stored middle heap related.1,
      by simpa only [built] using resultBound⟩
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
      _ _ _ _ inventory _ _ _ _ _ _ _ _ _ _ domain
    cases domain <;> cases recursive
  have nilChildren : ∀ {record originals entries offset state memos},
      ChildrenLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries offset
        ([] : List (Value Symbol Guard)) state [] state memos memos := by
    intro record originals entries offset state memos inventory _ _ _ _ _ _ _ _ stored _
    exact ⟨stored, .nil⟩
  have unselectedCase : ∀ {record originals memos saved entries values before results after value} {offset : Nat}
      {absent : SourceEqualityNeededMap.lookup (offset : Int) entries = none}
      {rest : EditChildren record originals entries (offset + 1) values before results after},
      ChildrenReads formulas solver base rest memos saved →
      ChildrenLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries (offset + 1) values before results after memos saved →
      ChildrenLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries offset (value :: values) before (value :: results) after memos saved := by
    intro record originals memos saved entries values before results after value offset absent rest reads ih
      inventory populated allowed ready available safe valid known capturedDomain stored domain
    cases domain with
    | cons firstDomain restDomain =>
        have later := ih inventory populated allowed ready
          (fun original member => available original (List.mem_cons_of_mem _ member)) (children_tail safe) valid
          known capturedDomain stored restDomain
        exact ⟨later.1, .cons (SourceCurrentAllocatedFiniteOrdinaryNarrow.node_refl firstDomain) later.2⟩
  have selectedCase : ∀ {record originals memos current saved entries edits value before result middle values results after} {offset : Nat}
      {found : SourceEqualityNeededMap.lookup (offset : Int) entries = some edits}
      {first : EditNode record originals edits value before result middle}
      {rest : EditChildren record originals entries (offset + 1) values middle results after},
      NodeReads formulas solver base first memos current → ChildrenReads formulas solver base rest current saved →
      NodeLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals edits value before result middle memos current →
      ChildrenLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries (offset + 1) values middle results after current saved →
      ChildrenLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries offset (value :: values) before (result :: results) after memos saved := by
    intro record originals memos current saved entries edits value before result middle values results after offset found first rest
      firstReads restReads firstIH restIH inventory populated allowed ready available safe valid known capturedDomain stored domain
    cases domain with
    | cons firstDomain restDomain =>
        have member := SourceEqualityNeededMap.lookup_mem _ _ _ found
        have children := (show ∀ index child, (index, child) ∈ entries → Populated child ∧ HasLeaf child from
          by simpa only [Populated] using populated)
        have childAllowed : Allowed record edits := by
          rw [Allowed, All] at allowed
          exact allowed _ _ member
        have firstSafe := safe 0 _ (by simpa using found) value rfl
        have related := firstIH inventory (children _ _ member).1 (children _ _ member).2 childAllowed
          ready (available _ List.mem_cons_self) firstSafe valid known capturedDomain stored firstDomain
        obtain ⟨middleInventory, checked⟩ := SourceCurrentAllocatedSharedEditEffects.node_effects firstReads
          (children _ _ member).1 (children _ _ member).2 childAllowed ready (available _ List.mem_cons_self) firstSafe valid
        have later := restIH middleInventory populated allowed checked.ready
          (fun original member => checked.effects.keeps.available original (available original (List.mem_cons_of_mem _ member)))
          (children_tail safe) checked.globals.valid known capturedDomain related.1 restDomain
        exact ⟨later.1, .cons related.2 later.2⟩
  have nilRows : ∀ {record originals entries state memos},
      RowsLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries
        ([] : List (EdgeValue Symbol Guard)) state [] state memos memos := by
    intro record originals entries state memos inventory _ _ _ _ _ _ _ _ stored _
    exact ⟨stored, .nil⟩
  have consCase : ∀ {record originals memos current saved entries before values middle result heap edges results after edge}
      {children : EditChildren record originals entries 0 edge.children before values middle}
      {rebuilt : run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.checked.native.machine.heap = (result, heap)}
      {rest : EditRows record originals entries edges (advanceHeap middle heap) results after},
      ChildrenReads formulas solver base children memos current → RowsReads formulas solver base rest current saved →
      ChildrenLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries 0 edge.children before values middle memos current →
      RowsLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries edges (advanceHeap middle heap) results after current saved →
      RowsLaw (width := width) (formulas := formulas) (solver := solver) (base := base) record originals entries (edge :: edges) before (result :: results) after memos saved := by
    intro record originals memos current saved entries before values middle result heap edges results after edge children rebuilt rest
      firstReads restReads firstIH restIH inventory populated allowed ready resident safe valid known capturedDomain stored domain
    cases domain with
    | cons childDomain restDomain =>
        have facts := ready.checked.semantic.ready.semantic.1.normal.facts
        have available := facts.cached.edges edge.entry.key edge (resident _ List.mem_cons_self)
        have related := firstIH inventory populated allowed ready available (safe _ List.mem_cons_self) valid
          known capturedDomain stored childDomain
        obtain ⟨middleInventory, checked⟩ := SourceCurrentAllocatedSharedEditEffects.children_effects firstReads
          populated allowed ready available (safe _ List.mem_cons_self) valid
        have field := (ready.checked.good.fields _ _ (resident _ List.mem_cons_self)).grows checked.effects.grows
        have rebuiltPhysical := SourceCurrentAllocatedSharedEditEffects.edge_physical checked.ready edge.entry.key.symbol
          edge.entry.key.constraint values field checked.available
        have edgeReady : Ready formulas solver middleInventory record originals base (advanceHeap middle heap) := by
          simpa only [rebuilt] using rebuiltPhysical.1
        have edgeKeeps : Keeps middle.checked.native.machine.heap heap := by
          have keeps := rebuiltPhysical.2.1.keeps
          change Keeps middle.checked.native.machine.heap
            (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.checked.native.machine.heap).2 at keeps
          simpa only [rebuilt] using keeps
        have currentFacts := checked.ready.checked.semantic.ready.semantic.1.normal.facts
        have resultBound := SourceCurrentAllocatedFiniteOrdinaryNarrow.makeEdge edge values middle.checked.native.machine.heap
          currentFacts.coherent currentFacts.cached checked.available related.2
        have currentValid := SourceQueryUnfoldMemo.valid_grows _ _ checked.ready.checked.semantic edgeKeeps current checked.globals.valid
        have later := restIH middleInventory populated allowed edgeReady
          (fun original member => InternedEdgeResidency.edge_grows _ _ (checked.effects.keeps.trans edgeKeeps).growth original
            (resident original (List.mem_cons_of_mem _ member)))
          (fun original member => safe original (List.mem_cons_of_mem _ member)) currentValid known capturedDomain
          (SourceCurrentAllocatedFiniteOrdinaryShared.advance_heap_stored middle heap related.1) restDomain
        exact ⟨later.1, .cons (by simpa only [rebuilt] using resultBound) later.2⟩
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

variable {inventory : Inventory} {record : SourceEqualityClassOrder.Record}
variable {originals : List (Value Symbol Guard)}

/-- Actual node reads derive domain and height bounds at the same returned state. -/
theorem node {edits value before result after memos final}
    {actual : EditNode (width := width) record originals edits value before result after}
    (reads : NodeReads formulas solver base actual memos final)
    (populated : Populated edits) (nonempty : HasLeaf edits) (allowed : Allowed record edits)
    (ready : Ready formulas solver inventory record originals base before)
    (available : Available before.checked.native.machine.heap value) (safe : Safe edits value)
    (valid : Valid before.checked.native.machine.heap memos)
    (known : Values base originals) (capturedDomain : DChildren originals) (stored : SharedStored before) (domain : DNode value) :
    SharedStored after ∧ NodeNarrow value result :=
  narrowing.1 reads inventory populated nonempty allowed ready available safe valid known capturedDomain stored domain

/-- Actual child reads retain ordered domain and height bounds for every position. -/
theorem children {entries offset values before results after memos final}
    {actual : EditChildren (width := width) record originals entries offset values before results after}
    (reads : ChildrenReads formulas solver base actual memos final)
    (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : Ready formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap values) (safe : ChildrenSafe entries offset values)
    (valid : Valid before.checked.native.machine.heap memos)
    (known : Values base originals) (capturedDomain : DChildren originals) (stored : SharedStored before) (domain : DChildren values) :
    SharedStored after ∧ All₂ NodeNarrow values results :=
  narrowing.2.1 reads inventory populated allowed ready available safe valid known capturedDomain stored domain

/-- Actual row reads retain the original row order and full child-height bounds. -/
theorem rows {entries edges before results after memos final}
    {actual : EditRows (width := width) record originals entries edges before results after}
    (reads : RowsReads formulas solver base actual memos final)
    (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : Ready formulas solver inventory record originals base before)
    (available : Edges before.checked.native.machine.heap edges) (safe : RowsSafe entries edges)
    (valid : Valid before.checked.native.machine.heap memos)
    (known : Values base originals) (capturedDomain : DChildren originals) (stored : SharedStored before) (domain : DRows edges) :
    SharedStored after ∧ All₂ EdgeNarrow edges results :=
  narrowing.2.2 reads inventory populated allowed ready available safe valid known capturedDomain stored domain

/-- Actual list edits retain every original position and all three structural tables. -/
theorem list {edits values before results after memos final}
    {actual : EditList (width := width) record originals edits values before results after}
    (reads : ListReads formulas solver base actual memos final)
    (populated : Populated edits) (allowed : Allowed record edits)
    (ready : Ready formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap values)
    (safe : SourceCurrentAllocatedSharedEditEffects.ListSafe edits values)
    (valid : Valid before.checked.native.machine.heap memos)
    (known : Values base originals) (capturedDomain : DChildren originals) (stored : SharedStored before) (domain : DChildren values) :
    SharedStored after ∧ All₂ NodeNarrow values results := by
  cases reads with
  | leaf => exact ⟨stored, SourceCurrentAllocatedFiniteOrdinaryNarrow.forest_refl domain⟩
  | children read => exact children read populated allowed ready available safe valid known capturedDomain stored domain

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEdits
