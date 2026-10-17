import MicroCFTA.SourceCurrentConstrainedCapEditSupport
import MicroCFTA.SourceCurrentConstrainedCapSharedSupport
import MicroCFTA.SourceCurrentConstrainedCapRichStoreEffects
import MicroCFTA.SourceCurrentConstrainedCapMaskCharacterization

/-!
# Rich causal stores through actual mixed-cap shared edits

Every leaf uses its actual receipt, captured original masks, and the local
rich store. No leaf certificate or recursive callback law is an input.
Selected callbacks receive immutable original inputs. The returned ordered
relation retains every initial supported path and the same finite cap.
This verifies supplied reads in the hereditary leaf-placement family. It
does not establish completion for the broader source selected-path gate.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapRichEditSupport
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityAnnotationLanguage SourceEqualityEdits
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentEditDomains SourceCurrentAllocatedSharedEditGraph
open SourceCurrentConstrainedCapPaths (ForestSupported)
open SourceCurrentConstrainedCapEditSupport
open SourceCurrentConstrainedCapRequiredSupport (Preserves)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "HeapState" => InternedConstructorTemplates.State Symbol Guard
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "Stored" => SourceCurrentConstrainedCapSharedSupport.Stored
local notation "Cap" => SourceCurrentConstrainedCap.Cap
local notation "EdgeCap" => SourceCurrentConstrainedCap.Edge
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula} {base : HeapState}

private def NodeGoal {record originals edits input before result after}
    (_actual : EditNode (width := width) record originals edits input before result after) (memos : Memos) : Prop :=
  ∀ inventory depth, Populated edits → HasLeaf edits → Allowed record edits →
    Ready formulas solver inventory record originals base before → Available before.checked.native.machine.heap input →
    Safe edits input → Valid before.checked.native.machine.heap memos →
    Values base originals → ClosedValues originals →
    (∀ path ∈ record.paths, ForestSupported Plain (path.map Int.ofNat) originals) →
    Stored record originals before → Cap Plain depth input → AtLeaves Plain edits input →
    Stored record originals after ∧ Preserves Plain input result

private def ChildrenGoal {record originals entries offset inputs before results after}
    (_actual : EditChildren (width := width) record originals entries offset inputs before results after) (memos : Memos) : Prop :=
  ∀ inventory depth, Populated (.editBelow entries) → Allowed record (.editBelow entries) →
    Ready formulas solver inventory record originals base before → Values before.checked.native.machine.heap inputs →
    ChildrenSafe entries offset inputs → Valid before.checked.native.machine.heap memos →
    Values base originals → ClosedValues originals →
    (∀ path ∈ record.paths, ForestSupported Plain (path.map Int.ofNat) originals) →
    Stored record originals before → (∀ value ∈ inputs, Cap Plain depth value) →
    ChildrenAtLeaves Plain entries offset inputs →
    Stored record originals after ∧ All₂ (Preserves Plain) inputs results

private def RowsGoal {record originals entries inputs before results after}
    (_actual : EditRows (width := width) record originals entries inputs before results after) (memos : Memos) : Prop :=
  ∀ inventory depth, Populated (.editBelow entries) → Allowed record (.editBelow entries) →
    Ready formulas solver inventory record originals base before → Edges before.checked.native.machine.heap inputs →
    RowsSafe entries inputs → Valid before.checked.native.machine.heap memos →
    Values base originals → ClosedValues originals →
    (∀ path ∈ record.paths, ForestSupported Plain (path.map Int.ofNat) originals) →
    Stored record originals before → (∀ edge ∈ inputs, EdgeCap Plain depth edge) →
    RowsAtLeaves Plain entries inputs →
    Stored record originals after ∧ All₂ (RowPreserves Plain) inputs results

set_option maxHeartbeats 1600000 in
private theorem all_reads :
    (∀ {record originals edits value before result after} {memos final : Memos}
      {actual : EditNode (width := width) record originals edits value before result after},
      NodeReads formulas solver base actual memos final → NodeGoal (width := width) (formulas := formulas) (solver := solver) (base := base) actual memos) ∧
    (∀ {record originals entries offset values before results after} {memos final : Memos}
      {actual : EditChildren (width := width) record originals entries offset values before results after},
      ChildrenReads formulas solver base actual memos final → ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base) actual memos) ∧
    (∀ {record originals entries edges before results after} {memos final : Memos}
      {actual : EditRows (width := width) record originals entries edges before results after},
      RowsReads formulas solver base actual memos final → RowsGoal (width := width) (formulas := formulas) (solver := solver) (base := base) actual memos) := by
  have leafCase : ∀ {next record originals path value before result after memos saved}
      (receipt : SourceCurrentAllocatedSharedTargetLeaf.Receipt formulas solver next record originals base path value before result after memos saved),
      NodeGoal (width := width) (formulas := formulas) (solver := solver) (base := base) (.leaf receipt.actual) memos := by
    intro next record originals path value before result after memos saved receipt inventory depth _ _ _ ready available safe _ known capturedClosed capturedMasks stored _ placed
    have inputClosed : value.free = [] :=
      safe [] path (by simp only [SourceEqualityEditLeafPaths.leaves, List.mem_singleton])
    have output := SourceCurrentConstrainedCapSharedSupport.leaf_receipt receipt ready known capturedClosed stored
      (SourceCurrentConstrainedCapPaths.operand_paths Plain record.paths path originals capturedMasks)
      available inputClosed (at_root placed)
    exact ⟨output.1, preserves_of_annotated Plain value result output.2⟩
  have emptyCase : ∀ {record originals entries state memos},
      NodeGoal (width := width) (formulas := formulas) (solver := solver) (base := base)
        (.empty (record := record) (originals := originals) (entries := entries) (state := state)) memos := by
    intro record originals entries state memos inventory depth _ _ _ _ _ _ _ _ _ _ stored _ _
    exact ⟨stored, preserves_refl Plain .empty⟩
  have ordinaryCase : ∀ {record originals memos saved entries edges before rebuilt middle value heap entry depth free}
      {actual : EditRows record originals entries edges before rebuilt middle}
      {built : run (InternedConstructorTemplates.makeNode rebuilt) middle.checked.native.machine.heap = (value, heap)},
      RowsReads formulas solver base actual memos saved →
      RowsGoal (width := width) (formulas := formulas) (solver := solver) (base := base) actual memos →
      NodeGoal (width := width) (formulas := formulas) (solver := solver) (base := base)
        (.ordinary (entry := entry) (depth := depth) (free := free) actual built) memos := by
    intro record originals memos saved entries edges before rebuilt middle value heap entry depth free actual built reads ih
      inventory capDepth populated _ allowed ready available safe valid known capturedClosed capturedMasks stored bounded placed
    have facts := ready.checked.semantic.ready.semantic.1.normal.facts
    have resident := InternedEdgeResidency.resident_edges _ facts.linked _ available.resident
    have related := ih inventory capDepth populated allowed ready resident (SourceCurrentEditDomains.ordinary_rows safe)
      valid known capturedClosed capturedMasks stored (fun edge member => SourceCurrentConstrainedCap.node_edge bounded edge member) (ordinary_rows placed)
    obtain ⟨next, checked⟩ := SourceCurrentAllocatedSharedEditEffects.rows_effects reads populated allowed ready resident
      (SourceCurrentEditDomains.ordinary_rows safe) valid
    have currentFacts := checked.ready.checked.semantic.ready.semantic.1.normal.facts
    have narrowed := makeNode Plain entry edges rebuilt depth free middle.checked.native.machine.heap
      currentFacts.coherent currentFacts.linked checked.available related.2
    have nodeStore := SourceCurrentConstrainedCapRichStoreEffects.node checked.ready rebuilt checked.available related.1
    exact ⟨by simpa only [built] using nodeStore.1, by simpa only [built] using narrowed⟩
  have recursiveCase : ∀ {record originals memos current saved entries original before exposed heap value after}
      {recursive : SourceEqualityRequiredGraph.Recursive original}
      {head : SourceEqualityRequiredHead.Head original before.checked.native.machine.heap exposed heap}
      {body : EditNode record originals (.editBelow entries) exposed (advanceHeap before heap) value after},
      SourceCurrentRequiredQueryMemos.HeadReads head memos current →
      SourceCurrentSubsumesQueryMemos.Effect before.checked.native.machine.heap heap memos current →
      NodeReads formulas solver base body current saved →
      NodeGoal (width := width) (formulas := formulas) (solver := solver) (base := base) body current →
      NodeGoal (width := width) (formulas := formulas) (solver := solver) (base := base) (.recursive recursive head body) memos := by
    intro record originals memos current saved entries original before exposed heap value after recursive actual body
      headReads headGlobal bodyReads ih inventory depth populated nonempty allowed ready available safe _ known capturedClosed capturedMasks stored bounded placed
    have closed := recursive_closed recursive nonempty safe
    have localHead := SourceCurrentConstrainedCapRichStoreEffects.head depth ready actual available closed bounded stored
    have physical := SourceCurrentAllocatedSharedEditEffects.head_physical ready actual available
    have headReady : Ready formulas solver inventory record originals base (advanceHeap before heap) := physical.1
    have headSafe : Safe (.editBelow entries) exposed := by
      have checked := actual.verified ready.checked.semantic.ready available closed
      exact closed_safe _ exposed heap headGlobal.semantic checked.2.1 checked.2.2.1
    have later := ih inventory depth populated nonempty allowed headReady physical.2.2 headSafe
      headGlobal.valid known capturedClosed capturedMasks localHead.1 localHead.2.2.2.2.1 (placement_preserved localHead.2.2.2.2.2 placed)
    exact ⟨later.1, preserves_trans localHead.2.2.2.2.2 later.2⟩
  have nilChildren : ∀ {record originals entries offset state memos},
      ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base)
        (.nil (record := record) (originals := originals) (entries := entries) (index := offset) (state := state)) memos := by
    intro record originals entries offset state memos inventory depth _ _ _ _ _ _ _ _ _ stored _ _
    exact ⟨stored, .nil⟩
  have unselectedCase : ∀ {record originals memos saved entries values before results after value} {offset : Nat}
      {absent : SourceEqualityNeededMap.lookup (offset : Int) entries = none}
      {rest : EditChildren record originals entries (offset + 1) values before results after},
      ChildrenReads formulas solver base rest memos saved →
      ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base) rest memos →
      ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base) (.unselected (value := value) offset absent rest) memos := by
    intro record originals memos saved entries values before results after value offset absent rest _ ih inventory depth
      populated allowed ready available safe valid known capturedClosed capturedMasks stored bounded placed
    have later := ih inventory depth populated allowed ready
      (fun child member => available child (List.mem_cons_of_mem _ member)) (SourceCurrentEditDomains.children_tail safe) valid known capturedClosed capturedMasks stored
      (fun child member => bounded child (List.mem_cons_of_mem _ member)) (children_tail placed)
    exact ⟨later.1, .cons (preserves_refl Plain value) later.2⟩
  have selectedCase : ∀ {record originals memos current saved entries edits value before result middle values results after} {offset : Nat}
      {found : SourceEqualityNeededMap.lookup (offset : Int) entries = some edits}
      {first : EditNode record originals edits value before result middle}
      {rest : EditChildren record originals entries (offset + 1) values middle results after},
      NodeReads formulas solver base first memos current → ChildrenReads formulas solver base rest current saved →
      NodeGoal (width := width) (formulas := formulas) (solver := solver) (base := base) first memos →
      ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base) rest current →
      ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base) (.selected offset found first rest) memos := by
    intro record originals memos current saved entries edits value before result middle values results after offset found first rest
      firstReads _ firstIH restIH inventory depth populated allowed ready available safe valid known capturedClosed capturedMasks stored bounded placed
    have member := SourceEqualityNeededMap.lookup_mem _ _ _ found
    have children := (show ∀ index child, (index, child) ∈ entries → Populated child ∧ HasLeaf child from
      by simpa only [Populated] using populated)
    have childAllowed : Allowed record edits := by
      rw [Allowed, All] at allowed
      exact allowed _ _ member
    have firstSafe := safe 0 _ (by simpa using found) value rfl
    have related := firstIH inventory depth (children _ _ member).1 (children _ _ member).2 childAllowed
      ready (available _ List.mem_cons_self) firstSafe valid known capturedClosed capturedMasks stored (bounded _ List.mem_cons_self) (children_head placed found)
    obtain ⟨middleInventory, checked⟩ := SourceCurrentAllocatedSharedEditEffects.node_effects firstReads
      (children _ _ member).1 (children _ _ member).2 childAllowed ready (available _ List.mem_cons_self) firstSafe valid
    have later := restIH middleInventory depth populated allowed checked.ready
      (fun original member => checked.effects.keeps.available original (available original (List.mem_cons_of_mem _ member)))
      (SourceCurrentEditDomains.children_tail safe) checked.globals.valid known capturedClosed capturedMasks related.1
      (fun original member => bounded original (List.mem_cons_of_mem _ member)) (children_tail placed)
    exact ⟨later.1, .cons related.2 later.2⟩
  have nilRows : ∀ {record originals entries state memos},
      RowsGoal (width := width) (formulas := formulas) (solver := solver) (base := base)
        (.nil (record := record) (originals := originals) (entries := entries) (state := state)) memos := by
    intro record originals entries state memos inventory depth _ _ _ _ _ _ _ _ _ stored _ _
    exact ⟨stored, .nil⟩
  have consCase : ∀ {record originals memos current saved entries before values middle result heap edges results after} {edge : EdgeValue Symbol Guard}
      {children : EditChildren record originals entries 0 edge.children before values middle}
      {rebuilt : run (InternedConstructorTemplates.makeEdge edge.entry.key.symbol edge.entry.key.constraint values)
        middle.checked.native.machine.heap = (result, heap)}
      {rest : EditRows record originals entries edges (advanceHeap middle heap) results after},
      ChildrenReads formulas solver base children memos current → RowsReads formulas solver base rest current saved →
      ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base) children memos →
      RowsGoal (width := width) (formulas := formulas) (solver := solver) (base := base) rest current →
      RowsGoal (width := width) (formulas := formulas) (solver := solver) (base := base) (.cons children rebuilt rest) memos := by
    intro record originals memos current saved entries before values middle result heap edges results after edge children rebuilt rest
      firstReads _ firstIH restIH inventory depth populated allowed ready resident safe valid known capturedClosed capturedMasks stored bounded placed
    have facts := ready.checked.semantic.ready.semantic.1.normal.facts
    have available := facts.cached.edges edge.entry.key edge (resident _ List.mem_cons_self)
    have childCaps : ∀ child ∈ edge.children, Cap Plain (depth - 1) child := by
      cases depth with
      | zero => exact fun child member => .plain 0 ((bounded _ List.mem_cons_self).2 child member)
      | succ depth => exact bounded _ List.mem_cons_self
    have related := firstIH inventory (depth - 1) populated allowed ready available (safe _ List.mem_cons_self)
      valid known capturedClosed capturedMasks stored childCaps (placed _ List.mem_cons_self)
    obtain ⟨middleInventory, checked⟩ := SourceCurrentAllocatedSharedEditEffects.children_effects firstReads
      populated allowed ready available (safe _ List.mem_cons_self) valid
    have field := (ready.checked.good.fields _ _ (resident _ List.mem_cons_self)).grows checked.effects.grows
    have rebuiltPhysical := SourceCurrentAllocatedSharedEditEffects.edge_physical checked.ready edge.entry.key.symbol
      edge.entry.key.constraint values field checked.available
    have edgeReady : Ready formulas solver middleInventory record originals base (advanceHeap middle heap) := by
      simpa only [rebuilt] using rebuiltPhysical.1
    have edgeKeeps : SourceEqualityRequiredCache.Keeps middle.checked.native.machine.heap heap := by
      have keeps := rebuiltPhysical.2.1.keeps
      change SourceEqualityRequiredCache.Keeps middle.checked.native.machine.heap
        (run (InternedConstructorTemplates.makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.checked.native.machine.heap).2 at keeps
      simpa only [rebuilt] using keeps
    have currentFacts := checked.ready.checked.semantic.ready.semantic.1.normal.facts
    have resultMask := makeEdge Plain edge values middle.checked.native.machine.heap
      currentFacts.coherent currentFacts.cached checked.available related.2
    have edgeStore : Stored record originals (advanceHeap middle heap) := by
      have emitted := SourceCurrentConstrainedCapRichStoreEffects.edge checked.ready edge.entry.key.symbol edge.entry.key.constraint values field checked.available related.1
      simpa only [rebuilt] using emitted.1
    have currentValid := SourceQueryUnfoldMemo.valid_grows _ _ checked.ready.checked.semantic edgeKeeps current checked.globals.valid
    have later := restIH middleInventory depth populated allowed edgeReady
      (fun original member => InternedEdgeResidency.edge_grows _ _ (checked.effects.keeps.trans edgeKeeps).growth original
        (resident original (List.mem_cons_of_mem _ member)))
      (fun original member => safe original (List.mem_cons_of_mem _ member)) currentValid known capturedClosed capturedMasks edgeStore
      (fun original member => bounded original (List.mem_cons_of_mem _ member))
      (fun original member => placed original (List.mem_cons_of_mem _ member))
    exact ⟨later.1, .cons (by simpa only [rebuilt] using resultMask) later.2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro record originals edits value before result after memos final actual reads
    exact NodeReads.rec
      (motive_1 := fun {record originals edits value before result after} actual memos _ _ =>
        NodeGoal (width := width) (formulas := formulas) (solver := solver) (base := base) actual memos)
      (motive_2 := fun {record originals entries offset values before results after} actual memos _ _ =>
        ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base) actual memos)
      (motive_3 := fun {record originals entries edges before results after} actual memos _ _ =>
        RowsGoal (width := width) (formulas := formulas) (solver := solver) (base := base) actual memos)
      @leafCase @emptyCase @ordinaryCase @recursiveCase @nilChildren @unselectedCase @selectedCase @nilRows @consCase reads
  · intro record originals entries offset values before results after memos final actual reads
    exact ChildrenReads.rec
      (motive_1 := fun {record originals edits value before result after} actual memos _ _ =>
        NodeGoal (width := width) (formulas := formulas) (solver := solver) (base := base) actual memos)
      (motive_2 := fun {record originals entries offset values before results after} actual memos _ _ =>
        ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base) actual memos)
      (motive_3 := fun {record originals entries edges before results after} actual memos _ _ =>
        RowsGoal (width := width) (formulas := formulas) (solver := solver) (base := base) actual memos)
      @leafCase @emptyCase @ordinaryCase @recursiveCase @nilChildren @unselectedCase @selectedCase @nilRows @consCase reads
  · intro record originals entries edges before results after memos final actual reads
    exact RowsReads.rec
      (motive_1 := fun {record originals edits value before result after} actual memos _ _ =>
        NodeGoal (width := width) (formulas := formulas) (solver := solver) (base := base) actual memos)
      (motive_2 := fun {record originals entries offset values before results after} actual memos _ _ =>
        ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base) actual memos)
      (motive_3 := fun {record originals entries edges before results after} actual memos _ _ =>
        RowsGoal (width := width) (formulas := formulas) (solver := solver) (base := base) actual memos)
      @leafCase @emptyCase @ordinaryCase @recursiveCase @nilChildren @unselectedCase @selectedCase @nilRows @consCase reads


/-- Actual node reads retain rich stores, every input path mask, and the original cap depth. -/
theorem node {record originals edits value before result after memos final}
    {actual : EditNode (width := width) record originals edits value before result after}
    (reads : NodeReads formulas solver base actual memos final)
    (inventory : Inventory) (depth : Nat) (populated : Populated edits) (nonempty : HasLeaf edits) (allowed : Allowed record edits)
    (ready : Ready formulas solver inventory record originals base before) (available : Available before.checked.native.machine.heap value)
    (safe : Safe edits value) (valid : Valid before.checked.native.machine.heap memos)
    (known : Values base originals) (capturedClosed : ClosedValues originals)
    (capturedMasks : ∀ path ∈ record.paths, ForestSupported Plain (path.map Int.ofNat) originals)
    (stored : Stored record originals before) (bounded : Cap Plain depth value) (placed : AtLeaves Plain edits value) :
    Stored record originals after ∧ Preserves Plain value result ∧ Cap Plain depth result := by
  have retained := all_reads.1 reads inventory depth populated nonempty allowed ready available safe valid
    known capturedClosed capturedMasks stored bounded placed
  exact ⟨retained.1, retained.2, SourceCurrentConstrainedCapMaskCharacterization.preserves_cap retained.2 bounded⟩

/-- Actual child scans retain original signed slots, all masks, and the same cap depth. -/
theorem children {record originals entries offset values before results after memos final}
    {actual : EditChildren (width := width) record originals entries offset values before results after}
    (reads : ChildrenReads formulas solver base actual memos final)
    (inventory : Inventory) (depth : Nat) (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : Ready formulas solver inventory record originals base before) (available : Values before.checked.native.machine.heap values)
    (safe : ChildrenSafe entries offset values) (valid : Valid before.checked.native.machine.heap memos)
    (known : Values base originals) (capturedClosed : ClosedValues originals)
    (capturedMasks : ∀ path ∈ record.paths, ForestSupported Plain (path.map Int.ofNat) originals)
    (stored : Stored record originals before) (bounded : ∀ value ∈ values, Cap Plain depth value)
    (placed : ChildrenAtLeaves Plain entries offset values) :
    Stored record originals after ∧ All₂ (Preserves Plain) values results ∧ ∀ value ∈ results, Cap Plain depth value := by
  have retained := all_reads.2.1 reads inventory depth populated allowed ready available safe valid
    known capturedClosed capturedMasks stored bounded placed
  exact ⟨retained.1, retained.2, SourceCurrentConstrainedCapMaskCharacterization.children_cap retained.2 bounded⟩

private theorem row_cap {depth : Nat} {original result : EdgeValue Symbol Guard}
    (related : RowPreserves Plain original result) (bounded : EdgeCap Plain depth original) : EdgeCap Plain depth result := by
  cases depth with
  | zero =>
      refine ⟨related.1.symm ▸ bounded.1, ?_⟩
      exact SourceCurrentConstrainedCapRequiredSupport.forest_supported Plain related.2 [] bounded.2
  | succ depth =>
      exact SourceCurrentConstrainedCapMaskCharacterization.children_cap related.2 bounded

private theorem rows_cap {depth : Nat} {originals results : List (EdgeValue Symbol Guard)}
    (related : All₂ (RowPreserves Plain) originals results) (bounded : ∀ edge ∈ originals, EdgeCap Plain depth edge) :
    ∀ edge ∈ results, EdgeCap Plain depth edge := by
  induction related with
  | nil => intro edge member; cases member
  | cons first rest ih =>
      intro edge member
      rcases List.mem_cons.mp member with rfl | member
      · exact row_cap first (bounded _ List.mem_cons_self)
      · exact ih (fun edge member => bounded edge (List.mem_cons_of_mem _ member)) edge member

/-- Actual rows retain their complete raw guard and every original supported child path. -/
theorem rows {record originals entries edges before results after memos final}
    {actual : EditRows (width := width) record originals entries edges before results after}
    (reads : RowsReads formulas solver base actual memos final)
    (inventory : Inventory) (depth : Nat) (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : Ready formulas solver inventory record originals base before) (resident : Edges before.checked.native.machine.heap edges)
    (safe : RowsSafe entries edges) (valid : Valid before.checked.native.machine.heap memos)
    (known : Values base originals) (capturedClosed : ClosedValues originals)
    (capturedMasks : ∀ path ∈ record.paths, ForestSupported Plain (path.map Int.ofNat) originals)
    (stored : Stored record originals before) (bounded : ∀ edge ∈ edges, EdgeCap Plain depth edge)
    (placed : RowsAtLeaves Plain entries edges) :
    Stored record originals after ∧ All₂ (RowPreserves Plain) edges results ∧ ∀ edge ∈ results, EdgeCap Plain depth edge := by
  have retained := all_reads.2.2 reads inventory depth populated allowed ready resident safe valid
    known capturedClosed capturedMasks stored bounded placed
  exact ⟨retained.1, retained.2, rows_cap retained.2 bounded⟩

/-- The whole actual forest edit derives every leaf law from its initial stores and placement. -/
theorem list {record originals edits values before results after memos final}
    {actual : EditList (width := width) record originals edits values before results after}
    (reads : ListReads formulas solver base actual memos final)
    (inventory : Inventory) (depth : Nat) (populated : Populated edits) (allowed : Allowed record edits)
    (ready : Ready formulas solver inventory record originals base before) (available : Values before.checked.native.machine.heap values)
    (safe : SourceCurrentAllocatedSharedEditEffects.ListSafe edits values) (valid : Valid before.checked.native.machine.heap memos)
    (known : Values base originals) (capturedClosed : ClosedValues originals)
    (capturedMasks : ∀ path ∈ record.paths, ForestSupported Plain (path.map Int.ofNat) originals)
    (stored : Stored record originals before) (bounded : ∀ value ∈ values, Cap Plain depth value)
    (placed : ListAtLeaves Plain edits values) :
    Stored record originals after ∧ All₂ (Preserves Plain) values results ∧ ∀ value ∈ results, Cap Plain depth value := by
  cases reads with
  | leaf => exact ⟨stored, forest_refl Plain values, bounded⟩
  | children read =>
      exact children read inventory depth populated allowed ready available safe valid known capturedClosed capturedMasks stored bounded placed

end MicroCFTA.SourceCurrentConstrainedCapRichEditSupport
