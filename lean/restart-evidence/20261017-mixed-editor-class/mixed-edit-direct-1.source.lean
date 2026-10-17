import MicroCFTA.SourceCurrentConstrainedCapMixedEditStoreEffects

/-!
# Finite-depth caps through actual mixed shared edits

The immutable edit syntax supplies a finite output bound. Actual leaf
receipts derive their target and native cap at the reached state. Ordinary
constructors retain their exact original raw guard and ordered child arity.
No hereditary leaf placement or whole captured-forest closure is required.
This module verifies supplied reads. It does not prove general completion.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapMixedEdit
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityEdits SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentEditDomains SourceCurrentAllocatedSharedEditGraph
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "HeapState" => InternedConstructorTemplates.State Symbol Guard
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Stored" => SourceCurrentConstrainedCapMixedShared.Stored
local notation "Cap" => SourceCurrentConstrainedCap.Cap
local notation "EdgeCap" => SourceCurrentConstrainedCap.Edge
local notation "Domain" => SourceEqualityProjectionPathDomain.ForestClosed

/-- Initial cap depths and the literal finite edit syntax bound the output. -/
def outputDepth (capturedDepth inputDepth : Nat) (edits : Edits EqualityNormalize.Path) : Nat :=
  inputDepth + capturedDepth + sizeOf edits

/-- Child scans reserve only their map size; row reconstruction supplies the parent layer. -/
def childrenDepth (capturedDepth inputDepth : Nat) (entries : List (Int × Edits EqualityNormalize.Path)) : Nat :=
  inputDepth + capturedDepth + sizeOf entries

private theorem fold_depth_le (depth : Nat) (seed : List Int) (paths : List (List Int)) :
    SourceCurrentConstrainedCapMixedTarget.foldDepth depth seed paths ≤ depth := by
  induction paths with
  | nil => exact Nat.sub_le _ _
  | cons path rest ih => exact Nat.max_le.mpr ⟨Nat.sub_le _ _, ih⟩

private theorem target_depth_le (depth : Nat) (paths : List (List Int)) :
    SourceCurrentConstrainedCapMixedTarget.targetDepth depth paths ≤ depth := by
  cases paths with
  | nil => exact Nat.zero_le _
  | cons seed rest => exact fold_depth_le depth seed rest

private theorem child_depth_le {capturedDepth inputDepth : Nat} {entries : List (Int × Edits EqualityNormalize.Path)}
    {index : Int} {edits : Edits EqualityNormalize.Path} (member : (index, edits) ∈ entries) :
    outputDepth capturedDepth inputDepth edits ≤ childrenDepth capturedDepth inputDepth entries := by
  have small := List.sizeOf_lt_of_mem member
  simp only [Prod.mk.sizeOf_spec] at small
  unfold outputDepth childrenDepth
  omega

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula} {base : HeapState}

private def NodeGoal {record originals edits input before result after}
    (_actual : EditNode (width := width) record originals edits input before result after) (memos : Memos) : Prop :=
  ∀ inventory capturedDepth depth, Populated edits → HasLeaf edits → Allowed record edits →
    Ready formulas solver inventory record originals base before → Available before.checked.native.machine.heap input →
    Safe edits input → Valid before.checked.native.machine.heap memos →
    Values base originals →
    (∀ path ∈ record.paths, Domain (path.map Int.ofNat) originals) →
    Stored record originals before → (∀ original ∈ originals, Cap Plain capturedDepth original) → Cap Plain depth input →
    Stored record originals after ∧ Cap Plain (outputDepth capturedDepth depth edits) result

private def ChildrenGoal {record originals entries offset inputs before results after}
    (_actual : EditChildren (width := width) record originals entries offset inputs before results after) (memos : Memos) : Prop :=
  ∀ inventory capturedDepth depth, Populated (.editBelow entries) → Allowed record (.editBelow entries) →
    Ready formulas solver inventory record originals base before → Values before.checked.native.machine.heap inputs →
    ChildrenSafe entries offset inputs → Valid before.checked.native.machine.heap memos →
    Values base originals →
    (∀ path ∈ record.paths, Domain (path.map Int.ofNat) originals) →
    Stored record originals before → (∀ original ∈ originals, Cap Plain capturedDepth original) →
    (∀ value ∈ inputs, Cap Plain depth value) →
    Stored record originals after ∧ ∀ value ∈ results, Cap Plain (childrenDepth capturedDepth depth entries) value

private def RowsGoal {record originals entries inputs before results after}
    (_actual : EditRows (width := width) record originals entries inputs before results after) (memos : Memos) : Prop :=
  ∀ inventory capturedDepth depth, Populated (.editBelow entries) → Allowed record (.editBelow entries) →
    Ready formulas solver inventory record originals base before → Edges before.checked.native.machine.heap inputs →
    RowsSafe entries inputs → Valid before.checked.native.machine.heap memos →
    Values base originals →
    (∀ path ∈ record.paths, Domain (path.map Int.ofNat) originals) →
    Stored record originals before → (∀ original ∈ originals, Cap Plain capturedDepth original) →
    (∀ edge ∈ inputs, EdgeCap Plain depth edge) →
    Stored record originals after ∧ ∀ edge ∈ results, EdgeCap Plain (outputDepth capturedDepth depth (.editBelow entries)) edge

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
    intro next record originals path value before result after memos saved receipt inventory capturedDepth depth _ _ _ ready available safe _ known capturedDomains stored capturedCaps bounded
    have inputClosed : value.free = [] := by
      simpa only [SourceEqualityProjectionPathDomain.NodeClosed] using
        safe [] path (by simp only [SourceEqualityEditLeafPaths.leaves, List.mem_singleton])
    have domains : ∀ operand ∈ SourceEqualityClassTarget.operandPaths record.paths path, Domain operand originals := by
      intro operand member
      obtain ⟨original, selected, rfl⟩ := List.mem_map.mp member
      exact capturedDomains original (List.mem_filter.mp selected).1
    have output := SourceCurrentConstrainedCapMixedShared.leaf_receipt receipt ready known stored capturedDepth
      capturedCaps domains available inputClosed depth bounded
    have small := target_depth_le capturedDepth (SourceEqualityClassTarget.operandPaths record.paths path)
    refine ⟨output.1, output.2.mono ?_⟩
    unfold SourceCurrentConstrainedCapMixedShared.leafDepth outputDepth
    omega
  have emptyCase : ∀ {record originals entries state memos},
      NodeGoal (width := width) (formulas := formulas) (solver := solver) (base := base)
        (.empty (record := record) (originals := originals) (entries := entries) (state := state)) memos := by
    intro record originals entries state memos inventory capturedDepth depth _ _ _ _ _ _ _ _ _ stored _ _
    exact ⟨stored, .plain _ .empty⟩
  have ordinaryCase : ∀ {record originals memos saved entries edges before rebuilt middle value heap entry depth free}
      {actual : EditRows record originals entries edges before rebuilt middle}
      {built : run (InternedConstructorTemplates.makeNode rebuilt) middle.checked.native.machine.heap = (value, heap)},
      RowsReads formulas solver base actual memos saved →
      RowsGoal (width := width) (formulas := formulas) (solver := solver) (base := base) actual memos →
      NodeGoal (width := width) (formulas := formulas) (solver := solver) (base := base)
        (.ordinary (entry := entry) (depth := depth) (free := free) actual built) memos := by
    intro record originals memos saved entries edges before rebuilt middle value heap entry depth free actual built reads ih
      inventory capturedDepth capDepth populated _ allowed ready available safe valid known capturedDomains stored capturedCaps bounded
    have facts := ready.checked.semantic.ready.semantic.1.normal.facts
    have resident := InternedEdgeResidency.resident_edges _ facts.linked _ available.resident
    have related := ih inventory capturedDepth capDepth populated allowed ready resident (SourceCurrentEditDomains.ordinary_rows safe)
      valid known capturedDomains stored capturedCaps (fun edge member => SourceCurrentConstrainedCap.node_edge bounded edge member)
    obtain ⟨next, checked⟩ := SourceCurrentAllocatedSharedEditEffects.rows_effects reads populated allowed ready resident
      (SourceCurrentEditDomains.ordinary_rows safe) valid
    have currentFacts := checked.ready.checked.semantic.ready.semantic.1.normal.facts
    have boundedResult := SourceCurrentConstrainedCap.makeNode Plain (outputDepth capturedDepth capDepth (.editBelow entries))
      rebuilt middle.checked.native.machine.heap currentFacts.coherent currentFacts.linked checked.available related.2
    have nodeStore := SourceCurrentConstrainedCapMixedEditStoreEffects.node checked.ready rebuilt checked.available related.1
    exact ⟨by simpa only [built] using nodeStore.1, by simpa only [built] using boundedResult⟩
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
      headReads headGlobal bodyReads ih inventory capturedDepth depth populated nonempty allowed ready available safe _ known capturedDomains stored capturedCaps bounded
    have closed := recursive_closed recursive nonempty safe
    have localHead := SourceCurrentConstrainedCapMixedEditStoreEffects.head depth ready actual available closed bounded stored
    have physical := SourceCurrentAllocatedSharedEditEffects.head_physical ready actual available
    have headReady : Ready formulas solver inventory record originals base (advanceHeap before heap) := physical.1
    have headSafe : Safe (.editBelow entries) exposed := by
      have checked := actual.verified ready.checked.semantic.ready available closed
      exact closed_safe _ exposed heap headGlobal.semantic checked.2.1 checked.2.2.1
    exact ih inventory capturedDepth depth populated nonempty allowed headReady physical.2.2 headSafe
      headGlobal.valid known capturedDomains localHead.1 capturedCaps localHead.2.2.2.2
  have nilChildren : ∀ {record originals entries offset state memos},
      ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base)
        (.nil (record := record) (originals := originals) (entries := entries) (index := offset) (state := state)) memos := by
    intro record originals entries offset state memos inventory capturedDepth depth _ _ _ _ _ _ _ _ _ stored _ _
    exact ⟨stored, by intro value member; cases member⟩
  have unselectedCase : ∀ {record originals memos saved entries values before results after value} {offset : Nat}
      {absent : SourceEqualityNeededMap.lookup (offset : Int) entries = none}
      {rest : EditChildren record originals entries (offset + 1) values before results after},
      ChildrenReads formulas solver base rest memos saved →
      ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base) rest memos →
      ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base) (.unselected (value := value) offset absent rest) memos := by
    intro record originals memos saved entries values before results after value offset absent rest _ ih inventory capturedDepth depth
      populated allowed ready available safe valid known capturedDomains stored capturedCaps bounded
    have later := ih inventory capturedDepth depth populated allowed ready
      (fun child member => available child (List.mem_cons_of_mem _ member)) (SourceCurrentEditDomains.children_tail safe)
      valid known capturedDomains stored capturedCaps (fun child member => bounded child (List.mem_cons_of_mem _ member))
    refine ⟨later.1, ?_⟩
    intro result member
    rcases List.mem_cons.mp member with rfl | member
    · exact (bounded _ List.mem_cons_self).mono (by unfold childrenDepth; omega)
    · exact later.2 result member
  have selectedCase : ∀ {record originals memos current saved entries edits value before result middle values results after} {offset : Nat}
      {found : SourceEqualityNeededMap.lookup (offset : Int) entries = some edits}
      {first : EditNode record originals edits value before result middle}
      {rest : EditChildren record originals entries (offset + 1) values middle results after},
      NodeReads formulas solver base first memos current → ChildrenReads formulas solver base rest current saved →
      NodeGoal (width := width) (formulas := formulas) (solver := solver) (base := base) first memos →
      ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base) rest current →
      ChildrenGoal (width := width) (formulas := formulas) (solver := solver) (base := base) (.selected offset found first rest) memos := by
    intro record originals memos current saved entries edits value before result middle values results after offset found first rest
      firstReads _ firstIH restIH inventory capturedDepth depth populated allowed ready available safe valid known capturedDomains stored capturedCaps bounded
    have member := SourceEqualityNeededMap.lookup_mem _ _ _ found
    have children := (show ∀ index child, (index, child) ∈ entries → Populated child ∧ HasLeaf child from
      by simpa only [Populated] using populated)
    have childAllowed : Allowed record edits := by
      rw [Allowed, All] at allowed
      exact allowed _ _ member
    have firstSafe := safe 0 _ (by simpa using found) value rfl
    have related := firstIH inventory capturedDepth depth (children _ _ member).1 (children _ _ member).2 childAllowed
      ready (available _ List.mem_cons_self) firstSafe valid known capturedDomains stored capturedCaps (bounded _ List.mem_cons_self)
    obtain ⟨middleInventory, checked⟩ := SourceCurrentAllocatedSharedEditEffects.node_effects firstReads
      (children _ _ member).1 (children _ _ member).2 childAllowed ready (available _ List.mem_cons_self) firstSafe valid
    have later := restIH middleInventory capturedDepth depth populated allowed checked.ready
      (fun original member => checked.effects.keeps.available original (available original (List.mem_cons_of_mem _ member)))
      (SourceCurrentEditDomains.children_tail safe) checked.globals.valid known capturedDomains related.1 capturedCaps
      (fun original member => bounded original (List.mem_cons_of_mem _ member))
    refine ⟨later.1, ?_⟩
    intro output memberOutput
    rcases List.mem_cons.mp memberOutput with rfl | remaining
    · exact related.2.mono (child_depth_le member)
    · exact later.2 output remaining
  have nilRows : ∀ {record originals entries state memos},
      RowsGoal (width := width) (formulas := formulas) (solver := solver) (base := base)
        (.nil (record := record) (originals := originals) (entries := entries) (state := state)) memos := by
    intro record originals entries state memos inventory capturedDepth depth _ _ _ _ _ _ _ _ _ stored _ _
    exact ⟨stored, by intro edge member; cases member⟩
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
      firstReads _ firstIH restIH inventory capturedDepth depth populated allowed ready resident safe valid known capturedDomains stored capturedCaps bounded
    have facts := ready.checked.semantic.ready.semantic.1.normal.facts
    have available := facts.cached.edges edge.entry.key edge (resident _ List.mem_cons_self)
    have childCaps : ∀ child ∈ edge.children, Cap Plain (depth - 1) child := by
      cases depth with
      | zero => exact fun child member => .plain 0 ((bounded _ List.mem_cons_self).2 child member)
      | succ depth => exact bounded _ List.mem_cons_self
    have related := firstIH inventory capturedDepth (depth - 1) populated allowed ready available (safe _ List.mem_cons_self)
      valid known capturedDomains stored capturedCaps childCaps
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
    have resultCap := SourceCurrentConstrainedCap.makeEdge Plain
      (outputDepth capturedDepth depth (.editBelow entries)) edge.entry.key.symbol edge.entry.key.constraint values
      middle.checked.native.machine.heap currentFacts.coherent currentFacts.cached checked.available
      (by intro zero; unfold outputDepth at zero; simp only [Edits.editBelow.sizeOf_spec] at zero; omega)
      (fun child member => (related.2 child member).mono (by
        unfold childrenDepth outputDepth
        simp only [Edits.editBelow.sizeOf_spec]
        omega))
    have edgeStore : Stored record originals (advanceHeap middle heap) := by
      have emitted := SourceCurrentConstrainedCapMixedEditStoreEffects.edge checked.ready edge.entry.key.symbol edge.entry.key.constraint values field checked.available related.1
      simpa only [rebuilt] using emitted.1
    have currentValid := SourceQueryUnfoldMemo.valid_grows _ _ checked.ready.checked.semantic edgeKeeps current checked.globals.valid
    have later := restIH middleInventory capturedDepth depth populated allowed edgeReady
      (fun original member => InternedEdgeResidency.edge_grows _ _ (checked.effects.keeps.trans edgeKeeps).growth original
        (resident original (List.mem_cons_of_mem _ member)))
      (fun original member => safe original (List.mem_cons_of_mem _ member)) currentValid known capturedDomains edgeStore capturedCaps
      (fun original member => bounded original (List.mem_cons_of_mem _ member))
    refine ⟨later.1, ?_⟩
    intro output member
    rcases List.mem_cons.mp member with rfl | remaining
    · simpa only [rebuilt] using resultCap
    · exact later.2 output remaining
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


/-- Actual node reads derive the syntax bound and retain all mixed stores at the same return. -/
theorem node {record originals edits value before result after memos final}
    {actual : EditNode (width := width) record originals edits value before result after}
    (reads : NodeReads formulas solver base actual memos final)
    (inventory : Inventory) (capturedDepth inputDepth : Nat)
    (populated : Populated edits) (nonempty : HasLeaf edits) (allowed : Allowed record edits)
    (ready : Ready formulas solver inventory record originals base before)
    (available : Available before.checked.native.machine.heap value) (safe : Safe edits value)
    (valid : Valid before.checked.native.machine.heap memos) (known : Values base originals)
    (capturedDomains : ∀ path ∈ record.paths, Domain (path.map Int.ofNat) originals)
    (stored : Stored record originals before) (capturedCaps : ∀ original ∈ originals, Cap Plain capturedDepth original)
    (inputCap : Cap Plain inputDepth value) :
    Stored record originals after ∧ Cap Plain (outputDepth capturedDepth inputDepth edits) result :=
  all_reads.1 reads inventory capturedDepth inputDepth populated nonempty allowed ready available safe valid
    known capturedDomains stored capturedCaps inputCap

/-- Ordered signed child reads retain every current original input and its computed cap budget. -/
theorem children {record originals entries offset values before results after memos final}
    {actual : EditChildren (width := width) record originals entries offset values before results after}
    (reads : ChildrenReads formulas solver base actual memos final)
    (inventory : Inventory) (capturedDepth inputDepth : Nat)
    (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : Ready formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap values) (safe : ChildrenSafe entries offset values)
    (valid : Valid before.checked.native.machine.heap memos) (known : Values base originals)
    (capturedDomains : ∀ path ∈ record.paths, Domain (path.map Int.ofNat) originals)
    (stored : Stored record originals before) (capturedCaps : ∀ original ∈ originals, Cap Plain capturedDepth original)
    (inputCaps : ∀ value ∈ values, Cap Plain inputDepth value) :
    Stored record originals after ∧ ∀ value ∈ results, Cap Plain (childrenDepth capturedDepth inputDepth entries) value :=
  all_reads.2.1 reads inventory capturedDepth inputDepth populated allowed ready available safe valid
    known capturedDomains stored capturedCaps inputCaps

/-- Actual row reconstruction uses the original full guard and the positional child result cap. -/
theorem rows {record originals entries edges before results after memos final}
    {actual : EditRows (width := width) record originals entries edges before results after}
    (reads : RowsReads formulas solver base actual memos final)
    (inventory : Inventory) (capturedDepth inputDepth : Nat)
    (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : Ready formulas solver inventory record originals base before)
    (resident : Edges before.checked.native.machine.heap edges) (safe : RowsSafe entries edges)
    (valid : Valid before.checked.native.machine.heap memos) (known : Values base originals)
    (capturedDomains : ∀ path ∈ record.paths, Domain (path.map Int.ofNat) originals)
    (stored : Stored record originals before) (capturedCaps : ∀ original ∈ originals, Cap Plain capturedDepth original)
    (inputCaps : ∀ edge ∈ edges, EdgeCap Plain inputDepth edge) :
    Stored record originals after ∧ ∀ edge ∈ results, EdgeCap Plain (outputDepth capturedDepth inputDepth (.editBelow entries)) edge :=
  all_reads.2.2 reads inventory capturedDepth inputDepth populated allowed ready resident safe valid
    known capturedDomains stored capturedCaps inputCaps

/-- Whole supplied forest reads derive their leaf caps without hereditary placement or future callbacks. -/
theorem list {record originals edits values before results after memos final}
    {actual : EditList (width := width) record originals edits values before results after}
    (reads : ListReads formulas solver base actual memos final)
    (inventory : Inventory) (capturedDepth inputDepth : Nat) (populated : Populated edits) (allowed : Allowed record edits)
    (ready : Ready formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap values)
    (safe : SourceCurrentAllocatedSharedEditEffects.ListSafe edits values)
    (valid : Valid before.checked.native.machine.heap memos) (known : Values base originals)
    (capturedDomains : ∀ path ∈ record.paths, Domain (path.map Int.ofNat) originals)
    (stored : Stored record originals before) (capturedCaps : ∀ original ∈ originals, Cap Plain capturedDepth original)
    (inputCaps : ∀ value ∈ values, Cap Plain inputDepth value) :
    Stored record originals after ∧ ∀ value ∈ results, Cap Plain (outputDepth capturedDepth inputDepth edits) value := by
  cases reads with
  | leaf =>
      exact ⟨stored, fun value member => (inputCaps value member).mono (by unfold outputDepth; omega)⟩
  | children reads =>
      have bounded := children reads inventory capturedDepth inputDepth populated allowed ready available safe valid
        known capturedDomains stored capturedCaps inputCaps
      exact ⟨bounded.1, fun value member => (bounded.2 value member).mono (by
        unfold childrenDepth outputDepth
        simp only [Edits.editBelow.sizeOf_spec]
        omega)⟩

end MicroCFTA.SourceCurrentConstrainedCapMixedEdit
