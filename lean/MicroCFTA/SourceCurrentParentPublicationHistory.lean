import MicroCFTA.SourceCurrentRequiredPublicationHistory
import MicroCFTA.SourceCurrentMergePublicationHistory
import MicroCFTA.SourceCurrentClassEventExecutions
import MicroCFTA.SourceCurrentNativePublicationTrace

/-!
# Actual physical publication histories through class edits

Each actual physical operation supplies its own publication history.
Native traces extend those histories at their exact checked states.
Heap growth alone supplies no publication history.
-/
namespace MicroCFTA.SourceCurrentParentPublicationHistory
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceEqualityEdits SourceEqualityEditLeafPaths SourceCurrentEditDomains
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentAllocatedSharedEditGraph SourceCurrentAllocatedSharedEditEffects
open SourceCurrentNativeMuPublication (History)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => State Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Inventory" => SourceCurrentAllocatedNativeInventoryState.Inventory
local notation "SharedReady" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "ClassReady" => SourceCurrentConjunctionClassScan.Ready
local notation "Stored" => SourceCurrentMemoMergeEffects.Stored
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- Actual projection and merge supply the complete operand publication interval. -/
theorem operand {formulas solver inventory path values before memo value after saved memos final}
    (receipt : SourceCurrentAllocatedMergeOperand.Receipt (width := width) formulas solver inventory
      path values before memo value after saved memos final)
    (ready : ClassReady before) (available : Values before.native.machine.heap values)
    (stored : Stored before.native.machine.heap memo) :
    Nonempty (History before.native.machine.heap after.native.machine.heap) := by
  obtain ⟨projected,middle,current,projection,merged⟩ := receipt.actual
  obtain ⟨first⟩ := SourceCurrentRequiredPublicationHistory.forest projection.graph ready.semantic ready.costs available
  obtain ⟨last⟩ := SourceCurrentMergePublicationHistory.merge merged projection.ready.semantic projection.ready.costs
    (stored.grows projection.effects.keeps) projection.available
  exact ⟨.trans first last⟩

private theorem target_fold {formulas solver values seed paths before memo value after saved memos final}
    {actual : SourceCurrentAllocatedTargetGraph.Fold (width := width) values seed paths before memo value after saved}
    (reads : SourceCurrentAllocatedTargetComplete.FoldReads formulas solver actual memos final) :
    ClassReady before → Values before.native.machine.heap values → Stored before.native.machine.heap memo →
      Nonempty (History before.native.machine.heap after.native.machine.heap) ∧ ClassReady after := by
  induction reads with
  | nil receipt => exact fun ready available stored => ⟨operand receipt ready available stored,receipt.ready⟩
  | @cons values seed path paths before middle later after memo current saved head tail result
      memos nextMemos lastMemos inventory nextInventory first rest step receipt remaining query ih =>
    intro ready available stored
    obtain ⟨headHistory⟩ := operand receipt ready available stored
    obtain ⟨⟨tailHistory⟩,tailReady⟩ := ih receipt.ready
      (fun value member => receipt.effects.keeps.available value (available value member)) receipt.stored
    cases step with
    | run trace =>
      obtain ⟨_,⟨queryHistory⟩⟩ := SourceCurrentNativePublicationTrace.trace trace tailReady.semantic.ready.semantic
      exact ⟨⟨.trans headHistory (.trans tailHistory queryHistory)⟩,query.ready⟩

/-- Actual target reads retain projection, merge and native-query publication intervals. -/
theorem target {formulas solver values paths before memo value after saved memos final}
    {actual : SourceCurrentAllocatedTargetGraph.Target (width := width) values paths before memo value after saved}
    (reads : SourceCurrentAllocatedTargetComplete.TargetReads formulas solver actual memos final)
    (ready : ClassReady before) (available : Values before.native.machine.heap values)
    (stored : Stored before.native.machine.heap memo) :
    Nonempty (History before.native.machine.heap after.native.machine.heap) := by
  cases reads with
  | nil => exact ⟨.refl _⟩
  | cons reads => exact (target_fold reads ready available stored).1

/-- A target-slot hit keeps its heap; a miss retains its actual completed target history. -/
theorem force {formulas solver inventory record originals base path before value after memos final}
    (receipt : SourceCurrentAllocatedSharedTargetForce.Receipt (width := width) formulas solver inventory
      record originals base path before value after memos final)
    (ready : ClassReady before.checked) (available : Values before.checked.native.machine.heap originals)
    (stored : Stored before.checked.native.machine.heap before.memo) :
    Nonempty (History before.checked.native.machine.heap after.checked.native.machine.heap) := by
  cases receipt.reads with
  | hit => exact ⟨.refl _⟩
  | miss absent reads =>
    exact target reads ready available stored

/-- Actual target forcing and its following native query supply the complete leaf history. -/
theorem leaf {formulas solver inventory record originals base path input before value after memos final}
    (receipt : SourceCurrentAllocatedSharedTargetLeaf.Receipt (width := width) formulas solver inventory
      record originals base path input before value after memos final)
    (ready : ClassReady before.checked) (available : Values before.checked.native.machine.heap originals)
    (stored : Stored before.checked.native.machine.heap before.memo) :
    Nonempty (History before.checked.native.machine.heap after.checked.native.machine.heap) := by
  cases receipt.reads with
  | apply first query =>
    obtain ⟨firstHistory⟩ := force first ready available stored
    cases query.actual with
    | run trace =>
      obtain ⟨_,⟨lastHistory⟩⟩ := SourceCurrentNativePublicationTrace.trace trace first.ready.checked.semantic.ready.semantic
      exact ⟨.trans firstHistory lastHistory⟩

private def NodeLaw (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (base : Heap)
    {record originals edits input before result after}
    (_actual : EditNode (width := width) record originals edits input before result after) (memos : Memos) : Prop :=
  Values base originals → ∀ inventory, Populated edits → HasLeaf edits → Allowed record edits →
    SharedReady formulas solver inventory record originals base before → Available before.checked.native.machine.heap input →
    Safe edits input → EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos →
    Nonempty (History before.checked.native.machine.heap after.checked.native.machine.heap)

private def ChildrenLaw (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (base : Heap)
    {record originals entries offset inputs before results after}
    (_actual : EditChildren (width := width) record originals entries offset inputs before results after) (memos : Memos) : Prop :=
  Values base originals → ∀ inventory, Populated (.editBelow entries) → Allowed record (.editBelow entries) →
    SharedReady formulas solver inventory record originals base before → Values before.checked.native.machine.heap inputs →
    ChildrenSafe entries offset inputs → EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos →
    Nonempty (History before.checked.native.machine.heap after.checked.native.machine.heap)

private def RowsLaw (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (base : Heap)
    {record originals entries inputs before results after}
    (_actual : EditRows (width := width) record originals entries inputs before results after) (memos : Memos) : Prop :=
  Values base originals → ∀ inventory, Populated (.editBelow entries) → Allowed record (.editBelow entries) →
    SharedReady formulas solver inventory record originals base before → Edges before.checked.native.machine.heap inputs →
    RowsSafe entries inputs → EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos →
    Nonempty (History before.checked.native.machine.heap after.checked.native.machine.heap)

set_option maxHeartbeats 2400000 in
private theorem node_law {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {base : Heap}
    {record originals edits input before result after memos final}
    {actual : EditNode (width := width) record originals edits input before result after}
    (reads : NodeReads formulas solver base actual memos final) : NodeLaw formulas solver base actual memos := by
  refine NodeReads.rec
    (motive_1 := fun {record originals edits input before result after} actual memos _ _ => NodeLaw formulas solver base actual memos)
    (motive_2 := fun {record originals entries offset inputs before results after} actual memos _ _ => ChildrenLaw formulas solver base actual memos)
    (motive_3 := fun {record originals entries inputs before results after} actual memos _ _ => RowsLaw formulas solver base actual memos)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ reads
  · intro next record originals path input before result after memos saved receipt originalValues
      inventory populated nonempty allowed ready available safe valid
    exact leaf receipt ready.checked
      (fun value member => ready.captured.available value (originalValues value member)) ready.stored
  · intros
    dsimp only [NodeLaw]
    intros
    exact ⟨.refl _⟩
  · intro record originals memos saved entries edges before rebuilt middle value heap entry depth free actual built read ih
      originalValues inventory populated nonempty allowed ready available safe valid
    have facts := ready.checked.semantic.ready.semantic.1.normal.facts
    have resident := resident_edges _ facts.linked _ available.resident
    obtain ⟨first⟩ := ih originalValues inventory populated allowed ready resident (ordinary_rows safe) valid
    have last : History middle.checked.native.machine.heap heap := by
      have actual := InternedShallowHeap.makeNode_noNewMu rebuilt middle.checked.native.machine.heap
      rw [built] at actual
      exact .retain _ _ actual
    exact ⟨.trans first last⟩
  · intro record originals memos current saved entries original before exposed heap value after recursive head body
      headRead headGlobal bodyRead ih originalValues inventory populated nonempty allowed ready available safe valid
    have closed := recursive_closed recursive nonempty safe
    have first := head_physical ready head available
    have checked := head.verified ready.checked.semantic.ready available closed
    obtain ⟨headHistory⟩ := SourceCurrentRequiredPublicationHistory.head head
      ready.checked.semantic ready.checked.costs available
    obtain ⟨bodyHistory⟩ := ih originalValues inventory populated nonempty allowed first.1 first.2.2
      (closed_safe _ exposed heap first.1.checked.semantic first.2.2 checked.2.2.1) headGlobal.valid
    exact ⟨.trans headHistory bodyHistory⟩
  · intros
    dsimp only [ChildrenLaw]
    intros
    exact ⟨.refl _⟩
  · intro record originals memos saved entries values before results after original offset absent rest read ih
      originalValues inventory populated allowed ready available safe valid
    exact ih originalValues inventory populated allowed ready
      (fun value member => available value (List.mem_cons_of_mem _ member)) (children_tail safe) valid
  · intro record originals memos current saved entries edits original before result middle values results after offset found first rest
      firstRead restRead firstIH restIH originalValues inventory populated allowed ready available safe valid
    have member := SourceEqualityNeededMap.lookup_mem _ _ _ found
    have support := (show ∀ index child, (index,child) ∈ entries → Populated child ∧ HasLeaf child from
      by simpa only [Populated] using populated) _ _ member
    have childAllowed : Allowed record edits := by
      rw [Allowed,All] at allowed
      exact allowed _ _ member
    have childSafe := safe 0 _ (by simpa using found) original rfl
    obtain ⟨next,receipt⟩ := node_effects firstRead support.1 support.2 childAllowed ready
      (available _ List.mem_cons_self) childSafe valid
    obtain ⟨firstHistory⟩ := firstIH originalValues inventory support.1 support.2 childAllowed ready
      (available _ List.mem_cons_self) childSafe valid
    obtain ⟨restHistory⟩ := restIH originalValues next populated allowed receipt.ready
      (fun value member => receipt.effects.keeps.available value (available value (List.mem_cons_of_mem _ member)))
      (children_tail safe) receipt.globals.valid
    exact ⟨.trans firstHistory restHistory⟩
  · intros
    dsimp only [RowsLaw]
    intros
    exact ⟨.refl _⟩
  · intro record originals memos current saved entries before values middle result heap edges results after edge children built rest
      firstRead restRead firstIH restIH originalValues inventory populated allowed ready resident safe valid
    have facts := ready.checked.semantic.ready.semantic.1.normal.facts
    have childAvailable := facts.cached.edges edge.entry.key edge (resident _ List.mem_cons_self)
    have oneRead : RowsReads formulas solver base (EditRows.cons children built EditRows.nil) memos current :=
      .cons (rebuilt := built) firstRead .nil
    obtain ⟨next,receipt⟩ := rows_effects oneRead populated allowed ready
      (fun row member => resident row (List.mem_cons.mpr (.inl (by simpa using member))))
      (fun row member => safe row (List.mem_cons.mpr (.inl (by simpa using member)))) valid
    obtain ⟨firstHistory⟩ := firstIH originalValues inventory populated allowed ready childAvailable (safe _ List.mem_cons_self) valid
    have made : History middle.checked.native.machine.heap heap := by
      have same : heap.nodeRecords = middle.checked.native.machine.heap.nodeRecords := by
        have actual := congrArg Prod.snd built
        exact (congrArg State.nodeRecords actual).symm
      exact .retain _ _ (fun key entry body depth ordinary present => same ▸ present)
    obtain ⟨restHistory⟩ := restIH originalValues next populated allowed receipt.ready
      (fun row member => edge_grows _ _ receipt.effects.keeps.growth row (resident row (List.mem_cons_of_mem _ member)))
      (fun row member => safe row (List.mem_cons_of_mem _ member)) receipt.globals.valid
    exact ⟨.trans firstHistory (.trans made restHistory)⟩

/-- Actual supported node edits retain every physical publication interval. -/
theorem node {formulas solver base record originals edits input before result after memos final}
    {actual : EditNode (width := width) record originals edits input before result after}
    (reads : NodeReads formulas solver base actual memos final)
    (originalsAvailable : Values base originals) (inventory : Inventory)
    (populated : Populated edits) (nonempty : HasLeaf edits) (allowed : Allowed record edits)
    (ready : SharedReady formulas solver inventory record originals base before)
    (available : Available before.checked.native.machine.heap input) (safe : Safe edits input)
    (valid : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos) :
    Nonempty (History before.checked.native.machine.heap after.checked.native.machine.heap) :=
  node_law reads originalsAvailable inventory populated nonempty allowed ready available safe valid

/-- Actual ordered child edits compose publication intervals at their exact shared states. -/
theorem children {formulas solver base record originals entries offset inputs before results after memos final}
    {actual : EditChildren (width := width) record originals entries offset inputs before results after}
    (reads : ChildrenReads formulas solver base actual memos final)
    (originalsAvailable : Values base originals) (inventory : Inventory)
    (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : SharedReady formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap inputs) (safe : ChildrenSafe entries offset inputs)
    (valid : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos) :
    Nonempty (History before.checked.native.machine.heap after.checked.native.machine.heap) := by
  have law : ChildrenLaw formulas solver base actual memos := by
    refine ChildrenReads.rec
      (motive_1 := fun _ _ _ _ => True)
      (motive_2 := fun {record originals entries offset inputs before results after} actual memos _ _ =>
        ChildrenLaw formulas solver base actual memos)
      (motive_3 := fun _ _ _ _ => True)
      (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial)
      ?_ ?_ ?_ (by intros; trivial) (by intros; trivial) reads
    · intros
      dsimp only [ChildrenLaw]
      intros
      exact ⟨.refl _⟩
    · intro record originals memos saved entries values before results after original offset absent rest read ih
        originalValues inventory populated allowed ready available safe valid
      exact ih originalValues inventory populated allowed ready
        (fun value member => available value (List.mem_cons_of_mem _ member)) (children_tail safe) valid
    · intro record originals memos current saved entries edits original before result middle values results after offset found first rest
        firstRead restRead _ restIH originalValues inventory populated allowed ready available safe valid
      have member := SourceEqualityNeededMap.lookup_mem _ _ _ found
      have support := (show ∀ index child, (index,child) ∈ entries → Populated child ∧ HasLeaf child from
        by simpa only [Populated] using populated) _ _ member
      have childAllowed : Allowed record edits := by
        rw [Allowed,All] at allowed
        exact allowed _ _ member
      have childSafe := safe 0 _ (by simpa using found) original rfl
      obtain ⟨next,receipt⟩ := node_effects firstRead support.1 support.2 childAllowed ready
        (available _ List.mem_cons_self) childSafe valid
      obtain ⟨firstHistory⟩ := node firstRead originalValues inventory support.1 support.2 childAllowed ready
        (available _ List.mem_cons_self) childSafe valid
      obtain ⟨restHistory⟩ := restIH originalValues next populated allowed receipt.ready
        (fun value member => receipt.effects.keeps.available value (available value (List.mem_cons_of_mem _ member)))
        (children_tail safe) receipt.globals.valid
      exact ⟨.trans firstHistory restHistory⟩
  exact law originalsAvailable inventory populated allowed ready available safe valid

/-- Actual row edits retain child histories and literal raw edge-construction intervals. -/
theorem rows {formulas solver base record originals entries inputs before results after memos final}
    {actual : EditRows (width := width) record originals entries inputs before results after}
    (reads : RowsReads formulas solver base actual memos final)
    (originalsAvailable : Values base originals) (inventory : Inventory)
    (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : SharedReady formulas solver inventory record originals base before)
    (resident : Edges before.checked.native.machine.heap inputs) (safe : RowsSafe entries inputs)
    (valid : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos) :
    Nonempty (History before.checked.native.machine.heap after.checked.native.machine.heap) := by
  have law : RowsLaw formulas solver base actual memos := by
    refine RowsReads.rec
      (motive_1 := fun _ _ _ _ => True) (motive_2 := fun _ _ _ _ => True)
      (motive_3 := fun {record originals entries inputs before results after} actual memos _ _ =>
        RowsLaw formulas solver base actual memos)
      (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial)
      (by intros; trivial) (by intros; trivial) (by intros; trivial) ?_ ?_ reads
    · intros
      dsimp only [RowsLaw]
      intros
      exact ⟨.refl _⟩
    · intro record originals memos current saved entries before values middle result heap edges results after edge first built rest
        firstRead restRead _ restIH originalValues inventory populated allowed ready resident safe valid
      have facts := ready.checked.semantic.ready.semantic.1.normal.facts
      have childAvailable := facts.cached.edges edge.entry.key edge (resident _ List.mem_cons_self)
      have oneRead : RowsReads formulas solver base (EditRows.cons first built EditRows.nil) memos current :=
        .cons (rebuilt := built) firstRead .nil
      obtain ⟨next,receipt⟩ := rows_effects oneRead populated allowed ready
        (fun row member => resident row (List.mem_cons.mpr (.inl (by simpa using member))))
        (fun row member => safe row (List.mem_cons.mpr (.inl (by simpa using member)))) valid
      obtain ⟨firstHistory⟩ := children firstRead originalValues inventory populated allowed ready childAvailable
        (safe _ List.mem_cons_self) valid
      have made : History middle.checked.native.machine.heap heap := by
        have same : heap.nodeRecords = middle.checked.native.machine.heap.nodeRecords := by
          have actual := congrArg Prod.snd built
          exact (congrArg State.nodeRecords actual).symm
        exact .retain _ _ (fun key entry body depth ordinary present => same ▸ present)
      obtain ⟨restHistory⟩ := restIH originalValues next populated allowed receipt.ready
        (fun row member => edge_grows _ _ receipt.effects.keeps.growth row (resident row (List.mem_cons_of_mem _ member)))
        (fun row member => safe row (List.mem_cons_of_mem _ member)) receipt.globals.valid
      exact ⟨.trans firstHistory (.trans made restHistory)⟩
  exact law originalsAvailable inventory populated allowed ready resident safe valid

/-- Actual list edits retain the exact physical publication interval. -/
theorem list {formulas solver base record originals edits inputs before results after memos final}
    {actual : EditList (width := width) record originals edits inputs before results after}
    (reads : ListReads formulas solver base actual memos final)
    (originalsAvailable : Values base originals) (inventory : Inventory)
    (populated : Populated edits) (allowed : Allowed record edits)
    (ready : SharedReady formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap inputs) (safe : ListSafe edits inputs)
    (valid : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos) :
    Nonempty (History before.checked.native.machine.heap after.checked.native.machine.heap) := by
  cases reads with
  | leaf => exact ⟨.refl _⟩
  | children reads => exact children reads originalsAvailable inventory populated allowed ready available safe valid

end MicroCFTA.SourceCurrentParentPublicationHistory
