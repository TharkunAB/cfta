import MicroCFTA.SourceCurrentClassStructuralOrigins

/-!
# Structural row sources through actual class folds

Each output occurrence retains an occurrence in the initial fold forest,
or an actual native or Head event in a chronological class phase. The
event retains its residual structural occurrence and exact child slices.
These sources do not assert an observational origin or a decreasing rank.
-/
namespace MicroCFTA.SourceCurrentClassFoldStructuralOrigins
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityEdits SourceEqualityEditLeafPaths SourceCurrentEditDomains
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentAllocatedSharedEditGraph SourceCurrentAllocatedSharedEditEffects
open SourceCurrentNativeEdgeWriterGrowth (History)
open SourceCurrentRequiredRowOrigins (RowAt Position)
open SourceCurrentRequiredGuardOrigins (RowOrigin)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Inventory" => SourceCurrentAllocatedNativeInventoryState.Inventory
local notation "SharedReady" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "ChildEvent" => SourceCurrentClassStructuralOrigins.ChildEvent
local notation "Class" => SourceCurrentAllocatedClassEdits.Class
local notation "ClassReads" => SourceCurrentAllocatedClassEdits.ClassReads
local notation "Fold" => SourceCurrentAllocatedClassPass.Fold
local notation "FoldReads" => SourceCurrentAllocatedClassPass.FoldReads

private def Source (value : Node) (row : Edge) : Prop :=
  ∃ path index original, RowAt value path index original ∧ RowOrigin original row

private theorem row_trans {first middle last : Edge}
    (earlier : RowOrigin first middle) (later : RowOrigin middle last) : RowOrigin first last :=
  ⟨later.1.trans earlier.1,later.2.1.trans earlier.2.1,later.2.2.trans earlier.2.2⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- A forest event retains its exact ordered child execution slice. -/
inductive ListEvent (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (base : Heap) :
    {record : Record} → {originals : List Node} → {edits : Edits EqualityNormalize.Path} →
    {inputs : List Node} → {before : SharedState width} → {results : List Node} → {after : SharedState width} →
    EditList record originals edits inputs before results after → Nat → Node → Prop where
  /-- A below edit retains the actual indexed forest child and its event. -/
  | children {record originals entries inputs before results after index event child memos final}
      {actual : EditChildren record originals entries 0 inputs before results after}
      (read : ChildrenReads formulas solver base actual memos final)
      (selected : results[index]? = some child)
      (slice : SourceCurrentSharedEditChildLineage.Slice formulas solver base record originals entries 0
        inputs before results after memos final index child)
      (source : ChildEvent formulas solver base actual index event) :
      ListEvent formulas solver base (.children actual) index event

/-- A class event retains the literal compiled edit and its captured forest. -/
inductive ClassEvent (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    {record : Record} → {inputs : List Node} → {before : Checked width} → {memo : Memo} →
    {results : List Node} → {after : Checked width} → {saved : Memo} →
    Class record inputs before memo results after saved → Nat → Node → Prop where
  /-- The actual class uses this list event at its original base heap. -/
  | edit {record inputs before memo results shared index event}
      {actual : EditList record inputs (SourceCurrentAllocatedClassEditPlan.compiled record) inputs
        (SourceCurrentAllocatedSharedTargetState.initial before memo) results shared}
      (source : ListEvent formulas solver before.native.machine.heap actual index event) :
      ClassEvent formulas solver (.edit actual) index event

/-- An event retains its actual class occurrence in the chronological right fold. -/
inductive FoldEvent (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    {records : List Record} → {inputs : List Node} → {before : Checked width} → {memo : Memo} →
    {results : List Node} → {after : Checked width} → {saved : Memo} →
    Fold records inputs before memo results after saved → Nat → Node → Prop where
  /-- The current class follows the exact completed tail and its native history. -/
  | head {records inputs before memo middle next current record results after saved index event memos phaseMemos final}
      {tail : Fold records inputs before memo middle next current}
      {head : Class record middle next current results after saved}
      (tailReads : FoldReads formulas solver tail memos phaseMemos)
      (headReads : ClassReads formulas solver head phaseMemos final)
      (history : History next) (source : ClassEvent formulas solver head index event) :
      FoldEvent formulas solver (.cons tail head) index event
  /-- A later actual class retains an earlier event's row fields. -/
  | tail {records inputs before memo middle next current record results after saved index event phaseMemos final}
      {tail : Fold records inputs before memo middle next current}
      {head : Class record middle next current results after saved}
      (headReads : ClassReads formulas solver head phaseMemos final)
      (source : FoldEvent formulas solver tail index event) :
      FoldEvent formulas solver (.cons tail head) index event

private def ChildrenLaw (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (base : Heap)
    {record originals entries offset inputs before results after}
    (actual : EditChildren (width := width) record originals entries offset inputs before results after) (memos : Memos) : Prop :=
  ∀ inventory, Populated (.editBelow entries) → Allowed record (.editBelow entries) →
    SharedReady formulas solver inventory record originals base before → Values before.checked.native.machine.heap inputs →
    ChildrenSafe entries offset inputs → EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos → History before.checked →
    ∀ childIndex child, results[childIndex]? = some child → ∀ path index row, RowAt child path index row →
    ∃ original, inputs[childIndex]? = some original ∧
      (Source original row ∨ ∃ event suffix sourceIndex source, ChildEvent formulas solver base actual childIndex event ∧
        RowAt event suffix sourceIndex source ∧ RowOrigin source row)

set_option maxHeartbeats 1600000 in
private theorem children_law {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {base : Heap}
    {record originals entries offset inputs before results after memos final}
    {actual : EditChildren (width := width) record originals entries offset inputs before results after}
    (reads : ChildrenReads formulas solver base actual memos final) : ChildrenLaw formulas solver base actual memos := by
  refine ChildrenReads.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun {record originals entries offset inputs before results after} actual memos _ _ =>
      ChildrenLaw formulas solver base actual memos)
    (motive_3 := fun _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ reads
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intro record originals entries offset state memos inventory populated allowed ready available safe valid history childIndex child selected path index row occurrence
    simp at selected
  · intro record originals memos saved entries values before results after original offset absent rest read ih
      inventory populated allowed ready available safe valid history childIndex child selected path index row occurrence
    cases childIndex with
    | zero =>
      have same : original = child := by simpa using selected
      subst child
      exact ⟨original,rfl,.inl ⟨path,index,row,occurrence,rfl,rfl,rfl⟩⟩
    | succ childIndex =>
      obtain ⟨original,present,origin⟩ := ih inventory populated allowed ready
        (fun value member => available value (List.mem_cons_of_mem _ member)) (children_tail safe) valid history
        childIndex child (by simpa using selected) path index row occurrence
      refine ⟨original,by simpa using present,?_⟩
      rcases origin with source | event
      · exact .inl source
      · obtain ⟨event,suffix,sourceIndex,source,eventAt,sourceAt,fields⟩ := event
        exact .inr ⟨event,suffix,sourceIndex,source,.unselected (absent := absent) eventAt,sourceAt,fields⟩
  · intro record originals memos current saved entries edits original before result middle values results after offset found first rest firstRead restRead firstIH ih
      inventory populated allowed ready available safe valid history childIndex child selected path index row occurrence
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
      have origin := SourceCurrentClassStructuralOrigins.node firstRead inventory support.1 support.2 childAllowed ready
        (available _ List.mem_cons_self) childSafe valid history occurrence
      refine ⟨original,rfl,?_⟩
      rcases origin with source | event
      · exact .inl source
      · obtain ⟨event,suffix,sourceIndex,source,eventAt,sourceAt,fields⟩ := event
        exact .inr ⟨event,suffix,sourceIndex,source,.here (rest := rest) (found := found) eventAt,sourceAt,fields⟩
    | succ childIndex =>
      obtain ⟨next,receipt⟩ := node_effects firstRead support.1 support.2 childAllowed ready
        (available _ List.mem_cons_self) childSafe valid
      have oneRead : ChildrenReads formulas solver base
          (EditChildren.selected offset found first EditChildren.nil) memos current :=
        .selected (found := found) firstRead .nil
      have nextHistory := (SourceCurrentParentNativeHistory.edit_children oneRead history
        ready.checked.semantic.ready.semantic.1.normal.facts.coherent.valid).1
      obtain ⟨original,present,origin⟩ := ih next populated allowed receipt.ready
        (fun value member => receipt.effects.keeps.available value (available value (List.mem_cons_of_mem _ member)))
        (children_tail safe) receipt.globals.valid nextHistory childIndex child (by simpa using selected) path index row occurrence
      refine ⟨original,by simpa using present,?_⟩
      rcases origin with source | event
      · exact .inl source
      · obtain ⟨event,suffix,sourceIndex,source,eventAt,sourceAt,fields⟩ := event
        exact .inr ⟨event,suffix,sourceIndex,source,.selected (first := first) (found := found) eventAt,sourceAt,fields⟩
  · intros; trivial
  · intros; trivial

/-- Actual forest child scans retain a structural source at the same forest index. -/
theorem children {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {base : Heap}
    {record originals entries offset inputs before results after memos final}
    {actual : EditChildren (width := width) record originals entries offset inputs before results after}
    (reads : ChildrenReads formulas solver base actual memos final)
    (inventory : Inventory) (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : SharedReady formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap inputs) (safe : ChildrenSafe entries offset inputs)
    (valid : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos) (history : History before.checked)
    (forestIndex : Nat) (value : Node) (selected : results[forestIndex]? = some value)
    {positions rowIndex row} (occurrence : RowAt value positions rowIndex row) :
    ∃ original, inputs[forestIndex]? = some original ∧
      ((∃ sourcePath sourceIndex source, RowAt original sourcePath sourceIndex source ∧ RowOrigin source row) ∨
        ∃ event suffix sourceIndex source, ChildEvent formulas solver base actual forestIndex event ∧
          RowAt event suffix sourceIndex source ∧ RowOrigin source row) :=
  children_law reads inventory populated allowed ready available safe valid history forestIndex value selected positions rowIndex row occurrence

/-- Actual list dispatch retains the exact indexed source or native/Head event. -/
theorem list {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {base : Heap}
    {record originals edits inputs before results after memos final}
    {actual : EditList (width := width) record originals edits inputs before results after}
    (reads : ListReads formulas solver base actual memos final)
    (inventory : Inventory) (populated : Populated edits) (allowed : Allowed record edits)
    (ready : SharedReady formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap inputs) (safe : ListSafe edits inputs)
    (valid : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos) (history : History before.checked)
    (forestIndex : Nat) (value : Node) (selected : results[forestIndex]? = some value)
    {positions rowIndex row} (occurrence : RowAt value positions rowIndex row) :
    ∃ original, inputs[forestIndex]? = some original ∧
      ((∃ sourcePath sourceIndex source, RowAt original sourcePath sourceIndex source ∧ RowOrigin source row) ∨
        ∃ event suffix sourceIndex source, ListEvent formulas solver base actual forestIndex event ∧
          RowAt event suffix sourceIndex source ∧ RowOrigin source row) := by
  cases reads with
  | leaf => exact ⟨value,selected,.inl ⟨positions,rowIndex,row,occurrence,rfl,rfl,rfl⟩⟩
  | children read =>
    obtain ⟨original,present,origin⟩ := children read inventory populated allowed ready available safe valid history
      forestIndex value selected occurrence
    refine ⟨original,present,?_⟩
    rcases origin with source | event
    · exact .inl source
    · obtain ⟨event,suffix,sourceIndex,source,eventAt,sourceAt,fields⟩ := event
      exact .inr ⟨event,suffix,sourceIndex,source,
        .children read selected (SourceCurrentSharedEditChildLineage.indexed read selected) eventAt,sourceAt,fields⟩

/-- A literal compiled class derives structural sources from its captured input forest. -/
theorem class_sources {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {record inputs before memo results after saved memos final}
    {actual : SourceCurrentAllocatedClassEdits.Class (width := width) record inputs before memo results after saved}
    (reads : ClassReads formulas solver actual memos final)
    (inventory : Inventory) (coherent : SourceEqualityClassOrder.Coherent record)
    (active : EqualityNormalize.Nontrivial record.paths) (ready : SourceCurrentConjunctionClassScan.Ready before)
    (admitted : SourceCurrentAllocatedNativeInventoryState.At formulas solver inventory before)
    (available : Values before.native.machine.heap inputs)
    (domains : ∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) inputs)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) (history : History before)
    (forestIndex : Nat) (value : Node) (selected : results[forestIndex]? = some value)
    {positions rowIndex row} (occurrence : RowAt value positions rowIndex row) :
    ∃ original, inputs[forestIndex]? = some original ∧
      ((∃ sourcePath sourceIndex source, RowAt original sourcePath sourceIndex source ∧ RowOrigin source row) ∨
        ∃ event suffix sourceIndex source, ClassEvent formulas solver actual forestIndex event ∧
          RowAt event suffix sourceIndex source ∧ RowOrigin source row) := by
  cases reads with
  | edit lower =>
    have initialReady := SourceCurrentAllocatedSharedTargetState.initial_ready formulas solver inventory record inputs
      before.native.machine.heap before memo ready admitted (SourceEqualityRequiredCache.pure_keeps _ ready.semantic.ready) stored covered
    have safe : ListSafe (SourceCurrentAllocatedClassEditPlan.compiled record) inputs := by
      obtain ⟨entries,built⟩ := SourceCurrentAllocatedClassEditPlan.compiled_children record coherent active
      rw [built]
      exact SourceCurrentAllocatedClassEditPlan.compiled_safe record coherent inputs domains entries built
    obtain ⟨original,present,origin⟩ := list lower inventory
      (SourceCurrentAllocatedClassEditPlan.compiled_populated record) (SourceCurrentAllocatedClassEditPlan.compiled_allowed record)
      initialReady available safe valid history forestIndex value selected occurrence
    refine ⟨original,present,?_⟩
    rcases origin with source | event
    · exact .inl source
    · obtain ⟨event,suffix,sourceIndex,source,eventAt,sourceAt,fields⟩ := event
      exact .inr ⟨event,suffix,sourceIndex,source,.edit eventAt,sourceAt,fields⟩

/-- The actual right fold retains an initial structural source or a concrete earlier class event. -/
theorem fold {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {records inputs before memo results after saved memos final}
    {actual : SourceCurrentAllocatedClassPass.Fold (width := width) records inputs before memo results after saved}
    (reads : FoldReads formulas solver actual memos final)
    (inventory : Inventory)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : SourceCurrentConjunctionClassScan.Ready before)
    (admitted : SourceCurrentAllocatedNativeInventoryState.At formulas solver inventory before)
    (available : Values before.native.machine.heap inputs)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) inputs)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) (history : History before)
    (forestIndex : Nat) (value : Node) (selected : results[forestIndex]? = some value)
    {positions rowIndex row} (occurrence : RowAt value positions rowIndex row) :
    (∃ original, inputs[forestIndex]? = some original ∧
      ∃ sourcePath sourceIndex source, RowAt original sourcePath sourceIndex source ∧ RowOrigin source row) ∨
      ∃ event suffix sourceIndex source, FoldEvent formulas solver actual forestIndex event ∧
        RowAt event suffix sourceIndex source ∧ RowOrigin source row := by
  induction reads generalizing inventory forestIndex value positions rowIndex row with
  | nil => exact .inl ⟨value,selected,positions,rowIndex,row,occurrence,rfl,rfl,rfl⟩
  | @cons records inputs before memo middle step current record results after saved memos phaseMemos final
      tail head tailReads headReads ih =>
    have tailCoherent := fun own member => coherent own (List.mem_cons_of_mem record member)
    have tailActive := fun own member => active own (List.mem_cons_of_mem record member)
    have tailDomains := fun own member => domains own (List.mem_cons_of_mem record member)
    obtain ⟨phaseInventory,receipt⟩ := SourceCurrentAllocatedClassPass.Fold.verified formulas solver inventory tailReads
      tailCoherent tailActive ready admitted available tailDomains stored covered valid
    have phaseHistory := SourceCurrentParentNativeHistory.class_pass
      (SourceCurrentAllocatedClassPass.PassReads.done tailReads) history ready
    obtain ⟨phaseInput,phaseSelected,origin⟩ := class_sources headReads phaseInventory
      (coherent record List.mem_cons_self) (active record List.mem_cons_self) receipt.ready receipt.admitted receipt.available
      (fun path member => receipt.domains _ (domains record List.mem_cons_self path member))
      receipt.stored receipt.covered receipt.globals.valid phaseHistory forestIndex value selected occurrence
    rcases origin with source | event
    · obtain ⟨phasePath,phaseIndex,phaseRow,phaseAt,laterFields⟩ := source
      have earlier := ih inventory tailCoherent tailActive ready admitted available tailDomains stored covered valid history
        forestIndex phaseInput phaseSelected phaseAt
      rcases earlier with source | event
      · obtain ⟨original,present,path,index,row,sourceAt,earlierFields⟩ := source
        exact .inl ⟨original,present,path,index,row,sourceAt,row_trans earlierFields laterFields⟩
      · obtain ⟨event,suffix,index,row,eventAt,sourceAt,earlierFields⟩ := event
        exact .inr ⟨event,suffix,index,row,.tail headReads eventAt,sourceAt,row_trans earlierFields laterFields⟩
    · obtain ⟨event,suffix,index,row,eventAt,sourceAt,fields⟩ := event
      exact .inr ⟨event,suffix,index,row,.head tailReads headReads phaseHistory eventAt,sourceAt,fields⟩

end MicroCFTA.SourceCurrentClassFoldStructuralOrigins
