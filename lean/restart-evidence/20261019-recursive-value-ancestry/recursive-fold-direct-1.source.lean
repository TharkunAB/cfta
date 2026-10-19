import MicroCFTA.SourceCurrentClassRecursiveValueOrigins
import MicroCFTA.SourceCurrentClassFoldStructuralOrigins

/-!
# Exact recursive values through actual class folds

Each recursive output occurrence retains the same complete value in the
initial fold forest or an actual earlier native or Head event. The forest
slot remains fixed. The source arm retains the same child positions. Event paths remain explicit.
The proof does not descend through a Mu body or infer a decreasing rank.
-/
namespace MicroCFTA.SourceCurrentClassFoldRecursiveValueOrigins
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityEdits SourceEqualityEditLeafPaths SourceCurrentEditDomains
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentAllocatedSharedEditGraph SourceCurrentAllocatedSharedEditEffects
open SourceCurrentNativeEdgeWriterGrowth (History)
open SourceCurrentClassRecursiveValueOrigins (Occurs)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Inventory" => SourceCurrentAllocatedNativeInventoryState.Inventory
local notation "SharedReady" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "ChildEvent" => SourceCurrentClassStructuralOrigins.ChildEvent
local notation "ListEvent" => SourceCurrentClassFoldStructuralOrigins.ListEvent
local notation "ClassEvent" => SourceCurrentClassFoldStructuralOrigins.ClassEvent
local notation "FoldEvent" => SourceCurrentClassFoldStructuralOrigins.FoldEvent
local notation "ClassReads" => SourceCurrentAllocatedClassEdits.ClassReads
local notation "FoldReads" => SourceCurrentAllocatedClassPass.FoldReads

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

private def ChildrenLaw (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (base : Heap)
    {record originals entries offset inputs before results after}
    (actual : EditChildren (width := width) record originals entries offset inputs before results after) (memos : Memos) : Prop :=
  ∀ inventory, Populated (.editBelow entries) → Allowed record (.editBelow entries) →
    SharedReady formulas solver inventory record originals base before → Values before.checked.native.machine.heap inputs →
    ChildrenSafe entries offset inputs → EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos → History before.checked →
    ∀ forestIndex value, results[forestIndex]? = some value → ∀ positions needle,
      SourceEqualityRequiredGraph.Recursive needle → Occurs value positions needle →
      ∃ original, inputs[forestIndex]? = some original ∧
        (Occurs original positions needle ∨ ∃ event residual, ChildEvent formulas solver base actual forestIndex event ∧
          Occurs event residual needle)

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
  · intro record originals entries offset state memos inventory populated allowed ready available safe valid history
      forestIndex value selected positions needle recursive occurrence
    simp at selected
  · intro record originals memos saved entries values before results after original offset absent rest read ih
      inventory populated allowed ready available safe valid history forestIndex value selected positions needle recursive occurrence
    cases forestIndex with
    | zero =>
      have same : original = value := by simpa using selected
      subst value
      exact ⟨original,rfl,.inl occurrence⟩
    | succ forestIndex =>
      obtain ⟨original,present,origin⟩ := ih inventory populated allowed ready
        (fun value member => available value (List.mem_cons_of_mem _ member)) (children_tail safe) valid history
        forestIndex value (by simpa using selected) positions needle recursive occurrence
      refine ⟨original,by simpa using present,?_⟩
      rcases origin with source | event
      · exact .inl source
      · obtain ⟨event,residual,eventAt,sourceAt⟩ := event
        exact .inr ⟨event,residual,.unselected (absent := absent) eventAt,sourceAt⟩
  · intro record originals memos current saved entries edits original before result middle values results after offset found first rest firstRead restRead firstIH ih
      inventory populated allowed ready available safe valid history forestIndex value selected positions needle recursive occurrence
    have present := SourceEqualityNeededMap.lookup_mem _ _ _ found
    have support := (show ∀ index child, (index,child) ∈ entries → Populated child ∧ HasLeaf child from
      by simpa only [Populated] using populated) _ _ present
    have childAllowed : Allowed record edits := by
      rw [Allowed,All] at allowed
      exact allowed _ _ present
    have childSafe : Safe edits original := safe 0 _ (by simpa using found) original rfl
    cases forestIndex with
    | zero =>
      have same : result = value := by simpa using selected
      subst value
      have origin := SourceCurrentClassRecursiveValueOrigins.node firstRead inventory support.1 support.2 childAllowed ready
        (available _ List.mem_cons_self) childSafe valid history recursive occurrence
      refine ⟨original,rfl,?_⟩
      rcases origin with source | event
      · exact .inl source
      · obtain ⟨event,residual,eventAt,sourceAt⟩ := event
        exact .inr ⟨event,residual,.here (rest := rest) (found := found) eventAt,sourceAt⟩
    | succ forestIndex =>
      obtain ⟨next,receipt⟩ := node_effects firstRead support.1 support.2 childAllowed ready
        (available _ List.mem_cons_self) childSafe valid
      have oneRead : ChildrenReads formulas solver base
          (EditChildren.selected offset found first EditChildren.nil) memos current :=
        .selected (found := found) firstRead .nil
      have nextHistory := (SourceCurrentParentNativeHistory.edit_children oneRead history
        ready.checked.semantic.ready.semantic.1.normal.facts.coherent.valid).1
      obtain ⟨original,present,origin⟩ := ih next populated allowed receipt.ready
        (fun value member => receipt.effects.keeps.available value (available value (List.mem_cons_of_mem _ member)))
        (children_tail safe) receipt.globals.valid nextHistory forestIndex value (by simpa using selected) positions needle recursive occurrence
      refine ⟨original,by simpa using present,?_⟩
      rcases origin with source | event
      · exact .inl source
      · obtain ⟨event,residual,eventAt,sourceAt⟩ := event
        exact .inr ⟨event,residual,.selected (first := first) (found := found) eventAt,sourceAt⟩
  · intros; trivial
  · intros; trivial

/-- Actual ordered child edits retain the exact recursive value at the same forest slot. -/
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
    {positions needle} (recursive : SourceEqualityRequiredGraph.Recursive needle) (occurrence : Occurs value positions needle) :
    ∃ original, inputs[forestIndex]? = some original ∧
      (Occurs original positions needle ∨
        ∃ event residual, ChildEvent formulas solver base actual forestIndex event ∧ Occurs event residual needle) :=
  children_law reads inventory populated allowed ready available safe valid history forestIndex value selected positions needle recursive occurrence

/-- Actual list dispatch retains an exact recursive source or an indexed native/Head event. -/
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
    {positions needle} (recursive : SourceEqualityRequiredGraph.Recursive needle) (occurrence : Occurs value positions needle) :
    ∃ original, inputs[forestIndex]? = some original ∧
      (Occurs original positions needle ∨
        ∃ event residual, ListEvent formulas solver base actual forestIndex event ∧ Occurs event residual needle) := by
  cases reads with
  | leaf => exact ⟨value,selected,.inl occurrence⟩
  | children read =>
    obtain ⟨original,present,origin⟩ := children read inventory populated allowed ready available safe valid history
      forestIndex value selected recursive occurrence
    refine ⟨original,present,?_⟩
    rcases origin with source | event
    · exact .inl source
    · obtain ⟨event,residual,eventAt,sourceAt⟩ := event
      exact .inr ⟨event,residual,.children read selected (SourceCurrentSharedEditChildLineage.indexed read selected) eventAt,sourceAt⟩

/-- A completed compiled class retains the exact recursive payload from its captured input forest. -/
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
    {positions needle} (recursive : SourceEqualityRequiredGraph.Recursive needle) (occurrence : Occurs value positions needle) :
    ∃ original, inputs[forestIndex]? = some original ∧
      (Occurs original positions needle ∨
        ∃ event residual, ClassEvent formulas solver actual forestIndex event ∧ Occurs event residual needle) := by
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
      initialReady available safe valid history forestIndex value selected recursive occurrence
    refine ⟨original,present,?_⟩
    rcases origin with source | event
    · exact .inl source
    · obtain ⟨event,residual,eventAt,sourceAt⟩ := event
      exact .inr ⟨event,residual,.edit eventAt,sourceAt⟩

/-- The chronological right fold retains the same recursive value in its initial input or an actual earlier event. -/
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
    {positions needle} (recursive : SourceEqualityRequiredGraph.Recursive needle) (occurrence : Occurs value positions needle) :
    (∃ original, inputs[forestIndex]? = some original ∧ Occurs original positions needle) ∨
      ∃ event residual, FoldEvent formulas solver actual forestIndex event ∧ Occurs event residual needle := by
  induction reads generalizing inventory forestIndex value positions needle with
  | nil => exact .inl ⟨value,selected,occurrence⟩
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
      receipt.stored receipt.covered receipt.globals.valid phaseHistory forestIndex value selected recursive occurrence
    rcases origin with source | event
    · have phaseAt := source
      have earlier := ih inventory tailCoherent tailActive ready admitted available tailDomains stored covered valid history
        forestIndex phaseInput phaseSelected recursive phaseAt
      rcases earlier with source | event
      · exact .inl source
      · obtain ⟨event,residual,eventAt,sourceAt⟩ := event
        exact .inr ⟨event,residual,.tail headReads eventAt,sourceAt⟩
    · obtain ⟨event,residual,eventAt,sourceAt⟩ := event
      exact .inr ⟨event,residual,.head tailReads headReads phaseHistory eventAt,sourceAt⟩

end MicroCFTA.SourceCurrentClassFoldRecursiveValueOrigins
