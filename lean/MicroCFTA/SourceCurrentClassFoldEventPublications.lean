import MicroCFTA.SourceCurrentClassEventPublications
import MicroCFTA.SourceCurrentClassPublicationHistory
import MicroCFTA.SourceCurrentClassFoldStructuralOrigins
import MicroCFTA.SourceCurrentAllocatedClassWorkerCompletion
import MicroCFTA.SourceCurrentAllocatedClassWorkerStability

/-!
# Actual publication intervals for selected class-fold events

Each selected event keeps its exact native or Head receipt. The same
captured event heap has a physical publication prefix and suffix.
The prefix starts at the supplied initial heap. Actual fold operations
supply both intervals. Native history remains a separate premise.
-/
namespace MicroCFTA.SourceCurrentClassFoldEventPublications
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityEdits SourceEqualityEditLeafPaths SourceCurrentEditDomains
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentAllocatedSharedEditGraph SourceCurrentAllocatedSharedEditEffects
open SourceCurrentNativeEdgeWriterGrowth (History)
open SourceCurrentClassFoldStructuralOrigins (ListEvent ClassEvent FoldEvent)
open SourceCurrentClassEventPublications (Source)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Heap" => State Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Inventory" => SourceCurrentAllocatedNativeInventoryState.Inventory
local notation "SharedReady" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Class" => SourceCurrentAllocatedClassEdits.Class
local notation "ClassReads" => SourceCurrentAllocatedClassEdits.ClassReads
local notation "Fold" => SourceCurrentAllocatedClassPass.Fold
local notation "FoldReads" => SourceCurrentAllocatedClassPass.FoldReads
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable {initialHeap : Heap}
local notation "PublicationHistory" => SourceCurrentNativeMuPublication.History

private theorem list_unique {record originals edits inputs before first after second later}
    (one : EditList (width := width) record originals edits inputs before first after)
    (two : EditList record originals edits inputs before second later) : first = second ∧ after = later := by
  obtain ⟨fuel,done⟩ := SourceCurrentAllocatedSharedEditWorkerCompletion.list_uniform one
  obtain ⟨other,completed⟩ := SourceCurrentAllocatedSharedEditWorkerCompletion.list_uniform two
  exact SourceCurrentAllocatedSharedEditWorkerStability.editList_done_unique (done fuel (Nat.le_refl _)) (completed other (Nat.le_refl _))

private theorem fold_unique {records inputs before memo first after saved second later current}
    (one : SourceCurrentAllocatedClassPass.Fold (width := width) records inputs before memo first after saved)
    (two : Fold records inputs before memo second later current) : first = second ∧ after = later ∧ saved = current := by
  obtain ⟨e,p,h,m,s,n,done⟩ := SourceCurrentAllocatedClassWorkerCompletion.fold_complete one
  obtain ⟨E,P,H,M,S,N,completed⟩ := SourceCurrentAllocatedClassWorkerCompletion.fold_complete two
  exact SourceCurrentAllocatedClassWorkerStability.fold_done_unique
    (done e p h m s n (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
    (completed E P H M S N (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))

private theorem list_event_unique {formulas solver base record originals edits inputs before first after memos final}
    {one : EditList (width := width) record originals edits inputs before first after}
    (_reads : ListReads formulas solver base one memos final)
    {second later index event} {two : EditList record originals edits inputs before second later}
    (_source : ListEvent formulas solver base two index event) : first = second ∧ after = later :=
  list_unique one two

private theorem fold_reads_unique {formulas solver records inputs before memo first after saved memos final}
    {one : SourceCurrentAllocatedClassPass.Fold (width := width) records inputs before memo first after saved}
    (_reads : FoldReads formulas solver one memos final)
    {second later current otherMemos otherFinal} {two : Fold records inputs before memo second later current}
    (_other : FoldReads formulas solver two otherMemos otherFinal) : first = second ∧ after = later ∧ saved = current :=
  fold_unique one two

private theorem fold_event_unique {formulas solver records inputs before memo first after saved memos final}
    {one : SourceCurrentAllocatedClassPass.Fold (width := width) records inputs before memo first after saved}
    (_reads : FoldReads formulas solver one memos final)
    {second later current index event} {two : Fold records inputs before memo second later current}
    (_source : FoldEvent formulas solver two index event) : first = second ∧ after = later ∧ saved = current :=
  fold_unique one two

private theorem list_source {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {base : Heap}
    {record originals edits inputs before results after memos final}
    {actual : EditList (width := width) record originals edits inputs before results after}
    (reads : ListReads formulas solver base actual memos final)
    (originalValues : Values base originals)
    (inventory : Inventory) (populated : Populated edits) (allowed : Allowed record edits)
    (ready : SharedReady formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap inputs) (safe : ListSafe edits inputs)
    (valid : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos) (history : History before.checked)
    (published : PublicationHistory initialHeap before.checked.native.machine.heap)
    {index event} (source : ListEvent formulas solver base actual index event) :
    Source (width := width) formulas solver initialHeap event after.checked.native.machine.heap := by
  cases reads with
  | leaf => cases source
  | children childReads =>
    cases source with
    | children eventRead selected slice eventAt =>
      exact SourceCurrentClassEventPublications.children childReads originalValues inventory populated allowed ready available safe valid history published eventAt

private theorem class_source {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {record inputs before memo results after saved memos final}
    {actual : SourceCurrentAllocatedClassEdits.Class (width := width) record inputs before memo results after saved}
    (reads : ClassReads formulas solver actual memos final)
    (inventory : Inventory) (coherent : SourceEqualityClassOrder.Coherent record)
    (active : EqualityNormalize.Nontrivial record.paths)
    (ready : SourceCurrentConjunctionClassScan.Ready before)
    (admitted : SourceCurrentAllocatedNativeInventoryState.At formulas solver inventory before)
    (available : Values before.native.machine.heap inputs)
    (domains : ∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) inputs)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) (history : History before)
    (published : PublicationHistory initialHeap before.native.machine.heap) :
    ∀ otherAfter otherSaved (other : Class record inputs before memo results otherAfter otherSaved),
      ∀ index event, ClassEvent formulas solver other index event →
        Source (width := width) formulas solver initialHeap event after.native.machine.heap := by
  cases reads with
  | edit lower =>
    intro otherAfter otherSaved other index event source
    cases source with
    | edit eventAt =>
      have same := (list_event_unique lower eventAt).2
      cases same
      have initialReady := SourceCurrentAllocatedSharedTargetState.initial_ready formulas solver inventory record inputs
        before.native.machine.heap before memo ready admitted (SourceEqualityRequiredCache.pure_keeps _ ready.semantic.ready) stored covered
      have safe : ListSafe (SourceCurrentAllocatedClassEditPlan.compiled record) inputs := by
        obtain ⟨entries,built⟩ := SourceCurrentAllocatedClassEditPlan.compiled_children record coherent active
        rw [built]
        exact SourceCurrentAllocatedClassEditPlan.compiled_safe record coherent inputs domains entries built
      exact list_source lower available inventory (SourceCurrentAllocatedClassEditPlan.compiled_populated record)
        (SourceCurrentAllocatedClassEditPlan.compiled_allowed record) initialReady available safe valid history published eventAt

private def FoldLaw (initialHeap : Heap) {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {records inputs before memo results after saved}
    (_actual : SourceCurrentAllocatedClassPass.Fold (width := width) records inputs before memo results after saved) (memos : Memos) : Prop :=
  ∀ inventory, (∀ record ∈ records, SourceEqualityClassOrder.Coherent record) →
    (∀ record ∈ records, EqualityNormalize.Nontrivial record.paths) →
    SourceCurrentConjunctionClassScan.Ready before → SourceCurrentAllocatedNativeInventoryState.At formulas solver inventory before →
    Values before.native.machine.heap inputs →
    (∀ record ∈ records, ∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) inputs) →
    SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo →
    (∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo) →
    EndpointMemoGateTrace.Valid before.native.machine.heap memos → History before →
    PublicationHistory initialHeap before.native.machine.heap →
    ∀ otherAfter otherSaved (other : Fold records inputs before memo results otherAfter otherSaved),
      ∀ index event, FoldEvent formulas solver other index event →
        Source (width := width) formulas solver initialHeap event after.native.machine.heap

private theorem fold_law {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {records inputs before memo results after saved memos final}
    {actual : SourceCurrentAllocatedClassPass.Fold (width := width) records inputs before memo results after saved}
    (reads : FoldReads formulas solver actual memos final) : FoldLaw initialHeap (formulas := formulas) (solver := solver) actual memos := by
  induction reads with
  | nil =>
    intro inventory coherent active ready admitted available domains stored covered valid history published otherAfter otherSaved other index event source
    cases source
  | @cons records inputs before memo middle step current record results after saved memos phaseMemos final
      tail head tailReads headReads ih =>
    intro inventory coherent active ready admitted available domains stored covered valid history published otherAfter otherSaved other index event source
    have tailCoherent := fun own member => coherent own (List.mem_cons_of_mem record member)
    have tailActive := fun own member => active own (List.mem_cons_of_mem record member)
    have tailDomains := fun own member => domains own (List.mem_cons_of_mem record member)
    obtain ⟨phaseInventory,receipt⟩ := SourceCurrentAllocatedClassPass.Fold.verified formulas solver inventory tailReads
      tailCoherent tailActive ready admitted available tailDomains stored covered valid
    obtain ⟨tailPublished⟩ := SourceCurrentClassPublicationHistory.fold tailReads inventory
      tailCoherent tailActive ready admitted available tailDomains stored covered valid
    have phasePublished := SourceCurrentNativeMuPublication.History.trans published tailPublished
    have phaseHistory := SourceCurrentParentNativeHistory.class_pass (SourceCurrentAllocatedClassPass.PassReads.done tailReads) history ready
    cases source with
    | head eventTailReads eventHeadReads eventHistory eventAt =>
      obtain ⟨rfl,rfl,rfl⟩ := fold_reads_unique tailReads eventTailReads
      exact class_source headReads phaseInventory (coherent record List.mem_cons_self) (active record List.mem_cons_self)
        receipt.ready receipt.admitted receipt.available
        (fun path member => receipt.domains _ (domains record List.mem_cons_self path member))
        receipt.stored receipt.covered receipt.globals.valid phaseHistory phasePublished _ _ _ index event eventAt
    | tail eventHeadReads eventAt =>
      obtain ⟨rfl,rfl,rfl⟩ := fold_event_unique tailReads eventAt
      obtain ⟨next,headReceipt⟩ := SourceCurrentAllocatedClassEdits.verified formulas solver phaseInventory record
        (coherent record List.mem_cons_self) (active record List.mem_cons_self) headReads
        receipt.ready receipt.admitted receipt.available
        (fun path member => receipt.domains _ (domains record List.mem_cons_self path member))
        receipt.stored receipt.covered receipt.globals.valid
      have headPublished := SourceCurrentClassPublicationHistory.class_history headReads phaseInventory
        (coherent record List.mem_cons_self) (active record List.mem_cons_self)
        receipt.ready receipt.admitted receipt.available
        (fun path member => receipt.domains _ (domains record List.mem_cons_self path member))
        receipt.stored receipt.covered receipt.globals.valid
      exact (ih inventory tailCoherent tailActive ready admitted available tailDomains stored covered valid history published
        _ _ _ index event eventAt).later headReceipt.effects.keeps headPublished

/-- Actual fold reads derive a selected event with both physical publication intervals. -/
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
    (published : PublicationHistory initialHeap before.native.machine.heap)
    {forestIndex event} (source : FoldEvent formulas solver actual forestIndex event) :
    Source (width := width) formulas solver initialHeap event after.native.machine.heap :=
  fold_law reads inventory coherent active ready admitted available domains stored covered valid history published after saved actual forestIndex event source

end MicroCFTA.SourceCurrentClassFoldEventPublications
