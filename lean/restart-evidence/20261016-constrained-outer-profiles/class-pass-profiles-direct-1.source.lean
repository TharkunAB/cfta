import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEditProfiles
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryClassPass

/-!
# Strong profile stores through actual class and pass reads

A class clears only its target slots before its compiled edit. Each head
class captures the actual tail return of the right fold. Existing actual
receipts derive readiness, domains, and structural tables at that return.
Final propagation changes values and retains the checked state and memo.
No capacity, range plan, or future callback law is an input.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryClassPassProfiles
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedClassEdits (Class ClassReads compiled)
open SourceCurrentAllocatedClassEditPlan
open SourceCurrentAllocatedClassPass (Fold FoldReads Pass PassReads)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "CacheCovers" => SourceCurrentMemoMergeLanguage.CacheCovers
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- The same compiled class reads retain both strong profile stores. -/
theorem class_reads (inventory : Inventory) (record : SourceEqualityClassOrder.Record)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    {values results : List (Value Symbol Guard)} {before after : Checked width} {memo saved : Memo}
    {memos final : Memos} {actual : Class record values before memo results after saved}
    (reads : ClassReads formulas solver actual memos final)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (domain : DChildren values)
    (physical : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : NativeStored before.native) (profiles : Profiles memo)
    (valid : Valid before.native.machine.heap memos) (output : OutputStored before.native) :
    Profiles saved ∧ OutputStored after.native := by
  have domains : ∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) values :=
    fun path _ => SourceCurrentAllocatedFiniteOrdinaryTarget.forest_closed _ ready.semantic values available domain _
  cases reads with
  | edit lower =>
      have initialReady := SourceCurrentAllocatedSharedTargetState.initial_ready formulas solver inventory record values
        before.native.machine.heap before memo ready admitted
        (SourceEqualityRequiredCache.pure_keeps _ ready.semantic.ready) physical covered
      have initialStored := SourceCurrentAllocatedFiniteOrdinaryShared.initial_stored before memo native profiles.domain
      have safe : SourceCurrentAllocatedSharedEditEffects.ListSafe (compiled record) values := by
        obtain ⟨entries, built⟩ := compiled_children record coherent active
        rw [built]
        exact compiled_safe record coherent values domains entries built
      exact SourceCurrentAllocatedFiniteOrdinaryEditProfiles.list lower (compiled_populated record)
        (compiled_allowed record) initialReady available safe valid available domain initialStored domain profiles output

/-- The actual tail return supplies the next class's stores and captured input domain. -/
theorem fold (inventory : Inventory) {records values results} {before after : Checked width} {memo saved : Memo}
    {memos final : Memos} {actual : Fold records values before memo results after saved}
    (reads : FoldReads formulas solver actual memos final)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (domain : DChildren values)
    (physical : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : NativeStored before.native) (profiles : Profiles memo)
    (valid : Valid before.native.machine.heap memos) (output : OutputStored before.native) :
    Profiles saved ∧ OutputStored after.native := by
  induction reads generalizing inventory with
  | nil => exact ⟨profiles, output⟩
  | @cons records values before memo middle step current record results after saved memos stepMemos final tail head first last ih =>
      have tailCoherent := fun own member => coherent own (List.mem_cons_of_mem record member)
      have tailActive := fun own member => active own (List.mem_cons_of_mem record member)
      have firstProfiles := ih inventory tailCoherent tailActive ready admitted available domain physical covered native profiles valid output
      obtain ⟨next, firstReceipt, firstNative, _, related⟩ := SourceCurrentAllocatedFiniteOrdinaryClassPass.fold
        formulas solver inventory first tailCoherent tailActive ready admitted available domain physical covered native profiles.domain valid
      exact class_reads formulas solver next record (coherent _ List.mem_cons_self) (active _ List.mem_cons_self)
        last firstReceipt.ready firstReceipt.admitted firstReceipt.available
        (SourceCurrentAllocatedFiniteOrdinaryNarrow.forest_domain related) firstReceipt.stored firstReceipt.covered
        firstNative firstProfiles.1 firstReceipt.globals.valid firstProfiles.2

/-- Final empty propagation retains the same strong stores at the exact actual pass return. -/
theorem pass (inventory : Inventory) {records values results} {before after : Checked width} {memo saved : Memo}
    {memos final : Memos} {actual : Pass records values before memo results after saved}
    (reads : PassReads formulas solver actual memos final)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (domain : DChildren values)
    (physical : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : NativeStored before.native) (profiles : Profiles memo)
    (valid : Valid before.native.machine.heap memos) (output : OutputStored before.native) :
    Profiles saved ∧ OutputStored after.native := by
  cases reads with
  | done remaining =>
      exact fold formulas solver inventory remaining coherent active ready admitted available domain physical covered native profiles valid output

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryClassPassProfiles
