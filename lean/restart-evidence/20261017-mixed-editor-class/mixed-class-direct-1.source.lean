import MicroCFTA.SourceCurrentConstrainedCapMixedEdit
import MicroCFTA.SourceCurrentAllocatedClassEdits

/-!
# Finite-depth caps through actual compiled classes

Each class captures its literal entry forest and clears only local slots.
Selected source paths supply the edit domains. Other roots can stay open.
The exact returned receipt retains physical and language facts.
These results verify supplied reads. They do not assert completion.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapMixedClass
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedClassEditPlan
open SourceCurrentAllocatedClassEdits (Class ClassReads Receipt)
open SourceEqualityProjectionPathDomain (ForestClosed)
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "Current" => SourceCurrentConstrainedCapCurrentNative.At Plain
local notation "MergeStored" => SourceCurrentConstrainedCapMemoMerge.Stored Plain
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "CacheCovers" => SourceCurrentMemoMergeLanguage.CacheCovers
variable {width : Nat}

/-- The compiled class depth includes its captured targets and literal edit syntax. -/
noncomputable def classDepth (record : SourceEqualityClassOrder.Record) (depth : Nat) : Nat :=
  SourceCurrentConstrainedCapMixedEdit.outputDepth depth depth (compiled record)

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual class reads produce both warm stores and the explicit output depth. -/
theorem verified
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (record : SourceEqualityClassOrder.Record)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    {values results : List (Value Symbol Guard)} {before after : Checked width} {memo saved : Memo}
    {memos final : Memos} {actual : Class record values before memo results after saved}
    (reads : ClassReads formulas solver actual memos final)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (physical : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (current : Current before) (merged : MergeStored memo) (depth : Nat)
    (bounded : ∀ value ∈ values, Cap Plain depth value) :
    ∃ next, Receipt formulas solver next record values before memo results after saved memos final ∧
      Current after ∧ MergeStored saved ∧ ∀ value ∈ results, Cap Plain (classDepth record depth) value := by
  cases reads with
  | edit lower =>
      have initialReady := SourceCurrentAllocatedSharedTargetState.initial_ready
        formulas solver inventory record values before.native.machine.heap before memo ready admitted
        (SourceEqualityRequiredCache.pure_keeps _ ready.semantic.ready) physical covered
      have safe : SourceCurrentAllocatedSharedEditEffects.ListSafe (compiled record) values := by
        obtain ⟨entries, built⟩ := compiled_children record coherent active
        rw [built]
        exact compiled_safe record coherent values domains entries built
      have initialStored := SourceCurrentConstrainedCapMixedShared.initial_stored record values before memo current merged
      have produced := SourceCurrentConstrainedCapMixedEdit.list lower inventory depth depth
        (compiled_populated record) (compiled_allowed record) initialReady available safe valid
        available domains initialStored bounded bounded
      obtain ⟨next, receipt⟩ := SourceCurrentAllocatedClassEdits.verified formulas solver inventory record coherent active
        (.edit lower) ready admitted available domains physical covered valid
      exact ⟨next, receipt, produced.1.current, produced.1.merge, produced.2⟩

end MicroCFTA.SourceCurrentConstrainedCapMixedClass
