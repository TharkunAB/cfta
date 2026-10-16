import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEditCapacity
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryClass

/-!
# Numeric capacity for one compiled class

The class captures its actual entry forest and clears only target slots.
The compiler derives edit safety. Initial native and merge certificates
derive the shared structural state. Numeric capacity replaces the lower
range plan without a completed class or future state premise.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryClassCapacity
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedClassEditPlan
open SourceCurrentAllocatedClassEdits (Class ClassReads ClassRanges Receipt)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow)
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
local notation "MergeStored" => SourceCurrentAllocatedFiniteOrdinaryMergeCache.Stored
local notation "CacheCovers" => SourceCurrentMemoMergeLanguage.CacheCovers
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A class uses the literal compiled edit plan at its actual freshly captured forest. -/
def ClassCapacity (bits : Nat) (record : SourceEqualityClassOrder.Record)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (memo : Memo) : Prop :=
  SourceCurrentAllocatedFiniteOrdinaryEditCapacity.ListCapacity bits record values (compiled record) values
    (SourceCurrentAllocatedSharedTargetState.initial before memo)

variable (bits : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (record : SourceEqualityClassOrder.Record)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (domain : DChildren values)
    (physical : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : NativeStored before.native) (merged : MergeStored memo)
    (capacity : ClassCapacity bits record values before memo) (memos : Memos)
    (valid : Valid before.native.machine.heap memos)

include coherent active ready admitted available domain physical covered native merged capacity valid

/-- Initial forest facts and numeric entries derive the complete compiled class range plan. -/
theorem class_ranges : ClassRanges record values before memo := by
  have domains : ∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) values :=
    fun path _ => SourceCurrentAllocatedFiniteOrdinaryTarget.forest_closed _ ready.semantic values available domain _
  have initialReady := SourceCurrentAllocatedSharedTargetState.initial_ready formulas solver inventory record values
    before.native.machine.heap before memo ready admitted
    (SourceEqualityRequiredCache.pure_keeps _ ready.semantic.ready) physical covered
  have initialStored := SourceCurrentAllocatedFiniteOrdinaryShared.initial_stored before memo native merged
  have safe : SourceCurrentAllocatedSharedEditEffects.ListSafe (compiled record) values := by
    obtain ⟨entries, built⟩ := compiled_children record coherent active
    rw [built]
    exact compiled_safe record coherent values domains entries built
  exact SourceCurrentAllocatedFiniteOrdinaryEditCapacity.list_ranges bits formulas solver record values
    before.native.machine.heap available domain coherent active capacity (compiled_populated record)
    (compiled_allowed record) inventory initialReady available safe initialStored domain memos valid

/-- Numeric capacity and initial invariants construct the actual class and its structural receipts. -/
theorem finite :
    ∃ results after saved next final, ∃ actual : Class record values before memo results after saved,
      ClassReads formulas solver actual memos final ∧
      Receipt formulas solver next record values before memo results after saved memos final ∧
      NativeStored after.native ∧ MergeStored saved ∧ All₂ NodeNarrow values results :=
  SourceCurrentAllocatedFiniteOrdinaryClass.finite formulas solver inventory record coherent active values before memo
    ready admitted available domain physical covered native merged
    (class_ranges bits formulas solver inventory record coherent active values before memo ready admitted available domain
      physical covered native merged capacity memos valid) memos valid

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryClassCapacity
