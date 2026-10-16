import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardEdit
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryClassPass
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardOwn

/-!
# Hereditary guards through actual class and pass reads

Each class captures its literal entry forest and clears only its slots.
One class envelope bounds all callback results from immutable source positions.
The pass executes its tail first. The head captures that actual tail return.
No future guard profile, range plan, or completed body is an input.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardClassPass
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedClassEdits (Class ClassReads)
open SourceCurrentAllocatedClassEditPlan
open SourceCurrentAllocatedClassPass (Fold FoldReads Pass PassReads)
open SourceCurrentAllocatedFiniteOrdinaryGuardIteration
open SourceCurrentAllocatedFiniteOrdinaryGuardLimits (Le)
open SourceCurrentAllocatedFiniteOrdinaryGuardTarget (foldLimit)
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
local notation "NativeGuards" => SourceCurrentAllocatedFiniteOrdinaryGuardStored.Stored
local notation "MergeGuards" => SourceCurrentAllocatedFiniteOrdinaryMergeGuardCache.Stored
local notation "Limits" => SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Limits
local notation "Profile" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Children

/-- A class uses one common envelope for its captured forest and original inputs. -/
def classLimit (limits : Limits) (record : SourceEqualityClassOrder.Record) : Limits :=
  foldLimit limits (record.paths.length + 1)

/-- A right fold uses the actual tail envelope before the head class. -/
def passLimit (limits : Limits) : List SourceEqualityClassOrder.Record → Limits
  | [] => limits
  | record :: rest => classLimit (passLimit limits rest) record

/-- The ordered pass envelope is the initial vector iterated by the literal class step sum. -/
theorem passLimit_eq (limits : Limits) (records : List SourceEqualityClassOrder.Record) :
    passLimit limits records = foldLimit limits (SourceCurrentAllocatedFiniteOrdinaryGuardOwn.classSteps records) := by
  induction records with
  | nil => rfl
  | cons record rest ih =>
      simp only [passLimit, classLimit, SourceCurrentAllocatedFiniteOrdinaryGuardOwn.classSteps,
        List.map_cons, List.sum_cons] at *
      rw [ih, ← foldLimit_add, Nat.add_comm]

/-- An initial bound on the own class step sum bounds the complete pass envelope. -/
theorem passLimit_le_count (limits : Limits) (records : List SourceEqualityClassOrder.Record) (count : Nat)
    (enough : SourceCurrentAllocatedFiniteOrdinaryGuardOwn.classSteps records ≤ count) :
    Le (passLimit limits records) (foldLimit limits count) := by
  rw [passLimit_eq]
  exact foldLimit_count_mono limits enough

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- The same class reads retain both universal tables and produce the captured-forest envelope. -/
theorem class_reads (inventory : Inventory) (record : SourceEqualityClassOrder.Record)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    {values results : List (Value Symbol Guard)} {before after : Checked width} {memo saved : Memo}
    {memos final : Memos} {actual : Class record values before memo results after saved}
    (reads : ClassReads formulas solver actual memos final)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (domain : DChildren values)
    (physical : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : NativeStored before.native) (merged : MergeStored memo)
    (valid : Valid before.native.machine.heap memos)
    (guards : NativeGuards before.native) (mergeGuards : MergeGuards memo)
    (limits : Limits) (profile : Profile limits values) :
    MergeGuards saved ∧ NativeGuards after.native ∧ Profile (classLimit limits record) results := by
  have domains : ∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) values :=
    fun path _ => SourceCurrentAllocatedFiniteOrdinaryTarget.forest_closed _ ready.semantic values available domain _
  cases reads with
  | edit lower =>
      have initialReady := SourceCurrentAllocatedSharedTargetState.initial_ready formulas solver inventory record values
        before.native.machine.heap before memo ready admitted
        (SourceEqualityRequiredCache.pure_keeps _ ready.semantic.ready) physical covered
      have initialStored := SourceCurrentAllocatedFiniteOrdinaryShared.initial_stored before memo native merged
      have initialGuards := SourceCurrentAllocatedFiniteOrdinaryGuardShared.initial_stored record values before memo guards mergeGuards
      have safe : SourceCurrentAllocatedSharedEditEffects.ListSafe (compiled record) values := by
        obtain ⟨entries, built⟩ := compiled_children record coherent active
        rw [built]
        exact compiled_safe record coherent values domains entries built
      have checked := SourceCurrentAllocatedFiniteOrdinaryGuardEdit.list lower (compiled_populated record)
        (compiled_allowed record) initialReady available safe valid available domain initialStored domain
        initialGuards limits limits profile profile
      exact ⟨checked.1.merge, checked.1.native,
        SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Children.mono _ checked.2 (leafLimit_same record limits)⟩

/-- Earlier tail reads derive the guard vector and stores for the next captured forest. -/
theorem fold (inventory : Inventory) {records values results} {before after : Checked width} {memo saved : Memo}
    {memos final : Memos} {actual : Fold records values before memo results after saved}
    (reads : FoldReads formulas solver actual memos final)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (domain : DChildren values)
    (physical : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : NativeStored before.native) (merged : MergeStored memo)
    (valid : Valid before.native.machine.heap memos)
    (guards : NativeGuards before.native) (mergeGuards : MergeGuards memo)
    (limits : Limits) (profile : Profile limits values) :
    MergeGuards saved ∧ NativeGuards after.native ∧ Profile (passLimit limits records) results := by
  induction reads generalizing inventory with
  | nil => exact ⟨mergeGuards, guards, profile⟩
  | @cons records values before memo middle step current record results after saved memos stepMemos final tail head first last ih =>
      have tailCoherent := fun own member => coherent own (List.mem_cons_of_mem record member)
      have tailActive := fun own member => active own (List.mem_cons_of_mem record member)
      have firstGuards := ih inventory tailCoherent tailActive ready admitted available domain physical covered native merged
        valid guards mergeGuards
      obtain ⟨next, firstReceipt, firstNative, firstMerged, related⟩ := SourceCurrentAllocatedFiniteOrdinaryClassPass.fold
        formulas solver inventory first tailCoherent tailActive ready admitted available domain physical covered native merged valid
      exact class_reads formulas solver next record (coherent _ List.mem_cons_self) (active _ List.mem_cons_self)
        last firstReceipt.ready firstReceipt.admitted firstReceipt.available
        (SourceCurrentAllocatedFiniteOrdinaryNarrow.forest_domain related) firstReceipt.stored firstReceipt.covered
        firstNative firstMerged firstReceipt.globals.valid firstGuards.2.1 firstGuards.1 _ firstGuards.2.2

/-- Final empty propagation retains both tables and the same produced pass envelope. -/
theorem pass (inventory : Inventory) {records values results} {before after : Checked width} {memo saved : Memo}
    {memos final : Memos} {actual : Pass records values before memo results after saved}
    (reads : PassReads formulas solver actual memos final)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (domain : DChildren values)
    (physical : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : NativeStored before.native) (merged : MergeStored memo)
    (valid : Valid before.native.machine.heap memos)
    (guards : NativeGuards before.native) (mergeGuards : MergeGuards memo)
    (limits : Limits) (profile : Profile limits values) :
    MergeGuards saved ∧ NativeGuards after.native ∧ Profile (passLimit limits records) results := by
  cases reads with
  | done remaining =>
      have checked := fold formulas solver inventory remaining coherent active ready admitted available domain physical covered native merged
        valid guards mergeGuards limits profile
      refine ⟨checked.1, checked.2.1, ?_⟩
      unfold EqualityLeafProjectionRuntimeEmpty.propagate EqualityLeafProjectionRuntimeEmpty.erase
      split
      · exact SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.children_of_members _ _ (fun _ member => by
          obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
          trivial)
      · exact checked.2.2

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardClassPass
