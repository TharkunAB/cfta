import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStage
import MicroCFTA.SourceCurrentAllocatedLocalReductionActual

/-!
# Structural bounds for the actual local equality reduction

The precheck retains native tables. Unchanged children retain identity.
Contradiction erases their slots. Live classes use the exact actual Scan,
required-path return, and class pass. The output retains positional domain
and height bounds with its complete physical and language receipt.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryLocal
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
open SourceCurrentAllocatedLocalReduction (Reduction Receipt)
open SourceCurrentAllocatedLocalReductionActual (Reads Ranges prefix_verified)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "MergeStored" => SourceCurrentAllocatedFiniteOrdinaryMergeCache.Stored
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

section Verify
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (original : Guard)
variable {budget : Nat} {loaded : Allocated} {inherited : EqValue}
    {values results : List (Value Symbol Guard)} {before after : Checked width}
    {fourth savedFourth : Fourth} {memo saved : Memo} {memos final : Memos}
    {actual : Reduction budget loaded inherited values before fourth memo results after savedFourth saved}
variable (reads : Reads formulas solver actual memos final)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited)
    (available : Values before.native.machine.heap values) (domain : DChildren values)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physicalStored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : Ranges budget loaded inherited values before fourth)
    (nativeStored : NativeStored before.native) (mergeStored : MergeStored memo)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)

include reads ready admitted cached found inheritedReady available domain correct physicalStored covered ranges nativeStored mergeStored valid

private theorem actual_structure :
    NativeStored after.native ∧ MergeStored saved ∧ All₂ NodeNarrow values results := by
  cases reads with
  | unchanged => exact ⟨nativeStored, mergeStored, SourceCurrentAllocatedFiniteOrdinaryNarrow.forest_refl domain⟩
  | emptyChildren => exact ⟨nativeStored, mergeStored, SourceCurrentAllocatedFiniteOrdinaryNarrow.forest_erase values⟩
  | classes read =>
      rename_i records outcome actual continuation
      obtain ⟨own, checked⟩ := prefix_verified formulas solver inventory before original loaded inherited
        ready admitted cached found inheritedReady actual
      obtain ⟨proper, _, _, _, _, fields⟩ := checked.classes records rfl
      have recordsProper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [] := by
        intro record member
        exact proper record.paths (List.mem_map.mpr ⟨record, member, rfl⟩)
      exact SourceCurrentAllocatedFiniteOrdinaryStage.structure_from_reads formulas solver inventory read
        checked.ready checked.admitted available domain recordsProper fields correct physicalStored covered
        (ranges records checked.actual) nativeStored mergeStored valid

/-- Initial facts derive the full actual local receipt and positional structural bounds. -/
theorem verified :
    ∃ next, Receipt formulas solver next original loaded inherited values results before after fourth savedFourth memo saved final ∧
      NativeStored after.native ∧ MergeStored saved ∧ All₂ NodeNarrow values results := by
  obtain ⟨next, receipt⟩ := SourceCurrentAllocatedLocalReductionActual.verified formulas solver inventory original
    reads ready admitted cached found inheritedReady available correct physicalStored covered ranges valid
  exact ⟨next, receipt, actual_structure formulas solver inventory original reads ready admitted cached found inheritedReady
    available domain correct physicalStored covered ranges nativeStored mergeStored valid⟩
end Verify

/-- Initial invariants and reached ranges construct the actual local return with its input bounds. -/
theorem finite (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited)
    (available : Values before.native.machine.heap values) (domain : DChildren values)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physicalStored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : SourceCurrentAllocatedLocalReduction.Ranges budget loaded inherited values before fourth memo)
    (nativeStored : NativeStored before.native) (mergeStored : MergeStored memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    ∃ results after savedFourth saved next final,
      ∃ actual : Reduction budget loaded inherited values before fourth memo results after savedFourth saved,
        Reads formulas solver actual memos final ∧
        Receipt formulas solver next original loaded inherited values results before after fourth savedFourth memo saved final ∧
        NativeStored after.native ∧ MergeStored saved ∧ All₂ NodeNarrow values results := by
  obtain ⟨results, after, savedFourth, saved, next, final, actual, reads, receipt⟩ :=
    SourceCurrentAllocatedLocalReductionActual.finite formulas solver inventory budget original loaded inherited values before fourth memo
      ready admitted cached found inheritedReady available correct physicalStored covered ranges memos valid
  have structural := actual_structure formulas solver inventory original reads ready admitted cached found inheritedReady
    available domain correct physicalStored covered (SourceCurrentAllocatedLocalReductionActual.ranges_of_finite ranges)
    nativeStored mergeStored valid
  exact ⟨results, after, savedFourth, saved, next, final, actual, reads, receipt, structural⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryLocal
