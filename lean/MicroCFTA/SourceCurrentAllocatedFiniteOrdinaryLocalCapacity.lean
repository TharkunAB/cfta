import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStageCapacity
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryLocal

/-!
# Numeric query-entry plans after the actual local precheck

Only a live precheck enters its selected class-stage plan.
The loaded original field derives that branch and its normalized records.
The precheck changes equality operations and retains the native machine.
Every current stage invariant follows from the initial local facts.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryLocalCapacity
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
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
local notation "prefixState" => SourceCurrentAllocatedPrecheck.state
local notation "runPrefix" => SourceEqualityPartialPrecheckAllocation.run
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- Numeric class-stage plans are required only after a live actual precheck return. -/
def LocalCapacity (bits budget : Nat) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (fourth : Fourth) (memo : Memo) : Prop :=
  ∀ records, (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok (.classes records) →
    SourceCurrentAllocatedFiniteOrdinaryStageCapacity.StageCapacity bits budget records values
      (prefixState before loaded inherited) fourth memo

variable (bits : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
variable (budget : Nat) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (fourth : Fourth) (memo : Memo)
variable (ready : Ready before) (admitted : At formulas solver inventory before)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited)
    (available : Values before.native.machine.heap values) (domain : DChildren values)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physicalStored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (nativeStored : NativeStored before.native) (mergeStored : MergeStored memo)
    (capacity : LocalCapacity bits budget loaded inherited values before fourth memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)

include ready admitted cached found inheritedReady available domain correct physicalStored covered nativeStored mergeStored capacity valid

/-- Initial same-cache field facts derive every existing local range check from numeric entries. -/
theorem ranges : SourceCurrentAllocatedLocalReduction.Ranges budget loaded inherited values before fourth memo := by
  intro records actual
  obtain ⟨own, checked⟩ := SourceCurrentAllocatedLocalReductionActual.prefix_verified formulas solver inventory
    before original loaded inherited ready admitted cached found inheritedReady actual
  obtain ⟨proper, _records, _read, _classes, _order, fields⟩ := checked.classes records rfl
  have recordsProper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [] := by
    intro record member
    exact proper record.paths (List.mem_map.mpr ⟨record, member, rfl⟩)
  exact SourceCurrentAllocatedFiniteOrdinaryStageCapacity.ranges bits formulas solver inventory budget records
    values (prefixState before loaded inherited) fourth memo checked.ready checked.admitted available domain
    recordsProper fields correct physicalStored covered nativeStored mergeStored (capacity records actual) memos valid

/-- Initial local facts and numeric entries construct the complete reduction and positional bounds. -/
theorem finite :
    ∃ results after savedFourth saved next final,
      ∃ actual : SourceCurrentAllocatedLocalReduction.Reduction budget loaded inherited values before fourth memo
          results after savedFourth saved,
        SourceCurrentAllocatedLocalReductionActual.Reads formulas solver actual memos final ∧
        SourceCurrentAllocatedLocalReduction.Receipt formulas solver next original loaded inherited values results
          before after fourth savedFourth memo saved final ∧
        NativeStored after.native ∧ MergeStored saved ∧
          All₂ SourceCurrentAllocatedFiniteOrdinaryRequired.NodeNarrow values results :=
  SourceCurrentAllocatedFiniteOrdinaryLocal.finite formulas solver inventory budget original loaded inherited
    values before fourth memo ready admitted cached found inheritedReady available domain correct physicalStored covered
    (ranges bits formulas solver inventory budget original loaded inherited values before fourth memo ready admitted
      cached found inheritedReady available domain correct physicalStored covered nativeStored mergeStored capacity memos valid)
    nativeStored mergeStored memos valid

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryLocalCapacity
