import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryLocal
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMkEdge
import MicroCFTA.SourceCurrentAllocatedParentEdgeActual
import MicroCFTA.SourceCurrentAllocatedParentWorkerCompletion

/-!
# Finite ordinary bounds for actual constrained parent reduction

Local reduction derives positional bounds before the actual constructor.
The constructor retains those children or the singleton Empty sentinel.
Raw rejection has no local call. Every certificate refers to the same
actual parent return and its complete checked state.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParent
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
open SourceCurrentAllocatedFiniteOrdinaryRequired (EdgeNarrow)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "DEdge" => SourceCurrentAllocatedFiniteOrdinaryDomain.Edge
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "MergeStored" => SourceCurrentAllocatedFiniteOrdinaryMergeCache.Stored
local notation "contradictory" => SourceEqualityMkEdgeAllocation.contradictory
local notation "raw" => SourceEqualityConjoinAllocation.readback
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

section Actual
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (original : EdgeValue Symbol Guard)
variable {budget : Nat} {loaded : Allocated} {inherited : EqValue}
    {before after : Checked width} {result : EdgeValue Symbol Guard}
    {fourth savedFourth : Fourth} {memo saved : Memo} {memos final : Memos}
    {actual : SourceCurrentAllocatedParentEdge.Edge budget original.entry.key.symbol original.entry.key.constraint
      loaded inherited original.children before fourth memo result after savedFourth saved}
variable (reads : SourceCurrentAllocatedParentEdgeActual.Reads formulas solver actual memos final)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (live : contradictory original.entry.key.constraint = false →
      SourceEqualityGuardReadback.Cached original.entry.key.constraint.equalities ∧
      SourceEqualityConstraintFieldLookup.load original.entry.key.constraint before.operations.constraints = .ok (some loaded) ∧
      SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited ∧
      Values before.native.machine.heap original.children ∧
      SourceCurrentAllocatedLocalReductionActual.Ranges budget loaded inherited original.children before fourth)
    (domain : DEdge original)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physicalStored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (nativeStored : NativeStored before.native) (mergeStored : MergeStored memo)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)

include reads ready admitted live domain correct physicalStored covered nativeStored mergeStored valid

/-- Actual parent reads derive the owner-relative bound before publishing an outer result. -/
theorem structure_from_reads :
    NativeStored after.native ∧ MergeStored saved ∧ EdgeNarrow original result := by
  cases reads with
  | rejected =>
      have constructor := SourceCurrentAllocatedMkEdge.reject_correct formulas solver inventory
        original.entry.key.symbol before ready admitted
      exact ⟨SourceCurrentAllocatedFiniteOrdinaryMkEdge.native_stored constructor.toPhysicalReceipt nativeStored,
        mergeStored, SourceCurrentAllocatedFiniteOrdinaryMkEdge.rejected constructor original⟩
  | live reads =>
      rename_i children middle test built reduction
      obtain ⟨cached, found, inheritedReady, available, ranges⟩ := live test
      have loadedReady := SourceEqualityConstraintFieldLookup.load_ready original.entry.key.constraint
        before.operations.constraints ready.good.operations.constraints cached loaded found
      obtain ⟨next, receipt, native, merged, bounds⟩ := SourceCurrentAllocatedFiniteOrdinaryLocal.verified
        formulas solver inventory original.entry.key.constraint reads ready admitted cached found inheritedReady
        available domain correct physicalStored covered ranges nativeStored mergeStored valid
      have storedReady := loadedReady.1.grows receipt.effects.grows.constraint_growth
      have field : SourceCurrentConjunctionEquality.FieldAvailable middle.operations (raw loaded) := by
        rw [loadedReady.2]
        exact (show SourceCurrentConjunctionEquality.FieldAvailable before.operations original.entry.key.constraint from
          ⟨cached, loaded, found⟩).grows receipt.effects.grows
      obtain ⟨chosen, returned, constructor⟩ := SourceCurrentAllocatedMkEdge.finite formulas solver next
        original.entry.key.symbol loaded children middle receipt.ready receipt.admitted storedReady field receipt.available
      have same := Prod.mk.inj (constructor.actual.symm.trans built)
      have sameValue := Except.ok.inj same.1
      cases sameValue
      cases same.2
      exact ⟨SourceCurrentAllocatedFiniteOrdinaryMkEdge.native_stored constructor.toPhysicalReceipt native,
        merged, SourceCurrentAllocatedFiniteOrdinaryMkEdge.narrowed constructor original bounds⟩

/-- The same parent return retains its full semantic receipt and both structural cache certificates. -/
theorem verified :
    ∃ next, SourceCurrentAllocatedParentEdge.Receipt formulas solver next original.entry.key.symbol
      original.entry.key.constraint loaded inherited original.children before result after fourth savedFourth memo saved final ∧
      NativeStored after.native ∧ MergeStored saved ∧ EdgeNarrow original result := by
  obtain ⟨next, receipt⟩ := SourceCurrentAllocatedParentEdgeActual.verified formulas solver inventory reads
    ready admitted live correct physicalStored covered valid
  exact ⟨next, receipt, structure_from_reads formulas solver inventory original reads ready admitted live domain
    correct physicalStored covered nativeStored mergeStored valid⟩
end Actual

/-- Initial domains and reached checks construct stable literal parent execution and its structural return. -/
theorem finite (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (original : EdgeValue Symbol Guard) (loaded : Allocated) (inherited : EqValue)
    (before : Checked width) (fourth : Fourth) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (cached : SourceEqualityGuardReadback.Cached original.entry.key.constraint.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original.entry.key.constraint before.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited)
    (available : Values before.native.machine.heap original.children) (domain : DEdge original)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physicalStored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : SourceCurrentAllocatedParentEdge.Ranges budget original.entry.key.constraint loaded inherited original.children before fourth memo)
    (nativeStored : NativeStored before.native) (mergeStored : MergeStored memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    ∃ result after savedFourth saved next final,
      SourceCurrentAllocatedParentWorkerCompletion.StableRun
        (fun g s r e p h m c n => SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
          original.entry.key.symbol original.entry.key.constraint inherited original.children before fourth memo)
        result after savedFourth saved ∧
      ∃ actual : SourceCurrentAllocatedParentEdge.Edge budget original.entry.key.symbol original.entry.key.constraint
          loaded inherited original.children before fourth memo result after savedFourth saved,
        SourceCurrentAllocatedParentEdgeActual.Reads formulas solver actual memos final ∧
        SourceCurrentAllocatedParentEdge.Receipt formulas solver next original.entry.key.symbol original.entry.key.constraint
          loaded inherited original.children before result after fourth savedFourth memo saved final ∧
        NativeStored after.native ∧ MergeStored saved ∧ EdgeNarrow original result := by
  obtain ⟨result, after, savedFourth, saved, next, final, actual, reads, receipt⟩ :=
    SourceCurrentAllocatedParentEdgeActual.finite formulas solver inventory budget original.entry.key.symbol
      original.entry.key.constraint loaded inherited original.children before fourth memo ready admitted cached found inheritedReady
      available correct physicalStored covered ranges memos valid
  have live : contradictory original.entry.key.constraint = false →
      SourceEqualityGuardReadback.Cached original.entry.key.constraint.equalities ∧
      SourceEqualityConstraintFieldLookup.load original.entry.key.constraint before.operations.constraints = .ok (some loaded) ∧
      SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited ∧
      Values before.native.machine.heap original.children ∧
      SourceCurrentAllocatedLocalReductionActual.Ranges budget loaded inherited original.children before fourth :=
    fun test => ⟨cached, found, inheritedReady, available,
      SourceCurrentAllocatedLocalReductionActual.ranges_of_finite (ranges test)⟩
  have structural := structure_from_reads formulas solver inventory original reads ready admitted live domain
    correct physicalStored covered nativeStored mergeStored valid
  exact ⟨result, after, savedFourth, saved, next, final,
    SourceCurrentAllocatedParentWorkerCompletion.edge_complete actual (fun _ => found), actual, reads, receipt, structural⟩

/-- Raw contradiction constructs the sentinel and stable literal return without child or field inputs. -/
theorem rejected_finite (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (budget : Nat) (original : EdgeValue Symbol Guard) (loaded : Allocated) (inherited : EqValue)
    (before : Checked width) (fourth : Fourth) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (test : contradictory original.entry.key.constraint = true)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physicalStored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (nativeStored : NativeStored before.native) (mergeStored : MergeStored memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    let result := (SourceCurrentAllocatedMkEdge.reject original.entry.key.symbol before).1
    let after := (SourceCurrentAllocatedMkEdge.reject original.entry.key.symbol before).2
    SourceCurrentAllocatedParentWorkerCompletion.StableRun
        (fun g s r e p h m c n => SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
          original.entry.key.symbol original.entry.key.constraint inherited original.children before fourth memo)
        result after fourth memo ∧
      ∃ actual : SourceCurrentAllocatedParentEdge.Edge budget original.entry.key.symbol original.entry.key.constraint
          loaded inherited original.children before fourth memo result after fourth memo,
        SourceCurrentAllocatedParentEdgeActual.Reads formulas solver actual memos memos ∧
        SourceCurrentAllocatedParentEdge.Receipt formulas solver inventory original.entry.key.symbol original.entry.key.constraint
          loaded inherited original.children before result after fourth fourth memo memo memos ∧
        NativeStored after.native ∧ MergeStored memo ∧ EdgeNarrow original result := by
  obtain ⟨_previous, _reads, receipt⟩ := SourceCurrentAllocatedParentEdge.rejected formulas solver inventory budget
    original.entry.key.symbol original.entry.key.constraint loaded inherited original.children before fourth memo
    ready admitted test correct physicalStored covered memos valid
  have constructor := SourceCurrentAllocatedMkEdge.reject_correct formulas solver inventory original.entry.key.symbol before ready admitted
  let actual : SourceCurrentAllocatedParentEdge.Edge budget original.entry.key.symbol original.entry.key.constraint loaded inherited
      original.children before fourth memo (SourceCurrentAllocatedMkEdge.reject original.entry.key.symbol before).1
        (SourceCurrentAllocatedMkEdge.reject original.entry.key.symbol before).2 fourth memo := .rejected test
  refine ⟨SourceCurrentAllocatedParentWorkerCompletion.edge_complete actual ?_, actual, .rejected (test := test), receipt,
    SourceCurrentAllocatedFiniteOrdinaryMkEdge.native_stored constructor.toPhysicalReceipt nativeStored,
    mergeStored, SourceCurrentAllocatedFiniteOrdinaryMkEdge.rejected constructor original⟩
  intro impossible
  rw [test] at impossible
  cases impossible

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParent
