import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryLocalResources
import MicroCFTA.SourceCurrentAllocatedLocalWorkerStability
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryLocal

/-!
# Initial resources for local equality reduction

The budget reads the deterministic initial precheck result.
Early branches make no constructor request and retain all warm tables.
A live branch constructs its stage at the same returned operation state.
The original field and inherited payload retain the full existing receipt.
-/
namespace MicroCFTA.LocalParentResourceChecks
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
open SourceCurrentAllocatedLocalReduction (Reduction Receipt)
open SourceCurrentAllocatedLocalReductionActual (Reads)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests)
open MergedOrdinaryHeight (childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "Capacity" => SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity
local notation "prefixState" => SourceCurrentAllocatedPrecheck.state
local notation "runPrefix" => SourceEqualityPartialPrecheckAllocation.run


variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

theorem constructed_unchanged (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits budget : Nat) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (fourth : Fourth) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited)
    (available : Values before.native.machine.heap values)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physical : PhysicalStored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count)
    (heightBound : childrenHeight values ≤ bound)
    (branch : (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok .unchanged)
    (capacity : Capacity bits before) :
    ∃ next final requests,
    ∃ actual : Reduction budget loaded inherited values before fourth memo values
        (prefixState before loaded inherited) fourth memo,
      Reads formulas solver actual memos final ∧
      Receipt formulas solver next original loaded inherited values values before
        (prefixState before loaded inherited) fourth fourth memo memo final ∧
      SourceCurrentAllocatedLocalWorkerCompletion.StableRun
        (fun g s r e p h m c n => SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n
          budget loaded inherited values before fourth memo) values (prefixState before loaded inherited) fourth memo ∧
      NativeStored (prefixState before loaded inherited).native ∧
      OutputStored (prefixState before loaded inherited).native ∧ Profiles memo ∧
      Trace before.native.machine.heap (prefixState before loaded inherited).native.machine.heap requests ∧
      nodeRequests requests = 0 ∧ edgeRequests requests = 0 := by
  have pathsBound : ∀ records, (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok (.classes records) →
      ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth := by
    intro records actual
    rw [branch] at actual
    cases actual
  obtain ⟨results, after, saved, next, final, requests, actual, reads, receipt, stable,
    finalNative, finalOutput, finalProfiles, _produced, _related, _length, _height, trace, nodes, edges,
    _capacity, _nodeSupply, _edgeSupply⟩ := SourceCurrentAllocatedFiniteOrdinaryLocalResources.complete formulas solver
      inventory bits budget original loaded inherited values before fourth memo ready admitted cached found inheritedReady
      available correct physical profiles native output covered memos valid rows arity count depth bound profile lengthBound
      pathsBound heightBound
      (by simpa only [SourceCurrentAllocatedFiniteOrdinaryLocalResources.nodeBudget, branch, Nat.add_zero] using capacity.1)
      (by simpa only [SourceCurrentAllocatedFiniteOrdinaryLocalResources.edgeBudget, branch, Nat.add_zero] using capacity.2)
  obtain ⟨g, s, r, e, p, h, m, c, n, enough⟩ := stable
  have done := enough g s r e p h m c n (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  have immediate := SourceCurrentAllocatedLocalWorker.reduce_unchanged 0 0 0 0 0 0 0 0 0 budget loaded inherited
    values before fourth memo branch
  obtain ⟨rfl, rfl, _sameFourth, rfl⟩ := SourceCurrentAllocatedLocalWorkerStability.reduce_done_unique done immediate
  exact ⟨next, final, requests, actual, reads, receipt, SourceCurrentAllocatedLocalWorkerCompletion.reduce_complete actual,
    finalNative, finalOutput, finalProfiles, trace,
    Nat.eq_zero_of_le_zero (by simpa only [SourceCurrentAllocatedFiniteOrdinaryLocalResources.nodeBudget, branch] using nodes),
    Nat.eq_zero_of_le_zero (by simpa only [SourceCurrentAllocatedFiniteOrdinaryLocalResources.edgeBudget, branch] using edges)⟩

theorem constructed_emptyChildren (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits budget : Nat) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (fourth : Fourth) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited)
    (available : Values before.native.machine.heap values)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physical : PhysicalStored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count)
    (heightBound : childrenHeight values ≤ bound)
    (branch : (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok .emptyChildren)
    (capacity : Capacity bits before) :
    ∃ next final requests,
    ∃ actual : Reduction budget loaded inherited values before fourth memo (EqualityLeafProjectionRuntimeEmpty.erase values)
        (prefixState before loaded inherited) fourth memo,
      Reads formulas solver actual memos final ∧
      Receipt formulas solver next original loaded inherited values (EqualityLeafProjectionRuntimeEmpty.erase values) before
        (prefixState before loaded inherited) fourth fourth memo memo final ∧
      SourceCurrentAllocatedLocalWorkerCompletion.StableRun
        (fun g s r e p h m c n => SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n
          budget loaded inherited values before fourth memo) (EqualityLeafProjectionRuntimeEmpty.erase values) (prefixState before loaded inherited) fourth memo ∧
      NativeStored (prefixState before loaded inherited).native ∧
      OutputStored (prefixState before loaded inherited).native ∧ Profiles memo ∧
      Trace before.native.machine.heap (prefixState before loaded inherited).native.machine.heap requests ∧
      nodeRequests requests = 0 ∧ edgeRequests requests = 0 := by
  have pathsBound : ∀ records, (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok (.classes records) →
      ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth := by
    intro records actual
    rw [branch] at actual
    cases actual
  obtain ⟨results, after, saved, next, final, requests, actual, reads, receipt, stable,
    finalNative, finalOutput, finalProfiles, _produced, _related, _length, _height, trace, nodes, edges,
    _capacity, _nodeSupply, _edgeSupply⟩ := SourceCurrentAllocatedFiniteOrdinaryLocalResources.complete formulas solver
      inventory bits budget original loaded inherited values before fourth memo ready admitted cached found inheritedReady
      available correct physical profiles native output covered memos valid rows arity count depth bound profile lengthBound
      pathsBound heightBound
      (by simpa only [SourceCurrentAllocatedFiniteOrdinaryLocalResources.nodeBudget, branch, Nat.add_zero] using capacity.1)
      (by simpa only [SourceCurrentAllocatedFiniteOrdinaryLocalResources.edgeBudget, branch, Nat.add_zero] using capacity.2)
  obtain ⟨g, s, r, e, p, h, m, c, n, enough⟩ := stable
  have done := enough g s r e p h m c n (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  have immediate := SourceCurrentAllocatedLocalWorker.reduce_emptyChildren 0 0 0 0 0 0 0 0 0 budget loaded inherited
    values before fourth memo branch
  obtain ⟨rfl, rfl, _sameFourth, rfl⟩ := SourceCurrentAllocatedLocalWorkerStability.reduce_done_unique done immediate
  exact ⟨next, final, requests, actual, reads, receipt, SourceCurrentAllocatedLocalWorkerCompletion.reduce_complete actual,
    finalNative, finalOutput, finalProfiles, trace,
    Nat.eq_zero_of_le_zero (by simpa only [SourceCurrentAllocatedFiniteOrdinaryLocalResources.nodeBudget, branch] using nodes),
    Nat.eq_zero_of_le_zero (by simpa only [SourceCurrentAllocatedFiniteOrdinaryLocalResources.edgeBudget, branch] using edges)⟩

end MicroCFTA.LocalParentResourceChecks

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
#print axioms MicroCFTA.LocalParentResourceChecks.constructed_unchanged
#check @MicroCFTA.LocalParentResourceChecks.constructed_unchanged
#print axioms MicroCFTA.LocalParentResourceChecks.constructed_emptyChildren
#check @MicroCFTA.LocalParentResourceChecks.constructed_emptyChildren
