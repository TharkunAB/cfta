import MicroCFTA.SourceEqualityPhysicalClassEntry
import MicroCFTA.SourceEqualityPartialPrecheckAllocation
import MicroCFTA.SourceEqualityConstraintFieldLookup

/-!
# Current class scans after the actual allocated accessor prefix

The original field lookup is read-only. Its successful receipt derives the
stored value and constructor readback. Actual accessor and precheck calls
then derive the physical entry and preserve the equality-operation tables.
The reached scan uses that derived entry. Original interner coverage and
initial native invariants remain explicit. No missing field is allocated
at the lookup site.
-/
namespace MicroCFTA.SourceCurrentClassAllocatedEntry
open Cache Language EqualityNormalize SourceEqualityClassOrder
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityNativeScoped
open SourceCurrentEqualityClassScan SourceCurrentClassScanGlobalMemos
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "FieldHeap" => SourceEqualityNativeDemandFieldHeap.Heap
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "Stored" => SourceEqualityConstraintAllocation.Value
local notation "prefix" => SourceEqualityPartialPrecheckAllocation.run

/-- Actual read-only lookup and allocated precheck derive the physical entry and retained operation tables. -/
theorem prefix_entry (original : Guard) (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (before : Operations) (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (loaded : Allocated)
    (found : SourceEqualityConstraintFieldLookup.load original before.constraints = .ok (some loaded))
    (inherited : Stored) (inheritedReady : SourceEqualityConstraintAllocation.Ready before.constraints inherited)
    (output : List Record) (done : (prefix loaded.stored loaded.guard inherited before).1 = .ok (.classes output)) :
    SourceEqualityPhysicalClassEntry.entry original inherited.payload = .ok (.classes output) ∧
      SourceEqualityConstraintMemoAllocation.Valid (prefix loaded.stored loaded.guard inherited before).2 ∧
      SourceEqualityConstraintMemoAllocation.Grows before (prefix loaded.stored loaded.guard inherited before).2 := by
  have loadedReady := SourceEqualityConstraintFieldLookup.load_ready original before.constraints valid.constraints cached loaded found
  have originalRead := SourceEqualityConstraintFieldLookup.load_constructor_receipt original before.constraints cached loaded found
  obtain ⟨own, branch, ownRead, actual, checked, afterValid, growth⟩ :=
    SourceEqualityPartialPrecheckAllocation.run_correct loaded.stored loaded.guard inherited before valid
      loadedReady.1 inheritedReady original.equalities cached originalRead
  have same : branch = .classes output := Except.ok.inj (actual.symm.trans done)
  subst branch
  have guardEq : loaded.guard = original.guard := congrArg (fun constraint : Guard => constraint.guard) loadedReady.2
  have computed : SourceEqualityPhysicalPayload.own original = .ok own.payload := by
    simpa only [guardEq] using ownRead
  exact ⟨(SourceEqualityPhysicalClassEntry.entry_of_own original inherited.payload own.payload computed).trans checked,
    afterValid, growth⟩

/-- The actual allocation prefix and reached scan derive both operation and global memo invariants. -/
theorem scan_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (original : Guard) (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (operations : Operations) (operationsValid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (loaded : Allocated)
    (found : SourceEqualityConstraintFieldLookup.load original operations.constraints = .ok (some loaded))
    (inherited : Stored) (inheritedReady : SourceEqualityConstraintAllocation.Ready operations.constraints inherited)
    (output : List Record) (done : (prefix loaded.stored loaded.guard inherited operations).1 = .ok (.classes output))
    {values : List (Value Symbol Guard)} {selected : Constraints} {outcome : Option Class}
    {before after : Native width Symbol Guard} {memo saved : Memo}
    (trace : Scan source reaches values (output.map Record.paths) before memo outcome selected after saved)
    (ready : IdleReady top conjoin before) (available : Values before.machine.heap values)
    (costs : CostHeap before.machine.heap) (fields : FieldHeap before.machine.heap)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.machine.heap memo)
    (memos : Memos) (valid : Valid before.machine.heap memos) :
    SourceEqualityConstraintMemoAllocation.Valid (prefix loaded.stored loaded.guard inherited operations).2 ∧
      SourceEqualityConstraintMemoAllocation.Grows operations (prefix loaded.stored loaded.guard inherited operations).2 ∧
      ∃ final, ScanReads trace memos final ∧ Valid after.machine.heap final ∧
        IdleReady top conjoin after ∧ CostHeap after.machine.heap ∧ FieldHeap after.machine.heap ∧
        Keeps before.machine.heap after.machine.heap ∧ Values after.machine.heap values ∧
        SourceCurrentEmptinessMemo.Correct formulas solver after.machine.heap saved ∧
        SourceCurrentEmptinessMemo.Extends memo saved := by
  obtain ⟨live, afterValid, growth⟩ := prefix_entry original cached operations operationsValid loaded found inherited inheritedReady output done
  exact ⟨afterValid, growth, SourceEqualityPhysicalClassEntry.live_memos original cached inherited.payload output live
    trace ready available costs fields formulas solver correct memos valid⟩

end MicroCFTA.SourceCurrentClassAllocatedEntry
