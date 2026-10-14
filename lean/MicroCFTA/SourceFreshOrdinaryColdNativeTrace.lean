import MicroCFTA.SourceFreshOrdinaryColdNativeTable

/-!
# Exact native compiler invariants for every actual cold trace

All successful cold traces have the same rows and final cache. The derived
finite traversal therefore supplies ready memos and complete row metadata
for every actual completed trace, without a final heap premise.
-/
namespace MicroCFTA.SourceFreshOrdinaryColdSharedRows
open Cache InternedConstructorTemplates
open SourceColdSharedRows (Rows)

/-- All actual successful bounds and traces produce identical rows and constructor caches. -/
theorem Trace.unique [DecidableEq (EdgeKey Symbol Guard)]
    {state firstFinal secondFinal : State Symbol Guard} {seen firstRows secondRows : Rows Symbol Guard}
    {pending : List (Value Symbol Guard)} (first : Trace state seen pending firstRows firstFinal)
    (second : Trace state seen pending secondRows secondFinal) : firstRows = secondRows ∧ firstFinal = secondFinal := by
  obtain ⟨firstOuter, firstInner, firstStable⟩ := first.finite
  obtain ⟨secondOuter, secondInner, secondStable⟩ := second.finite
  have firstDone := firstStable (max firstOuter secondOuter) (max firstInner secondInner) (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have secondDone := secondStable (max firstOuter secondOuter) (max firstInner secondInner) (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  exact SourceColdSharedRows.Result.done.inj (firstDone.symm.trans secondDone)

end MicroCFTA.SourceFreshOrdinaryColdSharedRows

namespace MicroCFTA.SourceFreshOrdinaryColdNativeTable
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceColdSharedRows (Rows Supported ResidentRows CoveredRows)
open SourceFreshOrdinaryColdSharedRows (Trace keys ReplayedRows)
open SourceFreshOrdinaryNativeCallback (Ready)

/-- Every actual completed cold trace has all derived next-call and finite-table invariants. -/
theorem for_trace [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) (ready : Ready emptyGuard conjoin state)
    (value : Value Symbol Guard) (available : Available state.machine.heap value) (valueClosed : value.free = [])
    (rows : Rows Symbol Guard) (final : InternedConstructorTemplates.State Symbol Guard)
    (trace : Trace state.machine.heap (fun _ => none) [value] rows final) :
    let after := advance state ⟨final, state.machine.domains⟩
    Ready emptyGuard conjoin after ∧ after.nodes = state.nodes ∧ after.edges = state.edges ∧
      Extension state.machine after.machine ∧ Available final value ∧ Supported rows value ∧
      ResidentRows final rows ∧ ReplayedRows final rows ∧ CoveredRows rows rows ∧
      (keys final rows).Nodup ∧ (∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys final rows) ∧
      SourceDenseRowsRestrict.Closed (SourceColdSharedRows.table rows (keys final rows) value) ∧
      SourceFreshOrdinaryNativeKeyScan.Invariant emptyGuard conjoin final after := by
  obtain ⟨actualRows, actualFinal, _, _, actual, _, facts⟩ := collect emptyGuard conjoin state ready value available valueClosed
  obtain ⟨rfl, rfl⟩ := trace.unique actual
  exact facts

end MicroCFTA.SourceFreshOrdinaryColdNativeTable
