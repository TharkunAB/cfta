import MicroCFTA.SourceFreshOrdinaryNativeCallback
import MicroCFTA.SourceFreshOrdinaryNativeKeyScan
import MicroCFTA.SourceFreshOrdinaryColdClosed

/-!
# Native compiler state after actual cold traversal

The finite cold worklist supplies the compiler's row metadata and final
constructor cache. Advancing the native state retains both memo tables.
The resulting state supplies every invariant for the first overlap query.
-/
namespace MicroCFTA.SourceFreshOrdinaryColdNativeTable
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceColdSharedRows (Rows Supported ResidentRows CoveredRows)
open SourceFreshOrdinaryColdSharedRows (Trace keys ReplayedRows)
open SourceFreshOrdinaryNativeCallback (Ready)

/-- Actual closed construction supplies a ready initial native cache and the closed available root. -/
theorem constructed [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (expression : InternedNestedConstruction.Syntax Symbol Guard) (value : Value Symbol Guard)
    (source : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value source)
    (domains : Cache.State DomainKey) (domainsValid : Cache.Valid domains)
    (width : Nat) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) :
    Ready emptyGuard conjoin (initial width ⟨source, domains⟩) ∧ Available source value ∧ value.free = [] := by
  have semantic := SourceRecursiveIntersectionSemanticHeap.constructed expression value source built
  have depth : InternedOpenDepthReadback.Heap source := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using InternedOpenDepthExecution.closed_heap expression
  have guarded : InternedGuardedProbeHeap.Heap source := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using InternedGuardedExecution.closed_heap expression
  have budget : InternedGuardedBudgetProbeHeap.Heap source := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using InternedGuardedBudgetExecution.closed_heap expression
  exact ⟨⟨initial_valid width emptyGuard conjoin _ ⟨semantic.1.normal.facts, domainsValid⟩,
    SourceRecursiveIntersectionNative.idle_initial _, semantic,
    InternedFreshOrdinaryCoverage.closed_covered expression value source built, depth, guarded, budget⟩,
    (InternedFreshOrdinaryFacts.closed_verified expression).result value source built,
    InternedFreshOrdinarySourceFreeNames.closed_free_empty expression value source built⟩

/-- Actual finite row collection retains ready native memos and derives all input-table metadata. -/
theorem collect [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (ready : Ready emptyGuard conjoin state)
    (value : Value Symbol Guard) (available : Available state.machine.heap value) (closed : value.free = []) :
    ∃ rows final outer inner, Trace state.machine.heap (fun _ => none) [value] rows final ∧
      (∀ largerOuter largerInner, outer ≤ largerOuter → inner ≤ largerInner →
        SourceFreshOrdinaryColdSharedRows.collect largerOuter largerInner state.machine.heap (fun _ => none) [value] = .done rows final) ∧
      (let after := advance state ⟨final, state.machine.domains⟩
       Ready emptyGuard conjoin after ∧ after.nodes = state.nodes ∧ after.edges = state.edges ∧
       Extension state.machine after.machine ∧ Available final value ∧ Supported rows value ∧
       ResidentRows final rows ∧ ReplayedRows final rows ∧ CoveredRows rows rows ∧
       (keys final rows).Nodup ∧ (∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys final rows) ∧
       SourceDenseRowsRestrict.Closed (SourceColdSharedRows.table rows (keys final rows) value) ∧
       SourceFreshOrdinaryNativeKeyScan.Invariant emptyGuard conjoin final after) := by
  obtain ⟨rows, final, outer, inner, trace, semantic, covered, depth, growth, history,
      resident, replayed, children, distinct, domain, stable⟩ :=
    SourceFreshOrdinaryColdSharedRows.cold_table state.machine.heap ready.semantic ready.covered ready.openDepth value available closed
  have inputs : SourceColdSharedRows.Inputs state.machine.heap [value] := by
    intro child member
    simpa only [List.mem_singleton.mp member] using And.intro available closed
  have extension : Extension state.machine ⟨final, state.machine.domains⟩ := ⟨growth, history, extends_refl _⟩
  have machineValid : SourceRecursiveIntersectionKernel.Valid (⟨final, state.machine.domains⟩ : Machine Symbol Guard) :=
    ⟨semantic.1.normal.facts, ready.valid.machine.2⟩
  have afterReady : Ready emptyGuard conjoin (advance state ⟨final, state.machine.domains⟩) :=
    ⟨advance_valid width emptyGuard conjoin state ready.valid _ machineValid extension,
      ready.idle.advance state _, semantic, covered, depth,
      trace.guarded_heap ready.semantic ready.covered ready.guarded inputs,
      trace.budget_heap ready.semantic ready.covered ready.budget inputs⟩
  refine ⟨rows, final, outer, inner, trace, stable, afterReady, rfl, rfl, extension,
    available.grows state.machine.heap final growth history, ?_, resident, replayed, children,
    distinct, domain, SourceFreshOrdinaryColdClosed.table_closed final semantic covered rows replayed resident children
      (keys final rows) domain value, afterReady, grows_refl _, extends_refl _⟩
  exact fun identity same => trace.pending_done value List.mem_cons_self identity same

end MicroCFTA.SourceFreshOrdinaryColdNativeTable
