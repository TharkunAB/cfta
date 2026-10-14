import MicroCFTA.SourceFreshOrdinaryColdProductivity
import MicroCFTA.SourceRecursiveIntersectionThunkEffects

/-!
# Actual cold callbacks retain native memo state

Root exposure and row collection extend only the constructor cache.
Advancing the source machine keeps both native memo tables and all their
checked completion provenance. The next callback uses that exact cache.
-/
namespace MicroCFTA.SourceFreshOrdinaryColdMemoState
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceFreshOrdinaryColdSharedRows (Trace keys)
open SourcePreparedSharedRows (encode)

/-- Actual precheck and row extraction retain valid native memos and every heap needed by the next callback. -/
theorem prechecked_advance [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
    (semantic : SemanticHeap state.machine.heap) (covered : Covered [] state.machine.heap)
    (heap : InternedOpenDepthReadback.Heap state.machine.heap) (guarded : InternedGuardedProbeHeap.Heap state.machine.heap)
    (budgetHeap : InternedGuardedBudgetProbeHeap.Heap state.machine.heap)
    (value : Value Symbol Guard) (available : Available state.machine.heap value) (closed : value.free = []) :
    ∃ readFuel edges exposed rows final outer inner,
      MergedFreshOrdinaryExposure.nodeEdges readFuel value state.machine.heap = .done edges exposed ∧
      (∀ extra, MergedFreshOrdinaryExposure.nodeEdges (readFuel + extra) value state.machine.heap = .done edges exposed) ∧
      Trace exposed (fun _ => none) [value] rows final ∧
      (∀ largerOuter largerInner, outer ≤ largerOuter → inner ≤ largerInner →
        SourceFreshOrdinaryColdSharedRows.collect largerOuter largerInner exposed (fun _ => none) [value] = .done rows final) ∧
      (let after := advance state ⟨final, state.machine.domains⟩
       SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin after ∧
       after.nodes = state.nodes ∧ after.edges = state.edges ∧
       SemanticHeap after.machine.heap ∧ Covered [] after.machine.heap ∧ InternedOpenDepthReadback.Heap after.machine.heap ∧
       InternedGuardedProbeHeap.Heap after.machine.heap ∧ InternedGuardedBudgetProbeHeap.Heap after.machine.heap ∧
       Extension state.machine after.machine) ∧
      ∀ ambient,
        (if edges.isEmpty then false else
          (SourceRowsMinimumAdapter.minimumSizes (SourceColdSharedRows.table rows (keys final rows) value) (encode value)).isSome) = true ↔
          ∃ term, InternedGuardedLanguage.meaning (fun _ _ => true) ambient value term := by
  obtain ⟨readFuel, edges, exposed, rows, final, outer, inner, read, readStable, trace, stable,
      finalSemantic, finalCovered, finalHeap, finalGuarded, finalBudget, growth, history, _, callback⟩ :=
    SourceFreshOrdinaryColdProductivity.prechecked_table state.machine.heap semantic covered heap guarded budgetHeap value available closed
  have extension : Extension state.machine ⟨final, state.machine.domains⟩ := ⟨growth, history, extends_refl _⟩
  have finalValid : SourceRecursiveIntersectionKernel.Valid (⟨final, state.machine.domains⟩ : Machine Symbol Guard) :=
    ⟨finalSemantic.1.normal.facts, valid.machine.2⟩
  refine ⟨readFuel, edges, exposed, rows, final, outer, inner, read, readStable, trace, stable, ?_, callback⟩
  exact ⟨advance_valid width emptyGuard conjoin state valid _ finalValid extension, rfl, rfl,
    finalSemantic, finalCovered, finalHeap, finalGuarded, finalBudget, extension⟩

end MicroCFTA.SourceFreshOrdinaryColdMemoState
