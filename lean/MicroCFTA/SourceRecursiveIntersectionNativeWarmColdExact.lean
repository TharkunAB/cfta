import MicroCFTA.SourceRecursiveIntersectionNativeColdExact

/-!
# Exact finite cold tables after completed warm native calls

Actual completed calls can start with populated native memo tables.
Their checked evaluation retains coverage and all three semantic heaps.
The returned closed value has a finite repaired table in its final cache.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceColdSharedRows (ResidentRows CoveredRows)
open SourceFreshOrdinaryColdSharedRows (Trace ReplayedRows keys)

/-- Any completed checked native request supplies a finite exact cold table, including warm memo states. -/
theorem done_node_table_exact [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (left right : Value Symbol Guard) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (value : Value Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
    (leftAvailable : Available state.machine.heap left) (rightAvailable : Available state.machine.heap right)
    (semantic : SemanticHeap state.machine.heap) (covered : Covered [] state.machine.heap)
    (heap : InternedOpenDepthReadback.Heap state.machine.heap) (guarded : InternedGuardedProbeHeap.Heap state.machine.heap)
    (budgetHeap : InternedGuardedBudgetProbeHeap.Heap state.machine.heap)
    (done : execute emptyGuard conjoin fuel (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure) state = .done value after)
    (ranges : WordRanges emptyGuard conjoin (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure) state) :
    ∃ rows final outer inner,
      value.free = [] ∧ SourceRecursiveIntersectionInputView.Original value ∧
      Trace after.machine.heap (fun _ => none) [value] rows final ∧
      SemanticHeap final ∧ Covered [] final ∧ InternedOpenDepthReadback.Heap final ∧
      InternedGuardedProbeHeap.Heap final ∧ InternedGuardedBudgetProbeHeap.Heap final ∧
      Grows after.machine.heap final ∧ Extends after.machine.heap.nodes.issued final.nodes.issued ∧
      ResidentRows final rows ∧ ReplayedRows final rows ∧ CoveredRows rows rows ∧
      (keys final rows).Nodup ∧
      (∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys final rows) ∧
      (∀ largerOuter largerInner, outer ≤ largerOuter → inner ≤ largerInner →
        SourceFreshOrdinaryColdSharedRows.collect largerOuter largerInner after.machine.heap (fun _ => none) [value] = .done rows final) ∧
      ∀ meaning ambient term, Accepts (FTAValidation.rowFor (SourceInternedRows.interpretedRows meaning
        (SourceColdSharedRows.table rows (keys final rows) value))) (SourcePreparedSharedRows.encode value) term ↔
        InternedGuardedLanguage.meaning meaning ambient value term := by
  have ready : NodeReady state.machine ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ :=
    ⟨empty_domain state.machine, leftAvailable, rightAvailable⟩
  have evaluated := evaluation_of_done emptyGuard conjoin fuel _ state after value done
  have bounds := evaluated.bounds_of_ranges ranges
  have correct := bounds.correct (fun current value => Available current.heap value) (by intro value; trivial)
    (safe_requestNode _ left right _ ready) valid
  have certificate := semantic_requestNode IntersectionEmptyDomain.emptyDomain left right state.machine ready
  have retained := bounds.guarded_heaps (fun current value => Available current.heap value)
    (by intro value; trivial) (safe_requestNode _ left right _ ready) valid certificate semantic (by intro value; trivial) guarded
  have openRetained := bounds.open_depth_heaps (fun current value => Available current.heap value)
    (by intro value; trivial) (safe_requestNode _ left right _ ready) valid certificate semantic (by intro value; trivial) heap
  have budgetRetained := bounds.budget_heaps (fun current value => Available current.heap value)
    (by intro value; trivial) (safe_requestNode _ left right _ ready) valid certificate semantic (by intro value; trivial) budgetHeap
  obtain ⟨steps, _, nativeTrace⟩ := done_trace emptyGuard conjoin fuel _ state after value done
  have afterCovered := (nativeTrace.covered emptyGuard conjoin steps _ _ state after semantic.1.normal.facts.coherent.valid covered).2
  have scope := correct.meaning.request_scope _ _ _ _ valid.machine ready semantic
  have closed := SourceRecursiveIntersectionResultScope.empty_scope value scope
  obtain ⟨rows, final, outer, inner, trace, finalSemantic, finalCovered, finalHeap, growth, history,
      resident, replayed, allChildren, distinct, domain, stable⟩ :=
    SourceFreshOrdinaryColdSharedRows.cold_table after.machine.heap retained.1 afterCovered openRetained.2 value correct.result closed
  have inputs : SourceColdSharedRows.Inputs after.machine.heap [value] := by
    intro child member
    simpa only [List.mem_singleton.mp member] using And.intro correct.result closed
  refine ⟨rows, final, outer, inner, closed, correct.closed_original closed, trace, finalSemantic, finalCovered, finalHeap,
    trace.guarded_heap retained.1 afterCovered retained.2 inputs,
    trace.budget_heap retained.1 afterCovered budgetRetained.2 inputs, growth, history,
    resident, replayed, allChildren, distinct, domain, stable, ?_⟩
  intro meaning ambient term
  exact SourceFreshOrdinaryColdGuardedExact.trace_table_exact after.machine.heap final value rows trace retained.1 afterCovered
    retained.2 budgetRetained.2 correct.result closed (keys final rows) domain meaning ambient term

end MicroCFTA.SourceRecursiveIntersectionNative
