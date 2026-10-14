import MicroCFTA.SourceRecursiveIntersectionNativeColdTable
import MicroCFTA.SourceRecursiveIntersectionNativeGuardedHeap
import MicroCFTA.SourceFreshOrdinaryColdGuardedExact
import MicroCFTA.SourceRecursiveIntersectionNativeBudgetHeap

/-!
# Exact independent language of actual native cold tables

Actual native execution retains both semantic probe heaps. Its finite final
cold table has exactly the independent language of the returned physical
value. The input intersection law remains a separate obligation.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView (Original)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceFreshOrdinaryColdSharedRows (Trace keys)

/-- The actual first native run has a finite stable cold table with its exact returned independent language. -/
theorem cold_node_table_exact [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (semantic : SemanticHeap source) (covered : Covered [] source)
    (heap : InternedOpenDepthReadback.Heap source) (guarded : InternedGuardedProbeHeap.Heap source)
    (budgetHeap : InternedGuardedBudgetProbeHeap.Heap source) (domains : Cache.State DomainKey) (domainsValid : Cache.Valid domains)
    (holds : Guard → Language.Term Symbol → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (ranges : WordRanges emptyGuard conjoin (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)
      (initial width ⟨source, domains⟩)) :
    ∃ fuel value after rows final outer inner,
      execute emptyGuard conjoin fuel (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)
        (initial width ⟨source, domains⟩) = .done value after ∧
      value.free = [] ∧ Original value ∧ Trace after.machine.heap (fun _ => none) [value] rows final ∧
      InternedGuardedProbeHeap.Heap final ∧ InternedGuardedBudgetProbeHeap.Heap final ∧
      (∀ extra, execute emptyGuard conjoin (fuel + extra) (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)
        (initial width ⟨source, domains⟩) = .done value after) ∧
      (∀ largerOuter largerInner, outer ≤ largerOuter → inner ≤ largerInner →
        SourceFreshOrdinaryColdSharedRows.collect largerOuter largerInner after.machine.heap (fun _ => none) [value] = .done rows final) ∧
      ∀ meaning ambient term, Language.Accepts (FTAValidation.rowFor (SourceInternedRows.interpretedRows meaning
        (SourceColdSharedRows.table rows (keys final rows) value))) (SourcePreparedSharedRows.encode value) term ↔
        InternedGuardedLanguage.meaning meaning ambient value term := by
  obtain ⟨fuel, value, after, rows, final, outer, inner, done, correct, closed, original, trace,
      _, _, _, _, _, _, domain, stable, rowStable, _⟩ :=
    cold_node_table source semantic covered heap domains domainsValid holds emptyGuard conjoin left right
      leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed ranges
  have ready : NodeReady (⟨source, domains⟩ : Machine Symbol Guard) ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ :=
    ⟨empty_domain _, leftAvailable, rightAvailable⟩
  have valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin (initial width ⟨source, domains⟩) :=
    initial_valid width emptyGuard conjoin _ ⟨semantic.1.normal.facts, domainsValid⟩
  have evaluated := evaluation_of_done emptyGuard conjoin fuel _ _ after value done
  have bounds := evaluated.bounds_of_ranges ranges
  have retained := bounds.guarded_heaps (fun current value => Available current.heap value)
    (by intro value; trivial) (safe_requestNode _ left right _ ready) valid
    (semantic_requestNode _ left right _ ready) semantic (by intro value; trivial) guarded
  have budgetRetained := bounds.budget_heaps (fun current value => Available current.heap value)
    (by intro value; trivial) (safe_requestNode _ left right _ ready) valid
    (semantic_requestNode _ left right _ ready) semantic (by intro value; trivial) budgetHeap
  obtain ⟨steps, _, nativeTrace⟩ := done_trace emptyGuard conjoin fuel _ (initial width ⟨source, domains⟩) after value done
  have afterCovered := (nativeTrace.covered emptyGuard conjoin steps _ _ (initial width ⟨source, domains⟩) after
    semantic.1.normal.facts.coherent.valid covered).2
  have inputs : SourceColdSharedRows.Inputs after.machine.heap [value] := by
    intro child member; simpa only [List.mem_singleton.mp member] using And.intro correct.result closed
  refine ⟨fuel, value, after, rows, final, outer, inner, done, closed, original, trace,
    trace.guarded_heap retained.1 afterCovered retained.2 inputs,
    trace.budget_heap retained.1 afterCovered budgetRetained.2 inputs, stable, rowStable, ?_⟩
  intro meaning ambient term
  exact SourceFreshOrdinaryColdGuardedExact.trace_table_exact after.machine.heap final value rows trace retained.1 afterCovered
    retained.2 budgetRetained.2 correct.result closed (keys final rows) domain meaning ambient term

/-- Actual closed source construction supplies both probe heaps for exact native table language. -/
theorem constructed_node_table_exact [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (expression : InternedNestedConstruction.Syntax Symbol Guard) (builtValue : Value Symbol Guard)
    (source : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done builtValue source)
    (domains : Cache.State DomainKey) (domainsValid : Cache.Valid domains)
    (holds : Guard → Language.Term Symbol → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (ranges : WordRanges emptyGuard conjoin (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)
      (initial width ⟨source, domains⟩)) :
    ∃ fuel value after rows final outer inner,
      execute emptyGuard conjoin fuel (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)
        (initial width ⟨source, domains⟩) = .done value after ∧
      value.free = [] ∧ Original value ∧ Trace after.machine.heap (fun _ => none) [value] rows final ∧
      InternedGuardedProbeHeap.Heap final ∧ InternedGuardedBudgetProbeHeap.Heap final ∧
      (∀ extra, execute emptyGuard conjoin (fuel + extra) (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)
        (initial width ⟨source, domains⟩) = .done value after) ∧
      (∀ largerOuter largerInner, outer ≤ largerOuter → inner ≤ largerInner →
        SourceFreshOrdinaryColdSharedRows.collect largerOuter largerInner after.machine.heap (fun _ => none) [value] = .done rows final) ∧
      ∀ meaning ambient term, Language.Accepts (FTAValidation.rowFor (SourceInternedRows.interpretedRows meaning
        (SourceColdSharedRows.table rows (keys final rows) value))) (SourcePreparedSharedRows.encode value) term ↔
        InternedGuardedLanguage.meaning meaning ambient value term := by
  have heap : InternedOpenDepthReadback.Heap source := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using InternedOpenDepthExecution.closed_heap expression
  have guarded : InternedGuardedProbeHeap.Heap source := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using InternedGuardedExecution.closed_heap expression
  have budgetHeap : InternedGuardedBudgetProbeHeap.Heap source := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using InternedGuardedBudgetExecution.closed_heap expression
  exact cold_node_table_exact source (SourceRecursiveIntersectionSemanticHeap.constructed expression builtValue source built)
    (InternedFreshOrdinaryCoverage.closed_covered expression builtValue source built) heap guarded budgetHeap domains domainsValid
    holds emptyGuard conjoin left right leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed ranges

end MicroCFTA.SourceRecursiveIntersectionNative
