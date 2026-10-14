import MicroCFTA.SourceRecursiveIntersectionNativeProduct
import MicroCFTA.SourceRecursiveIntersectionNativeColdExact

/-!
# Finite actual native cold tables have exact original product language

Actual first-run completion and repaired traversal supply a finite stable
table. Its independent returned-value language is the derived product of
the original inputs. No row relation or product-language contract is used.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView (Original)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceFreshOrdinaryColdSharedRows (Trace keys)

/-- Actual native execution and finite cold extraction accept exactly the common original terms. -/
theorem cold_node_table_product [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (semantic : SemanticHeap source) (covered : Covered [] source)
    (heap : InternedOpenDepthReadback.Heap source) (guarded : InternedGuardedProbeHeap.Heap source)
    (budgetHeap : InternedGuardedBudgetProbeHeap.Heap source) (domains : Cache.State DomainKey) (domainsValid : Cache.Valid domains)
    (holds : Guard → Term Symbol → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
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
      ∀ meaning, (∀ first second term, meaning (conjoin first second) term = (meaning first term && meaning second term)) →
        ∀ ambient term, Language.Accepts (FTAValidation.rowFor (SourceInternedRows.interpretedRows meaning
          (SourceColdSharedRows.table rows (keys final rows) value))) (SourcePreparedSharedRows.encode value) term ↔
          InternedGuardedLanguage.meaning meaning ambient left term ∧ InternedGuardedLanguage.meaning meaning ambient right term := by
  obtain ⟨fuel, value, after, rows, final, outer, inner, done, closed, original, trace, guardedFinal, budgetFinal, stable, rowStable, exactResult⟩ :=
    cold_node_table_exact source semantic covered heap guarded budgetHeap domains domainsValid holds emptyGuard conjoin left right
      leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed ranges
  have valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin (initial width ⟨source, domains⟩) :=
    initial_valid width emptyGuard conjoin _ ⟨semantic.1.normal.facts, domainsValid⟩
  refine ⟨fuel, value, after, rows, final, outer, inner, done, closed, original, trace, guardedFinal, budgetFinal, stable, rowStable, ?_⟩
  intro meaning conjoined ambient term
  exact (exactResult meaning ambient term).trans (native_product emptyGuard conjoin fuel left right _ after value valid
    leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed semantic guarded done ranges meaning conjoined ambient term)

/-- Completed repaired source construction supplies all heaps for finite exact native product tables. -/
theorem constructed_node_table_product [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (expression : InternedNestedConstruction.Syntax Symbol Guard) (builtValue : Value Symbol Guard)
    (source : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done builtValue source)
    (domains : Cache.State DomainKey) (domainsValid : Cache.Valid domains)
    (holds : Guard → Term Symbol → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
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
      ∀ meaning, (∀ first second term, meaning (conjoin first second) term = (meaning first term && meaning second term)) →
        ∀ ambient term, Language.Accepts (FTAValidation.rowFor (SourceInternedRows.interpretedRows meaning
          (SourceColdSharedRows.table rows (keys final rows) value))) (SourcePreparedSharedRows.encode value) term ↔
          InternedGuardedLanguage.meaning meaning ambient left term ∧ InternedGuardedLanguage.meaning meaning ambient right term := by
  have semantic := SourceRecursiveIntersectionSemanticHeap.constructed expression builtValue source built
  have covered := InternedFreshOrdinaryCoverage.closed_covered expression builtValue source built
  have heap : InternedOpenDepthReadback.Heap source := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using InternedOpenDepthExecution.closed_heap expression
  have guarded : InternedGuardedProbeHeap.Heap source := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using InternedGuardedExecution.closed_heap expression
  have budgetHeap : InternedGuardedBudgetProbeHeap.Heap source := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using InternedGuardedBudgetExecution.closed_heap expression
  exact cold_node_table_product source semantic covered heap guarded budgetHeap domains domainsValid holds emptyGuard conjoin left right
    leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed ranges

end MicroCFTA.SourceRecursiveIntersectionNative
