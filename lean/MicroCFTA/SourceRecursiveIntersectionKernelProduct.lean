import MicroCFTA.SourceRecursiveIntersectionKernelSchedule

/-!
# Actual completed source intersection has exact product language

The bounded kernel theorem derives the reference syntax and its language.
Finite exact original-input schedules identify that syntax result. Closed
actual source and result records make the final equation independent of
the reference environment. No product-language contract is supplied.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache Language Binding InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionInputView (view inputOf Original)

/-- Actual completed closed original intersection accepts exactly the common guarded finite terms. -/
theorem execute_product [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (before after : Machine Symbol Guard) (valid : Valid before)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap before.heap) (guarded : InternedGuardedProbeHeap.Heap after.heap)
    (holds : Guard → Term Symbol → Bool)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available before.heap left) (rightAvailable : Available before.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (value : Value Symbol Guard)
    (done : execute emptyGuard conjoin fuel IntersectionEmptyDomain.emptyDomain left right before = .done value after)
    (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol) :
    InternedGuardedLanguage.meaning holds ambient value term ↔
      InternedGuardedLanguage.meaning holds ambient left term ∧ InternedGuardedLanguage.meaning holds ambient right term := by
  have checked := execute_checked emptyGuard conjoin fuel IntersectionEmptyDomain.emptyDomain left right before valid
    (empty_domain before) leftAvailable rightAvailable
  have afterValid : Valid after := by simpa only [done, Result.state] using checked.valid
  have valueAvailable := checked.result value after done
  have observed := SourceRecursiveIntersectionScopeCalls.execute_scoped emptyGuard conjoin fuel IntersectionEmptyDomain.emptyDomain
    left right before valid (empty_domain before) leftAvailable rightAvailable semantic value after done
  have valueClosed := SourceRecursiveIntersectionResultScope.empty_scope value observed.2
  obtain ⟨shape, scheduled, correspondence⟩ := execute_schedule emptyGuard conjoin fuel before after valid observed.1 guarded holds conjoined
    IntersectionEmptyDomain.emptyDomain left right (empty_domain before)
    (SourceRecursiveIntersectionCode.initial_scope before.heap left right leftOriginal rightOriginal leftAvailable rightAvailable)
    SourceRecursiveIntersectionScheduleEnvironment.ordered_empty value done
  obtain ⟨bound, reference, completed, exactLanguage⟩ := SourceRecursiveIntersectionInputView.source_schedule_total before.heap valid.1 holds
    left right leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed
  have stable := IntersectSchedule.run_stable (view before.heap holds) (2 * fuel) (max bound (2 * fuel)) (by omega)
    {} (inputOf left) (inputOf right) shape scheduled
  have same : shape = reference := Except.ok.inj (stable.symm.trans (completed (max bound (2 * fuel)) (by omega)))
  subst reference
  have encodedExact (environment : BinderLanguage.Env Symbol) :
      InternedGuardedLanguage.meaning holds (SourceRecursiveIntersectionScheduleEnvironment.environment environment) value term ↔
        InternedGuardedLanguage.meaning holds (SourceRecursiveIntersectionScheduleEnvironment.environment environment) left term ∧
        InternedGuardedLanguage.meaning holds (SourceRecursiveIntersectionScheduleEnvironment.environment environment) right term := by
    rw [correspondence environment, exactLanguage environment term,
      ← SourceRecursiveIntersectionInputView.closed_copy_corresponds holds left leftOriginal before.heap valid.1 leftAvailable leftClosed environment,
      ← SourceRecursiveIntersectionInputView.closed_copy_corresponds holds right rightOriginal before.heap valid.1 rightAvailable rightClosed environment]
  let environment : BinderLanguage.Env Symbol := fun _ _ => False
  let encoded := SourceRecursiveIntersectionScheduleEnvironment.environment environment
  have outputSame := InternedGuardedLanguage.meaning_free holds value after.heap afterValid.1.coherent valueAvailable ambient encoded (by
    intro name member; rw [valueClosed] at member; cases member)
  have leftSame := InternedGuardedLanguage.meaning_free holds left before.heap valid.1.coherent leftAvailable ambient encoded (by
    intro name member; rw [leftClosed] at member; cases member)
  have rightSame := InternedGuardedLanguage.meaning_free holds right before.heap valid.1.coherent rightAvailable ambient encoded (by
    intro name member; rw [rightClosed] at member; cases member)
  rw [outputSame, leftSame, rightSame]
  exact encodedExact environment

end MicroCFTA.SourceRecursiveIntersectionKernel
