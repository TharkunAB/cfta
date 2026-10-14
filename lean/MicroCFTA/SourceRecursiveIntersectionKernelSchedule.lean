import MicroCFTA.SourceRecursiveIntersectionScheduleStep

/-!
# Complete bounded kernel execution matches the semantic schedule

Completed calls replay in their final cache. Induction on the actual kernel
bound keeps that cache fixed. Twice the bound includes the extra semantic
edge level. Actual growth then recovers the original input view.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache Language Binding InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionCode (NodeScope)
open SourceRecursiveIntersectionInputView (view inputOf OriginalInput)
open SourceRecursiveIntersectionScheduleConstructors (Corresponds)
open SourceRecursiveIntersectionScheduleEnvironment (Ordered)

/-- Full actual kernel execution derives semantic correspondence in one final replay cache. -/
theorem execute_schedule_replay [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (state : Machine Symbol Guard) (valid : Valid state)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap state.heap) (guarded : InternedGuardedProbeHeap.Heap state.heap)
    (holds : Guard → Term Symbol → Bool)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term)) :
    ScheduleCalls (execute emptyGuard conjoin fuel) state holds (2 * fuel) := by
  induction fuel with
  | zero =>
      intro domain left right known scope ordered value done
      cases done
  | succ fuel ih =>
      intro domain left right known scope ordered value done
      have completed : onNode emptyGuard conjoin (execute emptyGuard conjoin fuel) domain left right state = .done value state := done
      have actual := onNode_schedule emptyGuard conjoin _ (execute_checked emptyGuard conjoin fuel)
        (execute_replay emptyGuard conjoin fuel) (SourceRecursiveIntersectionScopeCalls.execute_scoped emptyGuard conjoin fuel)
        state valid semantic guarded holds conjoined (2 * fuel) ih domain left right known scope ordered value completed
      simpa only [Nat.mul_add, Nat.mul_one] using actual

/-- Actual completed kernel calls have the same bounded result and language as the original input schedule. -/
theorem execute_schedule [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (before after : Machine Symbol Guard) (valid : Valid before)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap after.heap) (guarded : InternedGuardedProbeHeap.Heap after.heap)
    (holds : Guard → Term Symbol → Bool)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (domain : Interned DomainKey) (left right : Value Symbol Guard) (known : Domain before domain)
    (scope : NodeScope before.heap ⟨domain, left, right⟩) (ordered : Ordered domain.key.seen)
    (value : Value Symbol Guard) (done : execute emptyGuard conjoin fuel domain left right before = .done value after) :
    ∃ shape, IntersectSchedule.run (view before.heap holds) (2 * fuel) (SourceRecursiveIntersectionSchedule.domain domain.key)
      (inputOf left) (inputOf right) = .ok shape ∧ Corresponds holds value shape := by
  have checked := execute_checked emptyGuard conjoin fuel domain left right before valid known scope.leftAvailable scope.rightAvailable
  have afterValid : Valid after := by simpa only [done, Result.state] using checked.valid
  have growth : Extension before after := by simpa only [done, Result.state] using checked.extension
  have replayed := execute_replay emptyGuard conjoin fuel domain left right before after value after valid known
    scope.leftAvailable scope.rightAvailable done (.refl _)
  obtain ⟨shape, completed, meaning⟩ := execute_schedule_replay emptyGuard conjoin fuel after afterValid semantic guarded holds conjoined
    domain left right (known.grows domain growth) (schedule_scope_grows before after growth _ scope) ordered value replayed
  rw [SourceRecursiveIntersectionInputView.run_grows before.heap after.heap valid.1 afterValid.1 growth.heap growth.history holds (2 * fuel)
    (SourceRecursiveIntersectionSchedule.domain domain.key)
    ((SourceRecursiveIntersectionInputView.domain_inputs_iff before.heap domain.key).mpr scope.bindings)
    (inputOf left) (inputOf right) ⟨left, scope.left, scope.leftAvailable, scope.left.codec left⟩
    ⟨right, scope.right, scope.rightAvailable, scope.right.codec right⟩] at completed
  exact ⟨shape, completed, meaning⟩

end MicroCFTA.SourceRecursiveIntersectionKernel
