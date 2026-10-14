import MicroCFTA.SourceRecursiveIntersectionMuReadback
import MicroCFTA.SourceRecursiveIntersectionKernelScope
import MicroCFTA.SourceRecursiveIntersectionScheduleConstructors

/-!
# Actual Mu branches transport semantic schedule correspondence

A completed source Mu branch derives its original operand identities,
extended domain, and actual body result. Scope follows from the recursive
caller. Any schedule syntax for that body passes through the actual binder.
This is a local induction step, not a complete product-language theorem.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionControl (identity pair)
open SourceRecursiveIntersectionScopeCalls (ScopedCalls)
open SourceRecursiveIntersectionScheduleConstructors (Corresponds)
open SourceRecursiveIntersectionScheduleEnvironment (Ordered)

/-- Actual completed Mu work derives a scope-correct body and transports every semantic body correspondence. -/
theorem mu_schedule_body [DecidableEq (EdgeKey Symbol Guard)]
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (replay : Replays call) (scopes : ScopedCalls call)
    (domain : Interned DomainKey) (left right : Value Symbol Guard) (state after : Machine Symbol Guard)
    (valid : Valid state) (afterValid : Valid after) (known : Domain state domain)
    (leftAvailable : Available state.heap left) (rightAvailable : Available state.heap right)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap after.heap)
    (guarded : InternedGuardedProbeHeap.Heap after.heap) (ordered : Ordered domain.key.seen)
    (value : Value Symbol Guard) (final : Machine Symbol Guard)
    (done : mu call domain left right state = .done value final) (growth : Extension final after) :
    ∃ first second extended bodyValue,
      identity left = some first ∧ identity right = some second ∧
      extended.key = SourceRecursiveIntersectionDomain.extend domain.key
        ((SourceRecursiveIntersectionEnvironment.bindings left right).map Prod.fst) (pair first second) ∧
      Domain after extended ∧ Available after.heap bodyValue ∧
      call extended (body left) (body right) after = .done bodyValue after ∧
      SourceRecursiveIntersectionResultScope.Scope extended.key.seen bodyValue ∧
      ∀ holds shape, Corresponds holds bodyValue shape →
        Corresponds holds value (IntersectSchedule.maybeMu (pair first second) shape) := by
  obtain ⟨first, second, extended, bodyValue, firstId, secondId, key, extendedKnown, available, entered, returned, built⟩ :=
    mu_body_replay call calls replay domain left right state after valid known leftAvailable rightAvailable value final done growth
  have checked := mu_checked call calls domain left right state valid known leftAvailable rightAvailable
  have earlier : Extension state final := by simpa only [done, Result.state] using checked.extension
  have total := earlier.trans growth
  have scope := (scopes extended (body left) (body right) after afterValid extendedKnown
    (body_available after.heap left (total.available left leftAvailable))
    (body_available after.heap right (total.available right rightAvailable)) semantic bodyValue after returned).2
  have pairOrdered := SourceRecursiveIntersectionScheduleEnvironment.ordered_pair first second
  have extendedOrdered : Ordered extended.key.seen := by
    rw [key]
    exact SourceRecursiveIntersectionScheduleEnvironment.ordered_extend domain.key _ _ ordered pairOrdered
  obtain ⟨heap, completed, _⟩ := construction_done _ after value after built
  refine ⟨first, second, extended, bodyValue, firstId, secondId, key, extendedKnown, available, returned, scope, ?_⟩
  intro holds shape bodyMeaning ambient
  exact SourceRecursiveIntersectionScheduleEnvironment.optionalBinder (pair first second) pairOrdered bodyValue shape
    after.heap semantic guarded available extended.key.seen extendedOrdered scope holds bodyMeaning value heap completed ambient

end MicroCFTA.SourceRecursiveIntersectionKernel
