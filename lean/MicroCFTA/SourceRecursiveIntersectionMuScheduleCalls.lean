import MicroCFTA.SourceRecursiveIntersectionScheduleCalls
import MicroCFTA.SourceRecursiveIntersectionMuScheduleAction
import MicroCFTA.SourceRecursiveIntersectionMuSchedule

/-!
# Complete actual Mu branch correspondence from recursive calls

Actual domain entry and the original body codec supply the semantic body
request. Canonical map order retains every lookup. The actual optional
binder then supplies the exact semantic result of every Mu branch.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache Language Binding InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionCode (NodeScope)
open SourceRecursiveIntersectionInputView (view inputOf)
open SourceRecursiveIntersectionScheduleConstructors (Corresponds)
open SourceRecursiveIntersectionScheduleEnvironment (Ordered)
open SourceRecursiveIntersectionControl (decision pair)

/-- Recursive correspondence supplies the full selected semantic Mu action and actual result language. -/
theorem mu_schedule_calls [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (replay : Replays call) (scopes : SourceRecursiveIntersectionScopeCalls.ScopedCalls call)
    (state : Machine Symbol Guard) (valid : Valid state)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap state.heap) (guarded : InternedGuardedProbeHeap.Heap state.heap)
    (holds : Guard → Term Symbol → Bool) (fuel : Nat) (correct : ScheduleCalls call state holds fuel)
    (domain : Interned DomainKey) (left right : Value Symbol Guard) (known : Domain state domain)
    (scope : NodeScope state.heap ⟨domain, left, right⟩) (ordered : Ordered domain.key.seen)
    (recursive : decision domain.key left right = .bothMu ∨ decision domain.key left right = .leftMu ∨ decision domain.key left right = .rightMu)
    (value : Value Symbol Guard) (done : mu call domain left right state = .done value state) :
    ∃ shape, SourceRecursiveIntersectionStep.action (view state.heap holds) (fuel + 1)
      (SourceRecursiveIntersectionSchedule.domain domain.key) (inputOf left) (inputOf right)
      (decision domain.key left right) = some (.ok shape) ∧ Corresponds holds value shape := by
  obtain ⟨first, second, extended, bodyValue, firstId, secondId, key, extendedKnown, _, returned, _, transport⟩ :=
    mu_schedule_body call calls replay scopes domain left right state state valid valid known scope.leftAvailable scope.rightAvailable
      semantic guarded ordered value state done (.refl _)
  have bodyScope := scope.mu state.heap domain extended left right first second key
  have extendedOrdered : Ordered extended.key.seen := by
    rw [key]
    exact SourceRecursiveIntersectionScheduleEnvironment.ordered_extend domain.key _ _ ordered
      (SourceRecursiveIntersectionScheduleEnvironment.ordered_pair first second)
  obtain ⟨bodyShape, bodyDone, bodyMeaning⟩ := correct.larger call state holds fuel (fuel + 1) (by omega)
    extended (body left) (body right) extendedKnown bodyScope extendedOrdered bodyValue returned
  have pairExact := SourceRecursiveIntersectionSchedule.pair_encoded left right (inputOf left) (inputOf right)
    (scope.left.codec left) (scope.right.codec right) first second firstId secondId
  rw [key, SourceRecursiveIntersectionSchedule.run_canonical_extend] at bodyDone
  simp only [SourceRecursiveIntersectionEnvironment.bindings, List.map_append,
    SourceRecursiveIntersectionEnvironment.binder_encoded left (inputOf left) (scope.left.codec left),
    SourceRecursiveIntersectionEnvironment.binder_encoded right (inputOf right) (scope.right.codec right)] at bodyDone
  rw [pairExact, SourceRecursiveIntersectionCode.body_encoded state.heap valid.1 holds left scope.left scope.leftAvailable,
    SourceRecursiveIntersectionCode.body_encoded state.heap valid.1 holds right scope.right scope.rightAvailable] at bodyDone
  have selected := (SourceRecursiveIntersectionCode.decision_source state.heap valid.1 holds ⟨domain, left, right⟩ scope).symm
  have payload := IntersectSchedule.mu_payload (view state.heap holds) (SourceRecursiveIntersectionSchedule.domain domain.key)
    (inputOf left) (inputOf right) (decision domain.key left right) selected recursive
  refine ⟨IntersectSchedule.maybeMu (pair first second) bodyShape, ?_, transport holds bodyShape bodyMeaning⟩
  rw [IntersectSchedule.mu_schedule_action _ _ _ _ _ _ payload recursive]
  simp only [List.map_append]
  rw [bodyDone, ← pairExact]
  rfl

end MicroCFTA.SourceRecursiveIntersectionKernel
