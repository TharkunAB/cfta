import MicroCFTA.SourceRecursiveIntersectionKernel
import MicroCFTA.InternedStoredPlanBinderDepthLowerAlgebra

/-!
# Allocation bounds through actual kernel sequencing

The bound includes failed outcomes and earlier ordered effects.
The invariant is needed only before each call and after each successful call.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open InternedConstructorTemplates InternedStoredPlanBinderDepthProgress

/-- Sequencing retains the reached heap when either call fails. -/
theorem result_bind_lower {initial : State Symbol Guard} {bound : Nat}
    (outcome : Result Symbol Guard A)
    (next : A → Machine Symbol Guard → Result Symbol Guard B)
    (lower : Lower initial bound outcome.state.heap)
    (later : ∀ value after, outcome = .done value after →
      Lower initial bound after.heap → Lower initial bound (next value after).state.heap) :
    Lower initial bound (outcome.bind next).state.heap := by
  cases outcome with
  | failed => exact lower
  | done value after => exact later value after rfl lower

/-- Every reached ordered-walk heap retains all earlier allocation bounds. -/
theorem walk_lower (call : A → Machine Symbol Guard → Result Symbol Guard B)
    (invariant : Machine Symbol Guard → Prop) (bound : Nat)
    (requests : List A)
    (limited : ∀ request ∈ requests, ∀ state, invariant state →
      Lower state.heap bound (call request state).state.heap)
    (preserved : ∀ request ∈ requests, ∀ state value after, invariant state →
      call request state = .done value after → invariant after)
    (state : Machine Symbol Guard) (valid : invariant state) :
    Lower state.heap bound (walk call requests state).state.heap := by
  induction requests generalizing state with
  | nil => exact lower_refl state.heap bound
  | cons first rest ih =>
      have firstLower := limited first (by simp) state valid
      cases firstDone : call first state with
      | failed reason after =>
          simpa only [walk, firstDone, Result.bind, Result.state] using firstLower
      | done value after =>
          have afterValid := preserved first (by simp) state value after valid firstDone
          have restLower := ih (fun request member => limited request (by simp [member]))
            (fun request member => preserved request (by simp [member])) after afterValid
          have currentLower : Lower state.heap bound after.heap := by
            simpa only [firstDone, Result.state] using firstLower
          have combined := currentLower.trans restLower
          cases restDone : walk call rest after <;>
            simpa only [walk, firstDone, Result.bind, restDone, Result.state] using combined

end MicroCFTA.SourceRecursiveIntersectionKernel
