import MicroCFTA.SourceRecursiveIntersectionNativeBindLower
import MicroCFTA.SourceRecursiveIntersectionNativePrimitiveLower
import MicroCFTA.SourceRecursiveIntersectionNativeWordRanges

namespace MicroCFTA.SourceRecursiveIntersectionNative
open InternedConstructorTemplates SourceRecursiveIntersectionCode
open InternedStoredPlanBinderDepthProgress

/-- Actual ordered native prefixes derive each call's word ranges from the preceding calls. -/
theorem walk_prefix_lower
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : A → Code Symbol Guard B)
    (invariant : SourceRecursiveIntersectionThunks.State width Symbol Guard → Prop)
    (bound : Nat) (requests : List A)
    (limited : ∀ request ∈ requests, ∀ current, invariant current →
      WordRanges emptyGuard conjoin (call request) current →
      ∀ fuel, Lower current.machine.heap bound
        (execute emptyGuard conjoin fuel (call request) current).state.machine.heap)
    (preserved : ∀ request ∈ requests, ∀ current, invariant current →
      WordRanges emptyGuard conjoin (call request) current →
      ∀ inner value after, execute emptyGuard conjoin inner (call request) current = .done value after →
        invariant after)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) (valid : invariant state)
    (ranges : WordRanges emptyGuard conjoin (walk call requests) state) (fuel : Nat) :
    Lower state.machine.heap bound
      (execute emptyGuard conjoin fuel (walk call requests) state).state.machine.heap := by
  induction requests generalizing state fuel with
  | nil => exact pure_lower emptyGuard conjoin fuel [] state bound
  | cons first rest ih =>
      let next (value : B) := (walk call rest).bind fun values => .pure (value :: values)
      have callRanges : WordRanges emptyGuard conjoin (call first) state :=
        ranges.before_bind emptyGuard conjoin (call first) next state
      change Lower state.machine.heap bound
        (execute emptyGuard conjoin fuel ((call first).bind next) state).state.machine.heap
      apply execute_bind_lower emptyGuard conjoin fuel (call first) next state bound
      · exact limited first List.mem_cons_self state valid callRanges
      · intro inner value after completed outer
        have afterValid := preserved first List.mem_cons_self state valid callRanges inner value after completed
        have tailRanges : WordRanges emptyGuard conjoin (next value) after :=
          ranges.after_body emptyGuard conjoin (call first) next state after value
            (evaluation_of_done emptyGuard conjoin inner (call first) state after value completed)
        have restRanges : WordRanges emptyGuard conjoin (walk call rest) after :=
          tailRanges.before_bind emptyGuard conjoin (walk call rest) (fun values => .pure (value :: values)) after
        apply execute_bind_lower emptyGuard conjoin outer (walk call rest)
          (fun values => .pure (value :: values)) after bound
        · intro restFuel
          exact ih (fun request member => limited request (List.mem_cons_of_mem _ member))
            (fun request member => preserved request (List.mem_cons_of_mem _ member))
            after afterValid restRanges restFuel
        · intro _ values final _ pureFuel
          exact pure_lower emptyGuard conjoin pureFuel (value :: values) final bound

end MicroCFTA.SourceRecursiveIntersectionNative
