import MicroCFTA.SourceRecursiveIntersectionNativeNodeProgress
import MicroCFTA.SourceRecursiveIntersectionNativeEdgeProgress

/-!
# Finite source code observations through actual continuations

Structural code induction composes finite smaller body observations.
Physical effects retain the original input inventory and active bounds.
Optional binders report their actual pending key or continue from their
actual returned heap. They are not assumed to complete successfully.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedProbeProvenance InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView IntersectSchedule

/-- Strictly smaller body observations derive finite actual code observations without a supplied completed run. -/
theorem code_terminal_of_bodies [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (holds : Guard → Language.Term Symbol → Bool)
    (bound : Nat) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (bodies : BodiesBelow source holds bound width emptyGuard conjoin) (code : Code Symbol Guard A) :
    ∀ (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) (post : Machine Symbol Guard → A → Prop),
    Safe code state.machine post → Below source holds bound code state.machine →
    SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state → Grows source state.machine.heap →
    Extends source.nodes.issued state.machine.heap.nodes.issued → ActiveAbove (view source holds) holds bound state →
    WordRanges emptyGuard conjoin code state → ∃ fuel, Terminal (execute emptyGuard conjoin fuel code state) := by
  induction code with
  | pure value => intro state _ _ _ _ _ _ _ _; exact ⟨1, .done value state⟩
  | fail failure => intro state _ _ _ _ _ _ _ _; exact ⟨1, .failed failure state⟩
  | work job next ih =>
      intro state post safe below valid growth history active ranges
      let actual := InternedConstructorTemplates.run job state.machine.heap
      let current : Machine Symbol Guard := {state.machine with heap := actual.2}
      have physical : Extension state.machine current := safe.2.1
      have continued := ih actual.1 (advance state current) post (safe.2.2 actual.1 current rfl) (below actual.1 current rfl)
        (advance_valid width emptyGuard conjoin state valid current safe.1 physical)
        (grows_trans growth physical.heap) (extends_trans history physical.history)
        (active.advance _ holds bound state current) (ranges.after_step emptyGuard conjoin _ _ _ _ rfl)
      exact terminal_after_step emptyGuard conjoin _ _ _ _ rfl continued
  | enter domain left right first second next ih =>
      intro state post safe below valid growth history active ranges
      let actual := SourceRecursiveIntersectionEnvironment.enter state.machine.domains domain.key left right first second
      let current : Machine Symbol Guard := {state.machine with domains := actual.2}
      have physical : Extension state.machine current := safe.2.1
      have continued := ih actual.1 (advance state current) post safe.2.2 below
        (advance_valid width emptyGuard conjoin state valid current safe.1 physical)
        (grows_trans growth physical.heap) (extends_trans history physical.history)
        (active.advance _ holds bound state current) (ranges.after_step emptyGuard conjoin _ _ _ _ rfl)
      exact terminal_after_step emptyGuard conjoin _ _ _ _ rfl continued
  | read name next ih =>
      intro state post safe below valid growth history active ranges
      exact terminal_after_step emptyGuard conjoin _ _ _ _ rfl
        (ih _ state post safe below valid growth history active (ranges.after_step emptyGuard conjoin _ _ _ _ rfl))
  | optionalBinder key body next ih =>
      intro state post safe below valid growth history active ranges
      cases constructed : SourceRecursiveIntersectionMaybeMu.maybeMu key body state.machine.heap with
      | pending pending heap =>
          exact ⟨1, by simp only [execute, step, constructed]; exact .constructor _ _ _⟩
      | done value heap =>
          let current : Machine Symbol Guard := {state.machine with heap := heap}
          have currentValid : SourceRecursiveIntersectionKernel.Valid current := by simpa only [constructed, construction, Result.state] using safe.1
          have physical : Extension state.machine current := by simpa only [constructed, construction, Result.state] using safe.2.1
          have actual : construction (SourceRecursiveIntersectionMaybeMu.maybeMu key body state.machine.heap) state.machine = .done value current := by
            simp only [constructed, construction]; rfl
          have one : step emptyGuard conjoin (.optionalBinder key body next) state = .yielded (next value) (advance state current) := by
            simp only [step, constructed]; rfl
          exact terminal_after_step emptyGuard conjoin _ _ _ _ one
            (ih value (advance state current) post (safe.2.2 value current actual) (below value current actual)
              (advance_valid width emptyGuard conjoin state valid current currentValid physical)
              (grows_trans growth physical.heap) (extends_trans history physical.history)
              (active.advance _ holds bound state current) (ranges.after_step emptyGuard conjoin _ _ _ _ one))
  | node request next ih =>
      intro state post safe below valid growth history active ranges
      apply node_terminal source holds bound emptyGuard conjoin bodies request next state valid safe.1 below.1 growth history active ranges
      intro value after afterValid physical available afterActive afterRanges
      exact ih value after post (safe.2 value after.machine afterValid.machine physical available)
        (below.2 value after.machine afterValid.machine physical available) afterValid
        (grows_trans growth physical.heap) (extends_trans history physical.history) afterActive afterRanges
  | edge request next ih =>
      intro state post safe below valid growth history active ranges
      apply edge_terminal source holds bound emptyGuard conjoin bodies request next state valid safe.1 below.1 growth history active ranges
      intro value after afterValid physical available afterActive afterRanges
      exact ih value after post (safe.2 value after.machine afterValid.machine physical available)
        (below.2 value after.machine afterValid.machine physical available) afterValid
        (grows_trans growth physical.heap) (extends_trans history physical.history) afterActive afterRanges
  | finishNode | finishEdge => intro _ _ _ impossible; cases impossible

end MicroCFTA.SourceRecursiveIntersectionNative
