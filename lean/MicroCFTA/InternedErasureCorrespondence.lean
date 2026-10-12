import MicroCFTA.InternedErasureChildren

/-!
# Normalized source-call correspondence below arbitrary constructors

A source-declared erased dependency preserves the earlier complete result.
The proof follows actual node, union, and nested Mu executions. Every later
callback has derived ordinary residual effects, including discarded edges.
-/
namespace MicroCFTA.InternedErasureCorrespondence
open InternedConstructorTemplates InternedNestedConstruction InternedRecordCoherence
open InternedNestedDependencies InternedNestedSpecialization InternedNestedCoherence
open InternedNestedErasureReplay InternedErasureResidual InternedErasureSyntax InternedErasureChildren
open InternedErasedEdgeReplay (run_coherent)

/-- Declared dependency erasure derives exact earlier-result correspondence and ordinary later effects through full source syntax. -/
theorem build_erased [DecidableEq (EdgeKey Symbol Guard)] {index : Nat} {expression : Syntax Symbol Guard}
    (erased : Erased index expression) (first second : List (Value Symbol Guard))
    (agree : AgreeExcept index first second) (before : State Symbol Guard) (value : Value Symbol Guard)
    (final : State Symbol Guard) (coherent : Coherent before)
    (completed : build expression first before = .done value final) : Residual value final (build expression second) := by
  induction erased generalizing first second before value final with
  | unused index expression absent =>
      exact pure_residual value final _ (fun after _ growth => independent_replay expression first second before after
        value final coherent.valid completed growth (fun selected member => agree selected (fun equal => absent (equal ▸ member))))
  | dead index live symbol constraint absent =>
      exact dead_residual index live absent symbol constraint first second agree before final value coherent completed
  | node index edges declared ih =>
      simp only [build] at completed
      obtain ⟨values, middle, edgesDone, parentDone⟩ := bind_done _ _ _ _ completed
      have edgesResidual := edges_residual edges first second
        (fun symbol constraint children member child included start value finish current returned =>
          ih symbol constraint children member child included first second agree start value finish current returned)
        before middle values coherent edgesDone
      have middleCoherent : Coherent middle := by
        simpa only [edgesDone, Outcome.state] using buildEdges_coherent edges first before coherent
      have parentResidual := work_residual (makeNode values) middle final value middleCoherent.valid parentDone
      have parentGrowth : Grows middle final := by
        simpa only [parentDone, Outcome.state] using (work_correct (makeNode values) middle middleCoherent.valid).2
      simpa only [Residual, build] using bind_residual (buildEdges edges second)
        (fun values current => work (makeNode values) current) values middle value final edgesResidual parentResidual parentGrowth
  | union index members declared ih =>
      simp only [build] at completed
      obtain ⟨values, middle, childrenDone, parentDone⟩ := bind_done _ _ _ _ completed
      have childResidual := many_residual members first second
        (fun child member start value finish current returned => ih child member first second agree start value finish current returned)
        before middle values coherent childrenDone
      have middleCoherent : Coherent middle := by
        simpa only [childrenDone, Outcome.state] using buildMany_coherent members first before coherent
      have parentResidual := work_residual (makeUnion values) middle final value middleCoherent.valid parentDone
      have parentGrowth : Grows middle final := by
        simpa only [parentDone, Outcome.state] using (work_correct (makeUnion values) middle middleCoherent.valid).2
      simpa only [Residual, build] using bind_residual (buildMany members second)
        (fun values current => work (makeUnion values) current) values middle value final childResidual parentResidual parentGrowth
  | binder index smart body inside ih =>
      let callback := fun environment name current => (build body (.reference name :: environment) current).bind
        fun value after => work (withoutSelfReference name value) after
      have growing : ∀ environment name, Growing (callback environment name) := by
        intro environment name current valid
        exact bind_correct _ _ current (build_correct body _ current valid)
          (fun value after afterValid => work_correct (withoutSelfReference name value) after afterValid)
      have callbackCoherent : ∀ environment name current, Coherent current → Coherent (callback environment name current).state := by
        intro environment name current currentCoherent
        exact bind_coherent _ _ (build_coherent body _ current currentCoherent)
          (fun value after _ afterCoherent => run_coherent (withoutSelfReference name value) after (withoutSelfReference_safe _ _) afterCoherent)
      have callbackResidual : ∀ name start result finish, Coherent start →
          callback first name start = .done result finish → Residual result finish (callback second name) := by
        intro name start result finish startCoherent returned
        obtain ⟨raw, middle, bodyDone, filterDone⟩ := bind_done _ _ _ _ returned
        have bodyResidual := ih (.reference name :: first) (.reference name :: second) (agree.local _) start raw middle startCoherent bodyDone
        have middleCoherent : Coherent middle := by
          simpa only [bodyDone, Outcome.state] using build_coherent body (.reference name :: first) start startCoherent
        have filterResidual := work_residual (withoutSelfReference name raw) middle finish result middleCoherent.valid filterDone
        have filterGrowth : Grows middle finish := by
          simpa only [filterDone, Outcome.state] using (work_correct (withoutSelfReference name raw) middle middleCoherent.valid).2
        exact bind_residual (build body (.reference name :: second)) (fun value after => work (withoutSelfReference name value) after)
          raw middle result finish bodyResidual filterResidual filterGrowth
      rw [build] at completed
      change (callback first .depth before).bind (fun depth afterDepth =>
        (callback first (.uninterned depth.depth) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary (callback first) afterOrdinary) = .done value final at completed
      obtain ⟨depth, afterDepth, depthDone, remaining⟩ := bind_done _ _ _ _ completed
      have depthCoherent : Coherent afterDepth := by
        simpa only [depthDone, Outcome.state] using callbackCoherent first .depth before coherent
      obtain ⟨ordinary, afterOrdinary, ordinaryDone, requestDone⟩ := bind_done _ _ _ _ remaining
      have ordinaryCoherent : Coherent afterOrdinary := by
        simpa only [ordinaryDone, Outcome.state] using callbackCoherent first (.uninterned depth.depth) afterDepth depthCoherent
      have requestGrowth : Grows afterOrdinary final := by
        simpa only [requestDone, Outcome.state] using
          (request_correct smart depth ordinary (callback first) (growing first) afterOrdinary ordinaryCoherent.valid).2
      have ordinaryGrowth : Grows afterDepth afterOrdinary := by
        simpa only [ordinaryDone, Outcome.state] using (growing first (.uninterned depth.depth) afterDepth depthCoherent.valid).2
      have requestResidual : Residual value final (request smart depth ordinary (callback second)) :=
        pure_residual value final _ (fun after _ growth => request_after_done smart depth ordinary
          (callback first) (callback second) afterOrdinary after value final ordinaryCoherent.valid (growing first) requestDone growth)
      have later := bind_residual (callback second (.uninterned depth.depth))
        (fun ordinary after => request smart depth ordinary (callback second) after)
        ordinary afterOrdinary value final
        (callbackResidual (.uninterned depth.depth) afterDepth ordinary afterOrdinary depthCoherent ordinaryDone)
        requestResidual requestGrowth
      have all := bind_residual (callback second .depth)
        (fun depth afterDepth => (callback second (.uninterned depth.depth) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary (callback second) afterOrdinary)
        depth afterDepth value final (callbackResidual .depth before depth afterDepth coherent depthDone)
        later (grows_trans ordinaryGrowth requestGrowth)
      simpa only [Residual, build, callback] using all

end MicroCFTA.InternedErasureCorrespondence
