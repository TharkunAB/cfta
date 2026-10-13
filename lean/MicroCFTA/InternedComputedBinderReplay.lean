import MicroCFTA.InternedComputedErasure

/-!
# Binder replay from source-computed empty children

Body certificates use either existing structural erasure or a dependent
edge with a source-computed empty child. Actual complete probe traces then
supply the same canonical request and its completed earlier record.
-/
namespace MicroCFTA.InternedComputedBinderReplay
open InternedConstructorTemplates InternedNestedConstruction InternedRecordCoherence
open InternedNestedDependencies InternedNestedSpecialization InternedNestedCoherence
open InternedNestedErasureReplay InternedErasureResidual InternedErasureSyntax InternedErasureCorrespondence
open InternedErasedEdgeReplay (run_coherent)
open InternedComputedEmpty

/-- The source body declares how its changed input is removed by actual normalization. -/
inductive Erases (index : Nat) : Syntax Symbol Guard → Prop where
  | structural (expression : Syntax Symbol Guard) (erased : Erased index expression) : Erases index expression
  | computed (live : List (EdgeSyntax Symbol Guard)) (symbol : Symbol) (constraint : Guard)
      (blocker : Syntax Symbol Guard) (absent : index ∉ edgeInputs live)
      (zero : EmptyResult blocker) (erased : Erased index blocker) :
      Erases index (.node (live ++ [.mk symbol constraint [.var index, blocker]]))

/-- Both source declarations derive exact changed-input replay and finite ordinary effects. -/
theorem body_residual [DecidableEq (EdgeKey Symbol Guard)] (erased : Erases index expression)
    (first second : List (Value Symbol Guard)) (agree : AgreeExcept index first second)
    (before : State Symbol Guard) (value : Value Symbol Guard) (final : State Symbol Guard)
    (coherent : Coherent before) (completed : build expression first before = .done value final) :
    Residual value final (build expression second) := by
  cases erased with
  | structural expression erased => exact build_erased erased first second agree before value final coherent completed
  | computed live symbol constraint blocker absent zero erased =>
      exact InternedComputedErasure.dead_residual index live absent symbol constraint blocker zero erased
        first second agree before final value coherent completed

/-- Actual normalized source probes reuse the completed request after computed dependency erasure. -/
theorem binder_residual [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (body : Syntax Symbol Guard)
    (erased : Erases (index + 1) body) (first second : List (Value Symbol Guard))
    (agree : AgreeExcept index first second) (before : State Symbol Guard) (value : Value Symbol Guard)
    (final : State Symbol Guard) (coherent : Coherent before)
    (completed : build (.binder smart body) first before = .done value final) :
    Residual value final (build (.binder smart body) second) := by
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
    have bodyResidual := body_residual erased (.reference name :: first) (.reference name :: second) (agree.local _) start raw middle startCoherent bodyDone
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

end MicroCFTA.InternedComputedBinderReplay
