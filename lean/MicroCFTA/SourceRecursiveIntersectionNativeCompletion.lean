import MicroCFTA.SourceRecursiveIntersectionNativeEvaluation

/-!
# Derive nested completion from actual native execution

Strong induction on the original finite trace extracts each body and its
completion frame. The derived nested evaluation contains actual native
effects. No source completion provenance is assumed.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode

/-- Every actual completed trace derives a finite nested native evaluation. -/
theorem evaluation_of_trace [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) {A : Type} (code : Code Symbol Guard A) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (value : A) (trace : Steps emptyGuard conjoin fuel code state (.pure value) after) :
    Evaluation width Symbol Guard emptyGuard conjoin code state value after := by
  induction fuel using Nat.strongRecOn generalizing A code state after value with
  | ind fuel ih =>
    cases fuel with
    | zero =>
      obtain ⟨same, retained⟩ := steps_zero emptyGuard conjoin _ _ _ _ trace
      subst code
      subst after
      exact .pure _ _
    | succ fuel =>
      obtain ⟨rest, current, one, tail⟩ := steps_succ emptyGuard conjoin fuel _ _ _ _ trace
      cases code with
      | pure | fail => cases one
      | work job next =>
        have same := Outcome.yielded.inj one
        rcases same.1 with rfl
        rcases same.2 with rfl
        exact .work (ih fuel (by omega) _ _ _ _ tail)
      | enter domain left right first second next =>
        have same := Outcome.yielded.inj one
        rcases same.1 with rfl
        rcases same.2 with rfl
        exact .enter (ih fuel (by omega) _ _ _ _ tail)
      | read name next =>
        have same := Outcome.yielded.inj one
        rcases same.1 with rfl
        rcases same.2 with rfl
        exact .read (ih fuel (by omega) _ _ _ _ tail)
      | optionalBinder key body next =>
        cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu key body state.machine.heap with
        | done result heap =>
          simp only [step, actual] at one
          have same := Outcome.yielded.inj one
          rcases same.1 with rfl
          rcases same.2 with rfl
          exact .optionalBinder actual (ih fuel (by omega) _ _ _ _ tail)
        | pending => simp only [step, actual] at one; cases one
      | node request next =>
        cases selected : lookupNode width request state with
        | mk selection chosen =>
          cases selection with
          | direct actual =>
            simp only [step, selected] at one
            have same := Outcome.yielded.inj one
            rcases same.1 with rfl
            rcases same.2 with rfl
            obtain ⟨inner, outer, bodyValue, middle, count, bodyTrace, restTrace⟩ :=
              steps_bind_inverse emptyGuard conjoin fuel (compileNode actual) next chosen after value tail
            exact .nodeDirect selected (ih inner (by omega) _ _ _ _ bodyTrace) (ih outer (by omega) _ _ _ _ restTrace)
          | memoized handle =>
            cases demanded : demandNode handle chosen with
            | mk observation running =>
              cases observation with
              | absent | busy => simp only [step, selected, demanded] at one; cases one
              | ready result =>
                simp only [step, selected, demanded] at one
                have same := Outcome.yielded.inj one
                rcases same.1 with rfl
                rcases same.2 with rfl
                exact .nodeReady selected demanded (ih fuel (by omega) _ _ _ _ tail)
              | evaluate actual =>
                simp only [step, selected, demanded] at one
                have same := Outcome.yielded.inj one
                rcases same.1 with rfl
                rcases same.2 with rfl
                obtain ⟨inner, outer, bodyValue, middle, count, bodyTrace, frameTrace⟩ :=
                  steps_bind_inverse emptyGuard conjoin fuel (compileNode actual)
                    (fun result => .finishNode handle result (next result)) running after value tail
                obtain ⟨remaining, frameCount, restTrace⟩ := finishNode_trace emptyGuard conjoin outer handle bodyValue (next bodyValue) middle after value frameTrace
                exact .nodeStarted selected demanded (ih inner (by omega) _ _ _ _ bodyTrace) (ih remaining (by omega) _ _ _ _ restTrace)
      | edge request next =>
        cases selected : lookupEdge width request state with
        | mk handle chosen =>
          cases demanded : demandEdge handle chosen with
          | mk observation running =>
            cases observation with
            | absent | busy => simp only [step, selected, demanded] at one; cases one
            | ready result =>
              simp only [step, selected, demanded] at one
              have same := Outcome.yielded.inj one
              rcases same.1 with rfl
              rcases same.2 with rfl
              exact .edgeReady selected demanded (ih fuel (by omega) _ _ _ _ tail)
            | evaluate actual =>
              simp only [step, selected, demanded] at one
              have same := Outcome.yielded.inj one
              rcases same.1 with rfl
              rcases same.2 with rfl
              obtain ⟨inner, outer, bodyValue, middle, count, bodyTrace, frameTrace⟩ :=
                steps_bind_inverse emptyGuard conjoin fuel (compileEdge emptyGuard conjoin actual)
                  (fun result => .finishEdge handle result (next result)) running after value tail
              obtain ⟨remaining, frameCount, restTrace⟩ := finishEdge_trace emptyGuard conjoin outer handle bodyValue (next bodyValue) middle after value frameTrace
              exact .edgeStarted selected demanded (ih inner (by omega) _ _ _ _ bodyTrace) (ih remaining (by omega) _ _ _ _ restTrace)
      | finishNode handle result next =>
        have same := Outcome.yielded.inj one
        rcases same.1 with rfl
        rcases same.2 with rfl
        exact .finishNode (ih fuel (by omega) _ _ _ _ tail)
      | finishEdge handle result next =>
        have same := Outcome.yielded.inj one
        rcases same.1 with rfl
        rcases same.2 with rfl
        exact .finishEdge (ih fuel (by omega) _ _ _ _ tail)

/-- Actual completed bounded execution supplies its nested source-request evaluation tree. -/
theorem evaluation_of_done [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (code : Code Symbol Guard A) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (value : A) (done : execute emptyGuard conjoin fuel code state = .done value after) :
    Evaluation width Symbol Guard emptyGuard conjoin code state value after := by
  obtain ⟨steps, _, trace⟩ := done_trace emptyGuard conjoin fuel code state after value done
  exact evaluation_of_trace emptyGuard conjoin steps code state after value trace

end MicroCFTA.SourceRecursiveIntersectionNative
