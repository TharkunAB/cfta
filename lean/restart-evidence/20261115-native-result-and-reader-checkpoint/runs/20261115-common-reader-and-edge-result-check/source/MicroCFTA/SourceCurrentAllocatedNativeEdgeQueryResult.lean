import MicroCFTA.SourceCurrentAllocatedNativeReturnedProperties
import MicroCFTA.SourceEqualityNativeDemandRunning

/-!
# Conditional result laws for actual completed edge queries

Actual completion selects a ready cell or the actual checked edge body.
The body hypothesis retains the original request and its emitted continuation.
The actual body, finish and pure traces identify the same returned row.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeEdgeQueryResult
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache (Returned)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Native" => SourceRecursiveIntersectionThunks.State
variable {width : Nat}

set_option autoImplicit false

/-- Actual publication retains the law at every previously returned edge cell. -/
private theorem lookup_returned
    (law : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop)
    (request : EdgeRequest Symbol Guard) (state : Native width Symbol Guard)
    (returned : Returned law state.edges) :
    Returned law (lookupEdge width request state).2.edges := by
  simpa only [lookupEdge] using
    SourceCurrentAllocatedNativeContextCache.returned_lookup law
      (SourceRecursiveIntersectionEdgeMemo.requestKey width request.domain request.left request.right)
      request state.edges returned

/-- Actual completion inherits its exact ready-cell law or its smaller checked body's law. -/
theorem edge_query_result_of_body_induction
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (law : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop)
    (request : EdgeRequest Symbol Guard) (before after : Checked width)
    (fuel : Nat) (value : EdgeValue Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (ready : EdgeReady before.native.machine request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right)
    (returned : Returned law before.native.edges)
    (done : SourceEqualityNativeDemand.execute fuel
      (.code (requestEdge request.domain request.left request.right)) before = .done value after)
    (bodies : ∀ bodySteps, bodySteps + 1 < fuel →
      ∀ (next : EdgeValue Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard)) (first middle : Checked width)
        (result : EdgeValue Symbol Guard),
      Steps 1 (.code (requestEdge request.domain request.left request.right)) before
        (.edgeBody request next) first →
      Steps bodySteps (.edgeBody request .pure) first (.code (.pure result)) middle →
      law request result) : law request value := by
  obtain ⟨total, bounded, trace⟩ :=
    done_trace fuel (.code (requestEdge request.domain request.left request.right)) before after value done
  cases total with
  | zero => cases (steps_zero _ _ _ _ trace).1
  | succ steps =>
      obtain ⟨rest, current, one, tail⟩ := steps_succ steps _ _ _ _ trace
      have published := lookup_returned law request before.native returned
      cases selected : lookupEdge width request before.native with
      | mk handle chosen =>
          have chosenReturned : Returned law chosen.edges := by
            simpa only [selected] using published
          cases demanded : demandEdge handle chosen with
          | mk observation running =>
              cases observation with
              | absent | busy =>
                  simp only [requestEdge, SourceEqualityNativeDemand.step, selected, demanded] at one
                  cases one
              | ready result =>
                  have same := Outcome.yielded.inj (by
                    simpa only [requestEdge, SourceEqualityNativeDemand.step, selected, demanded] using one)
                  rcases same.1 with rfl
                  rcases same.2 with rfl
                  have actualCell := SourceCurrentAllocatedNativePhysicalCache.edge_ready request
                    before.native chosen running handle result physical ready safe selected demanded
                  have localLaw := chosenReturned handle request result actualCell.1
                  have sameValue := (pure_trace steps result value ⟨running, before.operations⟩ after tail).2.1
                  simpa only [sameValue] using localLaw
              | evaluate actual =>
                  have original := SourceCurrentAllocatedNativePhysicalCache.edge_started request actual
                    before.native chosen running handle physical ready safe selected demanded
                  subst actual
                  let first : Checked width := ⟨running, before.operations⟩
                  let next : EdgeValue Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard) :=
                    fun result => .finishEdge handle result (.pure result)
                  have emitted : SourceEqualityNativeDemand.step
                      (.code (requestEdge request.domain request.left request.right)) before =
                      .yielded (.edgeBody request next) first := by
                    simp only [requestEdge, SourceEqualityNativeDemand.step, selected, demanded, first, next]
                  have origin : Steps 1 (.code (requestEdge request.domain request.left request.right)) before
                      (.edgeBody request next) first :=
                    .cons _ _ _ _ _ _ _ emitted (.refl _ _)
                  have same := Outcome.yielded.inj (emitted.symm.trans one)
                  rcases same.1 with rfl
                  rcases same.2 with rfl
                  obtain ⟨inner, outer, result, middle, count, bodyTrace, frameTrace⟩ :=
                    steps_bind_inverse steps (.edgeBody request .pure) next first after value tail
                  obtain ⟨remaining, frameCount, finalTrace⟩ :=
                    SourceEqualityNativeDemandRunning.finish_edge_trace
                      outer handle result (.pure result) middle after value frameTrace
                  have pure := pure_trace remaining result value _ after finalTrace
                  have noRemaining := pure.1
                  have localLaw := bodies inner (by omega) next first middle result origin bodyTrace
                  simpa only [pure.2.1] using localLaw

end MicroCFTA.SourceCurrentAllocatedNativeEdgeQueryResult


#check MicroCFTA.SourceCurrentAllocatedNativeEdgeQueryResult.edge_query_result_of_body_induction
#print axioms MicroCFTA.SourceCurrentAllocatedNativeEdgeQueryResult.edge_query_result_of_body_induction
