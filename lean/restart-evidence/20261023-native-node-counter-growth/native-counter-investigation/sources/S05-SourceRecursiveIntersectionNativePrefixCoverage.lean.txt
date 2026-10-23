import MicroCFTA.SourceRecursiveIntersectionMaybeMuCoverage
import MicroCFTA.SourceRecursiveIntersectionNativeRangeCertificate

/-!
# Payload coverage on every actual yielded native prefix

Ordinary work and completed optional binders retain coverage. Domain and
memo operations do not change the constructor heap. Thus any finite yielded
prefix retains its incoming pending-key allowance. No completed native run,
body preparation, word bound, or memo provenance premise is needed.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedRecordCoherence InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode

/-- Every native node lookup and demand leaves the source machine unchanged at its immediate observation. -/
theorem node_step_machine [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (request : NodeRequest Symbol Guard)
    (next : Value Symbol Guard → Code Symbol Guard A) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    (step emptyGuard conjoin (.node request next) state).state.machine = state.machine := by
  cases lookup : lookupNode width request state with
  | mk selection chosen =>
    have chosenMachine : chosen.machine = state.machine := by simpa only [lookup] using lookupNode_machine request state
    cases selection with
    | direct actual => simpa only [step, lookup, Outcome.state] using chosenMachine
    | memoized handle =>
      cases demand : demandNode handle chosen with
      | mk observation current =>
        have currentMachine : current.machine = chosen.machine := by simpa only [demand] using demandNode_machine handle chosen
        cases observation <;> simpa only [step, lookup, demand, Outcome.state] using currentMachine.trans chosenMachine

/-- Every native row lookup and demand leaves the source machine unchanged at its immediate observation. -/
theorem edge_step_machine [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (request : EdgeRequest Symbol Guard)
    (next : EdgeValue Symbol Guard → Code Symbol Guard A) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    (step emptyGuard conjoin (.edge request next) state).state.machine = state.machine := by
  cases lookup : lookupEdge width request state with
  | mk handle chosen =>
    have chosenMachine : chosen.machine = state.machine := by simpa only [lookup] using lookupEdge_machine request state
    cases demand : demandEdge handle chosen with
    | mk observation current =>
      have currentMachine : current.machine = chosen.machine := by simpa only [demand] using demandEdge_machine handle chosen
      cases observation <;> simpa only [step, lookup, demand, Outcome.state] using currentMachine.trans chosenMachine

/-- One actual yielded native step retains valid constructor caches and every incoming payload permission. -/
theorem step_yielded_covered [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (code next : Code Symbol Guard A)
    (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : InternedConstructorTemplates.Valid state.machine.heap) (covered : Covered pending state.machine.heap)
    (one : step emptyGuard conjoin code state = .yielded next after) :
    InternedConstructorTemplates.Valid after.machine.heap ∧ Covered pending after.machine.heap := by
  cases code with
  | pure | fail => cases one
  | work job resume =>
      cases one
      exact ⟨(InternedConstructorTemplates.run_correct job state.machine.heap valid).1,
        InternedNestedCoverage.run_covered job state.machine.heap valid covered⟩
  | enter | read | finishNode | finishEdge => cases one; exact ⟨valid, covered⟩
  | optionalBinder key body resume =>
      cases constructed : SourceRecursiveIntersectionMaybeMu.maybeMu key body state.machine.heap with
      | pending => simp only [step, constructed] at one; cases one
      | done value heap =>
          have same := Outcome.yielded.inj (by simpa only [step, constructed] using one)
          have physical : after.machine.heap = heap := congrArg (fun current => current.machine.heap) same.2.symm
          rw [physical]
          exact ⟨by simpa only [constructed, InternedNestedConstruction.Outcome.state] using
              (SourceRecursiveIntersectionMaybeMu.maybeMu_correct key body state.machine.heap valid).1,
            SourceRecursiveIntersectionMaybeMu.maybeMu_covered key body state.machine.heap valid covered value heap constructed⟩
  | node request resume =>
      have same := node_step_machine emptyGuard conjoin request resume state
      rw [one] at same
      change after.machine = state.machine at same
      rw [same]
      exact ⟨valid, covered⟩
  | edge request resume =>
      have same := edge_step_machine emptyGuard conjoin request resume state
      rw [one] at same
      change after.machine = state.machine at same
      rw [same]
      exact ⟨valid, covered⟩

/-- Every actual finite yielded prefix retains valid constructor caches and its incoming payload coverage. -/
theorem Steps.covered [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat) (code next : Code Symbol Guard A)
    (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (trace : Steps emptyGuard conjoin fuel code state next after) :
    InternedConstructorTemplates.Valid state.machine.heap → Covered pending state.machine.heap →
    InternedConstructorTemplates.Valid after.machine.heap ∧ Covered pending after.machine.heap := by
  induction trace with
  | refl => intro valid covered; exact ⟨valid, covered⟩
  | cons code state next after final result fuel one rest ih =>
      intro valid covered
      have retained := step_yielded_covered emptyGuard conjoin code next state after valid covered one
      exact ih retained.1 retained.2

end MicroCFTA.SourceRecursiveIntersectionNative
