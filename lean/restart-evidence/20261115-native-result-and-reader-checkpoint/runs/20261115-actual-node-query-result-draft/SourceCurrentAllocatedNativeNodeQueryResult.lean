import MicroCFTA.SourceCurrentAllocatedNativeReturnedProperties
import MicroCFTA.SourceEqualityNativeDemandNodeReadback

/-!
# Conditional result laws for actual completed node queries

Actual readback selects a direct body, a ready cell or an evaluated body.
Every body hypothesis retains the original query and its actual emitted prefix.
A ready hit uses the prior returned law at the exact original request.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeNodeQueryResult
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache (Returned)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}

set_option autoImplicit false

/-- Actual completion inherits its exact ready-cell law or its smaller emitted body's law. -/
theorem node_query_result_of_body_induction
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (law : NodeRequest Symbol Guard → Value Symbol Guard → Prop)
    (request : NodeRequest Symbol Guard) (before after : Checked width)
    (fuel : Nat) (value : Value Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (ready : NodeReady before.native.machine request)
    (safe : ∀ key, SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key →
      SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (returned : Returned law before.native.nodes)
    (done : SourceEqualityNativeDemand.execute fuel
      (.code (requestNode request.domain request.left request.right)) before = .done value after)
    (bodies : ∀ bodySteps, bodySteps + 1 < fuel →
      ∀ (next : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard)) (first middle : Checked width)
        (result : Value Symbol Guard),
      Steps 1 (.code (requestNode request.domain request.left request.right)) before
        (.code ((compileNode request).bind next)) first →
      Steps bodySteps (.code (compileNode request)) first (.code (.pure result)) middle →
      law request result) : law request value := by
  obtain ⟨total, bounded, actual⟩ :=
    SourceEqualityNativeDemandNodeReadback.of_done fuel request before after value done
  cases actual with
  | direct bodySteps middle result unresolved body =>
      have one : SourceEqualityNativeDemand.step
          (.code (requestNode request.domain request.left request.right)) before =
          .yielded (.code ((compileNode request).bind .pure)) before := by
        simp only [requestNode, SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step,
          lookupNode, unresolved, SourceEqualityNativeDemand.lift]
      have origin : Steps 1 (.code (requestNode request.domain request.left request.right)) before
          (.code ((compileNode request).bind .pure)) before :=
        .cons _ _ _ _ _ _ _ one (.refl _ _)
      exact bodies bodySteps bounded .pure before middle result origin body
  | ready key handle original result keyed published stored =>
      obtain ⟨_same, _selected, _demanded, _available, localLaw⟩ :=
        SourceCurrentAllocatedNativeReturnedProperties.node_ready_property law before.native physical returned
          request original ready key ⟨keyed, safe key keyed⟩ handle published result stored
      exact localLaw
  | started bodySteps handle chosen running actual middle result selected demanded _suspended _evaluating _machine body =>
      obtain ⟨key, keyed, _published, _unchanged⟩ :=
        SourceRecursiveIntersectionNative.lookupNode_memoized request before.native chosen handle selected
      have same := SourceCurrentAllocatedNativePhysicalCache.node_started request actual before.native chosen running
        handle physical ready (safe key keyed) selected demanded
      subst actual
      let first : Checked width := ⟨running, before.operations⟩
      let next : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard) :=
        fun result => .finishNode handle result (.pure result)
      have one : SourceEqualityNativeDemand.step
          (.code (requestNode request.domain request.left request.right)) before =
          .yielded (.code ((compileNode request).bind next)) first := by
        simp only [requestNode, SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step,
          selected, demanded, SourceEqualityNativeDemand.lift, first, next]
      have origin : Steps 1 (.code (requestNode request.domain request.left request.right)) before
          (.code ((compileNode request).bind next)) first :=
        .cons _ _ _ _ _ _ _ one (.refl _ _)
      exact bodies bodySteps (by omega) next first middle result origin body

end MicroCFTA.SourceCurrentAllocatedNativeNodeQueryResult
