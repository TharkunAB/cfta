import MicroCFTA.SourceCurrentAllocatedNativeMuSource
import MicroCFTA.SourceCurrentAllocatedNativePhysicalTraceCompletion
import MicroCFTA.SourceCurrentAllocatedNativeSemanticHeap

/-!
# Contextual Mu meaning through the actual checked body

The actual entered child trace supplies physical checks. These checks retain
the semantic heap from the initial state. Available child output completes
the optional binder. Its local contextual law then derives the parent law.
The recursive proof must still construct the child trace and child law.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeMuBodyMeaning
open Language Cache InternedBinderProtocol InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionInputView
open SourceRecursiveIntersectionCode SourceEqualityNativeDemand SourceCurrentAllocatedNativeContextCache
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable {width : Nat}

/-- Actual child checks and the available child value derive the complete source Mu body. -/
theorem mu_body [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Term Symbol → Bool) (model : IntersectSchedule.InputMeaning (view source holds))
    (ranked : IntersectSchedule.RankedInput (view source holds) model.valid)
    (request : NodeRequest Symbol Guard) (inputs : NodeInputs (view source holds) model request)
    (leftAvailable : Available source request.left) (rightAvailable : Available source request.right)
    (before middle : SourceEqualityNativeDemand.State width)
    (cacheValid : Cache.Valid before.native.machine.domains)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before.native.machine.heap)
    (first second : Nat)
    (leftIdentity : SourceRecursiveIntersectionControl.identity request.left = some first)
    (rightIdentity : SourceRecursiveIntersectionControl.identity request.right = some second)
    (leftNonempty : inputOf request.left ≠ .empty) (rightNonempty : inputOf request.right ≠ .empty)
    (recursive : (∃ name, inputOf request.left = .mu name) ∨ ∃ name, inputOf request.right = .mu name)
    (selected : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .bothMu ∨
      SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .leftMu ∨
      SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .rightMu)
    (fresh : SourceRecursiveIntersectionControl.pair first second ∉ request.domain.key.seen)
    (bodyValue : Value Symbol Guard) (fuel : Nat)
    (child : SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace fuel
      (.code (requestNode
        (SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains request.domain.key
          request.left request.right first second).1
        (SourceRecursiveIntersectionKernel.body request.left) (SourceRecursiveIntersectionKernel.body request.right)))
      {before with native := advance before.native {before.native.machine with domains :=
        (SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains request.domain.key
          request.left request.right first second).2}}
      (.code (.pure bodyValue)) middle)
    (keeps : SourceEqualityRequiredCache.Keeps before.native.machine.heap middle.native.machine.heap)
    (available : Available middle.native.machine.heap bodyValue)
    (childLaw : NodeLaw (view source holds) model ranked holds
      ⟨(SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains request.domain.key
          request.left request.right first second).1,
        SourceRecursiveIntersectionKernel.body request.left, SourceRecursiveIntersectionKernel.body request.right⟩ bodyValue) :
    ∃ (value : Value Symbol Guard) (heap : InternedConstructorTemplates.State Symbol Guard),
      let after : SourceEqualityNativeDemand.State width :=
        {middle with native := advance middle.native {middle.native.machine with heap := heap}}
      execute (fuel + 3) (.code (compileNode request)) before = .done value after ∧
        NodeLaw (view source holds) model ranked holds request value ∧
        SourceEqualityRequiredCache.Keeps before.native.machine.heap after.native.machine.heap ∧
        Available after.native.machine.heap value ∧
        SourceEqualityRequiredSemanticCache.SemanticReady after.native.machine.heap := by
  have childDone := trace_done fuel _ _ middle bodyValue child.steps
  let started : SourceEqualityNativeDemand.State width :=
    {before with native := advance before.native {before.native.machine with domains :=
      (SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains request.domain.key
        request.left request.right first second).2}}
  have initialSemantic : SourceEqualityRequiredSemanticCache.SemanticReady started.native.machine.heap := semantic
  have middleSemantic := SourceCurrentAllocatedNativeSemanticHeap.execute_semantic (fuel + 1) _ started initialSemantic
    (SourceCurrentAllocatedNativePhysicalExecution.through_heap _ _ started child.plan)
  rw [childDone] at middleSemantic
  change SourceEqualityRequiredSemanticCache.SemanticReady middle.native.machine.heap at middleSemantic
  obtain ⟨value, heap, done, constructorKeeps, valueAvailable⟩ :=
    SourceEqualityNativeDemandHeapPrimitives.optionalBinder_complete (SourceRecursiveIntersectionControl.pair first second)
      bodyValue middle.native.machine.heap middleSemantic.ready available
  have law := SourceCurrentAllocatedNativeMuSource.mu_source_law source facts holds model ranked request inputs
    leftAvailable rightAvailable before.native.machine.domains cacheValid first second leftIdentity rightIdentity
    leftNonempty rightNonempty recursive fresh bodyValue value childLaw middle.native.machine.heap heap
    middleSemantic.ready.semantic middleSemantic.guarded available done
  have finalSemantic := SourceCurrentAllocatedNativeSemanticHeap.optionalBinder_semantic
    (SourceRecursiveIntersectionControl.pair first second) bodyValue middle.native.machine.heap middleSemantic available
  rw [done] at finalSemantic
  have childTrace := child.steps.bind _ _ _ _ _ (fun value =>
    .optionalBinder (SourceRecursiveIntersectionControl.pair first second) value .pure)
  let finished : SourceEqualityNativeDemand.State width :=
    {middle with native := advance middle.native {middle.native.machine with heap := heap}}
  have optionalStep : step (.code (.optionalBinder (SourceRecursiveIntersectionControl.pair first second) bodyValue .pure)) middle =
      .yielded (.code (.pure value)) finished := by
    simp only [step, SourceRecursiveIntersectionNative.step, done, lift, finished]
  have optionalTrace : Steps 1
      (.code (.optionalBinder (SourceRecursiveIntersectionControl.pair first second) bodyValue .pure)) middle
      (.code (.pure value)) finished := Steps.cons _ _ _ _ _ _ 0 optionalStep (Steps.refl _ _)
  have bodyTrace := childTrace.trans _ _ _ _ _ _ _ _ optionalTrace
  have entered := SourceCurrentAllocatedNativeMuSource.enter_prefix request before first second leftIdentity rightIdentity
  have compiled : compileNode request = compileMu request.domain request.left request.right := by
    rcases selected with selected | selected | selected <;> simp only [compileNode, selected]
  refine ⟨value, heap, ?_⟩
  refine ⟨?_, law, keeps.trans constructorKeeps, valueAvailable, finalSemantic⟩
  rw [compiled]
  exact trace_done (fuel + 2) _ before _ value (Steps.cons _ _ _ _ _ _ (fuel + 1) entered bodyTrace)

end MicroCFTA.SourceCurrentAllocatedNativeMuBodyMeaning
