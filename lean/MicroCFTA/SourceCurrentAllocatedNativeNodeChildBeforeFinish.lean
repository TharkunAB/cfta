import MicroCFTA.SourceEqualityNativeDemandProtectedPrefix
import MicroCFTA.SourceCurrentHereditaryNativePhysicalSplit

/-!
# Completed child calls before an observed parent finish

The proof uses the literal captured finish continuation.
The completed child retains that continuation before the parent finish.
The actual root trace supplies the child input checks and the suffix.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeNodeChildBeforeFinish
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State

set_option autoImplicit false

private theorem bind_finish_ne_pure (code : Code Symbol Guard Node) (owner : Nat) (expected : Node) :
    code.bind (fun value => .finishNode owner value (.pure value)) ≠ .pure expected := by
  cases code <;> intro impossible <;> cases impossible

private theorem node_child_continuation_nonpure
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (count owner : Nat) (code : Code Symbol Guard Node) (child : NodeRequest Symbol Guard)
    (childNext : Node → Code Symbol Guard Node) (before after : Checked width)
    (actual : Steps count
      ((.code code : Control Node).bind (fun value => .finishNode owner value (.pure value))) before
      (.code (.node child childNext)) after) :
    ∀ value expected, childNext value ≠ .pure expected := by
  rcases steps_bind_cases count (.code code) (fun value => .finishNode owner value (.pure value))
      before after (.code (.node child childNext)) actual with
    ⟨inner, _, _, same⟩ | ⟨_, outer, value, middle, _, _, outerActual⟩
  · cases inner with
    | edgeBody => cases same
    | code inner =>
        cases inner with
        | node request next =>
            change (.code (.node child childNext) : Control Node) =
              .code (.node request (fun result => (next result).bind
                (fun result => .finishNode owner result (.pure result)))) at same
            have tails := (Code.node.inj (Control.code.inj same)).2
            intro result expected impossible
            exact bind_finish_ne_pure (next result) owner expected
              ((congrFun tails result).symm.trans impossible)
        | pure | fail | work | enter | read | optionalBinder | edge | finishNode | finishEdge => cases same
  · rcases SourceEqualityNativeDemandProtectedPrefix.finish_node_cases outer owner value (.pure value)
        middle after (.code (.node child childNext)) outerActual with
      ⟨_, same, _⟩ | ⟨rest, _, restActual⟩
    · cases same
    · cases rest with
      | zero =>
          have same := (steps_zero _ _ _ _ restActual).1
          cases same
      | succ rest =>
          obtain ⟨_, _, one, _⟩ := steps_succ rest _ _ _ _ restActual
          cases one

/-- A completed child stays within the same observed parent body and original budget. -/
theorem completed_node_child_span_before_parent_finish
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat} {Output : Type}
    (initial : Control Output) (outside : Node → Code Symbol Guard Output)
    (parent child : NodeRequest Symbol Guard) (owner : Nat)
    (start queryBefore beforeBody beforeFinish childBefore childAfter : Checked width)
    (parentFuel bodyCount queryUsed childUsed childCount : Nat) (parentValue childValue : Node)
    (childNext : Node → Code Symbol Guard Node)
    (bodyShape : SourceRecursiveIntersectionNative.Shape beforeBody.native)
    (running : beforeBody.native.nodes.cells owner = some ⟨parent, .evaluating⟩)
    (bodyBound : bodyCount < parentFuel)
    (whole : Trace (queryUsed + 1 + bodyCount) initial start
      (.code (.finishNode owner parentValue (outside parentValue))) beforeFinish)
    (queryPrefix : Steps queryUsed initial start
      ((.code (.node parent .pure) : Control Node).bind outside) queryBefore)
    (dispatched : Steps 1 (.code (.node parent .pure)) queryBefore
      ((.code (compileNode parent) : Control Node).bind
        (fun value => .finishNode owner value (.pure value))) beforeBody)
    (bodyActual : Steps bodyCount (.code (compileNode parent)) beforeBody
      (.code (.pure parentValue)) beforeFinish)
    (positive : 0 < childUsed)
    (childPrefix : Steps childUsed (.code (.node parent .pure)) queryBefore
      ((.code (requestNode child.domain child.left child.right) : Control Node).bind childNext) childBefore)
    (childActual : Steps childCount (.code (requestNode child.domain child.left child.right)) childBefore
      (.code (.pure childValue)) childAfter) :
    childUsed + childCount ≤ 1 + bodyCount ∧
    queryUsed + childUsed + childCount ≤ queryUsed + 1 + bodyCount ∧
    childUsed + childCount ≤ parentFuel ∧
    beforeFinish.native.nodes.cells owner = some ⟨parent, .evaluating⟩ ∧
    (SourceRecursiveIntersectionThunks.finishNode owner parentValue beforeFinish.native).nodes.cells owner =
      some ⟨parent, .returned parentValue⟩ ∧
    Trace (queryUsed + childUsed) initial start
      (.code ((requestNode child.domain child.left child.right).bind
        (fun value => (childNext value).bind outside))) childBefore ∧
    Trace childCount (.code (requestNode child.domain child.left child.right)) childBefore
      (.code (.pure childValue)) childAfter ∧
    Trace (queryUsed + childUsed + childCount) initial start
      (.code ((childNext childValue).bind outside)) childAfter ∧
    Trace (queryUsed + 1 + bodyCount - (queryUsed + childUsed + childCount))
      (.code ((childNext childValue).bind outside)) childAfter
      (.code (.finishNode owner parentValue (outside parentValue))) beforeFinish := by
  let finishParent : Node → Code Symbol Guard Node :=
    fun value => .finishNode owner value (.pure value)
  obtain ⟨next, reached, one, zero⟩ := steps_succ 0 _ _ _ _ dispatched
  obtain ⟨sameNext, sameState⟩ := steps_zero _ _ _ _ zero
  have dispatchedOne : step (.code (.node parent .pure)) queryBefore =
      .yielded ((.code (compileNode parent) : Control Node).bind finishParent) beforeBody := by
    simpa only [sameNext, sameState] using one
  have inside : Steps (childUsed - 1)
      ((.code (compileNode parent) : Control Node).bind finishParent) beforeBody
      (.code (.node child childNext)) childBefore := by
    cases childUsed with
    | zero => omega
    | succ remaining =>
        obtain ⟨other, advanced, first, tail⟩ := steps_succ remaining _ _ _ _ childPrefix
        obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj (first.symm.trans dispatchedOne)
        have remainingCount : remaining + 1 - 1 = remaining := by omega
        rw [remainingCount]
        exact tail
  have nonpure := node_child_continuation_nonpure (childUsed - 1) owner
    (compileNode parent) child childNext beforeBody childBefore inside
  let finished : Checked width :=
    {beforeFinish with native := SourceRecursiveIntersectionThunks.finishNode owner parentValue beforeFinish.native}
  have finishActual : Steps 1 (.code (.finishNode owner parentValue (.pure parentValue))) beforeFinish
      (.code (.pure parentValue)) finished := by
    exact .cons _ _ _ _ _ _ 0 rfl (.refl _ _)
  have bodyBoundActual := Steps.bind bodyCount _ _ beforeBody beforeFinish bodyActual finishParent
  have bodyCompleted : Steps (bodyCount + 1)
      ((.code (compileNode parent) : Control Node).bind finishParent) beforeBody
      (.code (.pure parentValue)) finished :=
    Steps.trans bodyCount 1 _ _ _ beforeBody beforeFinish finished bodyBoundActual finishActual
  have parentCompleted : Steps (1 + bodyCount + 1) (.code (.node parent .pure)) queryBefore
      (.code (.pure parentValue)) finished := by
    have joined := Steps.trans 1 (bodyCount + 1) _ _ _ queryBefore beforeBody finished
      dispatched bodyCompleted
    simpa only [Nat.add_assoc] using joined
  have childBoundActual := Steps.bind childCount _ _ childBefore childAfter childActual childNext
  have childCompleted := Steps.trans childUsed childCount _ _ _ queryBefore childBefore childAfter
    childPrefix childBoundActual
  have bounded := Steps.length_le_complete parentCompleted childCompleted
  have different : childUsed + childCount ≠ 1 + bodyCount + 1 := by
    intro sameCount
    have childExecution := childCompleted.execute
    have parentExecution := parentCompleted.execute
    rw [sameCount] at childExecution
    have sameControl := (Outcome.yielded.inj (childExecution.symm.trans parentExecution)).1
    exact nonpure childValue parentValue (Control.code.inj sameControl)
  have localBound : childUsed + childCount ≤ 1 + bodyCount := by omega
  have globalBound : queryUsed + childUsed + childCount ≤ queryUsed + 1 + bodyCount := by omega
  have suppliedBound : childUsed + childCount ≤ parentFuel := by omega
  have ownerReceipt := SourceEqualityNativeDemandProtectedPrefix.node_body_owner bodyCount owner parent
    beforeBody beforeFinish parentValue bodyShape running bodyActual
  let childOutside : Node → Code Symbol Guard Output := fun value => (childNext value).bind outside
  have liftedStart := Steps.bind childUsed _ _ queryBefore childBefore childPrefix outside
  have rootChildStart : Steps (queryUsed + childUsed) initial start
      (.code ((requestNode child.domain child.left child.right).bind childOutside)) childBefore := by
    have joined := Steps.trans queryUsed childUsed _ _ _ start queryBefore childBefore queryPrefix liftedStart
    simpa only [Control.bind, Code.bind_assoc] using joined
  have liftedChild := Steps.bind childCount _ _ childBefore childAfter childActual childOutside
  have rootChildEnd : Steps (queryUsed + childUsed + childCount) initial start
      (.code ((childNext childValue).bind outside)) childAfter :=
    Steps.trans (queryUsed + childUsed) childCount _ _ _ start childBefore childAfter rootChildStart liftedChild
  have totalEq : queryUsed + childUsed + childCount +
      (queryUsed + 1 + bodyCount - (queryUsed + childUsed + childCount)) =
        queryUsed + 1 + bodyCount := by omega
  have checkedEnd := SourceCurrentHereditaryNativePhysicalSplit.split
    (extra := queryUsed + 1 + bodyCount - (queryUsed + childUsed + childCount)) rootChildEnd
    (by simpa only [totalEq] using whole)
  have checkedStart := SourceCurrentHereditaryNativePhysicalSplit.split
    (extra := childCount) rootChildStart checkedEnd.1
  have checkedChild := SourceCurrentHereditaryNativePhysicalSplit.unbind childActual childOutside checkedStart.2
  exact ⟨localBound, globalBound, suppliedBound, ownerReceipt.1, ownerReceipt.2,
    checkedStart.1, checkedChild, checkedEnd.1, checkedEnd.2⟩

end MicroCFTA.SourceCurrentAllocatedNativeNodeChildBeforeFinish
