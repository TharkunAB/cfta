import MicroCFTA.EnumerationPartialObservation

/-!
# Agreement of successful partial observations

The observed bounds are independent. Related inputs return the same partial
term and retain a complete compression frame between their final states.
-/
namespace MicroCFTA.EnumerationObservations
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationCompressionFrame

local instance partialCongruenceMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

variable {Symbol Guard : Type}

private theorem partialChildren_agree (graph : Graph Symbol Guard) (leftFuel rightFuel : Nat)
    (paired : ∀ fragment (left right leftAfter rightAfter : State Symbol Guard)
      (leftTerm rightTerm : Term (PartialSymbol Symbol)), Frame left right →
      UnionFind.Total left.representatives →
      Success (expandPartial graph leftFuel fragment) left leftTerm leftAfter →
      Success (expandPartial graph rightFuel fragment) right rightTerm rightAfter →
      leftTerm = rightTerm ∧ Frame leftAfter rightAfter)
    (children : List (Fragment Symbol)) (left right leftAfter rightAfter : State Symbol Guard)
    (leftTerms rightTerms : List (Term (PartialSymbol Symbol))) (frame : Frame left right)
    (total : UnionFind.Total left.representatives)
    (leftRead : Success (children.mapM (expandPartial graph leftFuel)) left leftTerms leftAfter)
    (rightRead : Success (children.mapM (expandPartial graph rightFuel)) right rightTerms rightAfter) :
    leftTerms = rightTerms ∧ Frame leftAfter rightAfter := by
  induction children generalizing left right leftTerms rightTerms with
  | nil =>
      obtain ⟨leftEq, leftSame⟩ := (success_pure [] leftTerms left leftAfter).mp leftRead
      obtain ⟨rightEq, rightSame⟩ := (success_pure [] rightTerms right rightAfter).mp rightRead
      exact ⟨leftEq.trans rightEq.symm, by simpa only [leftSame, rightSame] using frame⟩
  | cons child rest ih =>
      rw [List.mapM_cons] at leftRead rightRead
      obtain ⟨leftTerm, leftMiddle, leftFirst, leftContinued⟩ := (success_bind _ _ _ _ _).mp leftRead
      obtain ⟨leftTail, leftLast, leftRest, leftFinal⟩ := (success_bind _ _ _ _ _).mp leftContinued
      obtain ⟨rightTerm, rightMiddle, rightFirst, rightContinued⟩ := (success_bind _ _ _ _ _).mp rightRead
      obtain ⟨rightTail, rightLast, rightRest, rightFinal⟩ := (success_bind _ _ _ _ _).mp rightContinued
      obtain ⟨sameFirst, middleFrame⟩ := paired child left right leftMiddle rightMiddle
        leftTerm rightTerm frame total leftFirst rightFirst
      have middleTotal := (expandPartial_frame graph leftFuel child left leftMiddle leftTerm total leftFirst).total total
      obtain ⟨sameTail, lastFrame⟩ := ih leftMiddle rightMiddle leftTail rightTail middleFrame middleTotal leftRest rightRest
      obtain ⟨leftEq, leftSame⟩ := (success_pure (leftTerm :: leftTail) leftTerms leftLast leftAfter).mp leftFinal
      obtain ⟨rightEq, rightSame⟩ := (success_pure (rightTerm :: rightTail) rightTerms rightLast rightAfter).mp rightFinal
      refine ⟨?_, ?_⟩
      · rw [leftEq, rightEq, sameFirst, sameTail]
      · simpa only [leftSame, rightSame] using lastFrame

/-- Independent successful partial renders agree and retain the full final frame. -/
theorem expandPartial_agrees (graph : Graph Symbol Guard) (leftFuel rightFuel : Nat)
    (fragment : Fragment Symbol) (left right leftAfter rightAfter : State Symbol Guard)
    (leftTerm rightTerm : Term (PartialSymbol Symbol)) (frame : Frame left right)
    (total : UnionFind.Total left.representatives)
    (leftRead : Success (expandPartial graph leftFuel fragment) left leftTerm leftAfter)
    (rightRead : Success (expandPartial graph rightFuel fragment) right rightTerm rightAfter) :
    leftTerm = rightTerm ∧ Frame leftAfter rightAfter := by
  induction leftFuel generalizing rightFuel fragment left right leftAfter rightAfter leftTerm rightTerm with
  | zero => exact (success_failure .fuelExhausted left leftAfter leftTerm leftRead).elim
  | succ leftFuel ih =>
      cases rightFuel with
      | zero => exact (success_failure .fuelExhausted right rightAfter rightTerm rightRead).elim
      | succ rightFuel =>
          cases fragment with
          | node symbol children =>
              change Success (children.mapM (expandPartial graph leftFuel) >>= fun terms =>
                pure (.node (.concrete symbol) terms)) left leftTerm leftAfter at leftRead
              change Success (children.mapM (expandPartial graph rightFuel) >>= fun terms =>
                pure (.node (.concrete symbol) terms)) right rightTerm rightAfter at rightRead
              obtain ⟨leftTerms, leftMiddle, leftChildren, leftFinal⟩ := (success_bind _ _ _ _ _).mp leftRead
              obtain ⟨rightTerms, rightMiddle, rightChildren, rightFinal⟩ := (success_bind _ _ _ _ _).mp rightRead
              obtain ⟨same, middleFrame⟩ := partialChildren_agree graph leftFuel rightFuel (ih rightFuel)
                children left right leftMiddle rightMiddle leftTerms rightTerms frame total leftChildren rightChildren
              obtain ⟨leftEq, leftSame⟩ := (success_pure _ leftTerm leftMiddle leftAfter).mp leftFinal
              obtain ⟨rightEq, rightSame⟩ := (success_pure _ rightTerm rightMiddle rightAfter).mp rightFinal
              refine ⟨?_, ?_⟩
              · rw [leftEq, rightEq, same]
              · simpa only [leftSame, rightSame] using middleFrame
          | hole uv =>
              change Success (getValue (leftFuel + 1) uv >>= fun value => match value with
                | .enumerated stored => expandPartial graph leftFuel stored
                | .unenumerated (some node) [] => match graph.node node with
                  | .recursive _ => pure (.node .truncated [])
                  | _ => pure (.node (.hole uv) [])
                | _ => pure (.node (.hole uv) [])) left leftTerm leftAfter at leftRead
              change Success (getValue (rightFuel + 1) uv >>= fun value => match value with
                | .enumerated stored => expandPartial graph rightFuel stored
                | .unenumerated (some node) [] => match graph.node node with
                  | .recursive _ => pure (.node .truncated [])
                  | _ => pure (.node (.hole uv) [])
                | _ => pure (.node (.hole uv) [])) right rightTerm rightAfter at rightRead
              obtain ⟨leftValue, leftMiddle, leftReading, leftFinal⟩ := (success_bind _ _ _ _ _).mp leftRead
              obtain ⟨rightValue, rightMiddle, rightReading, rightFinal⟩ := (success_bind _ _ _ _ _).mp rightRead
              obtain ⟨same, readFrame⟩ := getValue_agrees (leftFuel + 1) (rightFuel + 1) uv
                left right leftMiddle rightMiddle leftValue rightValue frame total leftReading rightReading
              subst rightValue
              have middleTotal := (getValue_frame (leftFuel + 1) uv left leftMiddle leftValue total leftReading).1.total total
              have terminal (produced : Term (PartialSymbol Symbol))
                  (leftPure : Success (pure produced) leftMiddle leftTerm leftAfter)
                  (rightPure : Success (pure produced) rightMiddle rightTerm rightAfter) :
                  leftTerm = rightTerm ∧ Frame leftAfter rightAfter := by
                obtain ⟨leftEq, leftSame⟩ := (success_pure produced leftTerm leftMiddle leftAfter).mp leftPure
                obtain ⟨rightEq, rightSame⟩ := (success_pure produced rightTerm rightMiddle rightAfter).mp rightPure
                exact ⟨leftEq.trans rightEq.symm, by simpa only [leftSame, rightSame] using readFrame⟩
              cases leftValue with
              | eliminated => exact terminal _ leftFinal rightFinal
              | enumerated stored =>
                  exact ih rightFuel stored leftMiddle rightMiddle leftAfter rightAfter
                    leftTerm rightTerm readFrame middleTotal leftFinal rightFinal
              | unenumerated node scs =>
                  cases node with
                  | none => exact terminal _ leftFinal rightFinal
                  | some node =>
                      cases scs with
                      | cons first rest => exact terminal _ leftFinal rightFinal
                      | nil =>
                          cases view : graph.node node <;> simp only [view] at leftFinal rightFinal <;>
                            exact terminal _ leftFinal rightFinal

end MicroCFTA.EnumerationObservations
