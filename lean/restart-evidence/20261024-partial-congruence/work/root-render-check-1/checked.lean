import MicroCFTA.EnumerationRootObservation
import MicroCFTA.EnumerationPartialCongruence
import MicroCFTA.EnumerationPartialTransport

/-!
# Observation of the root and its partial term

The sequence is the actual post-driver root read and partial render.
A single bound supplies both actions within each observed execution.
-/
namespace MicroCFTA.EnumerationObservations
open Language Fragments EnumerationState EnumerationCorrectness EnumerationCompressionFrame
open EnumerationUntil EnumerationExecution

local instance rootPartialMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

variable {Symbol Guard : Type}

/-- The complete root-read and partial-render sequence preserves the frame. -/
theorem rootPartial_frame (graph : Graph Symbol Guard) (fuel : Nat)
    (before after : State Symbol Guard) (term : Term (PartialSymbol Symbol))
    (total : UnionFind.Total before.representatives)
    (success : Success (rootFragment fuel >>= expandPartial graph fuel) before term after) :
    Frame before after := by
  obtain ⟨fragment, middle, rootRead, rendered⟩ := (success_bind _ _ _ _ _).mp success
  have rootFrame := rootFragment_frame fuel before middle fragment total rootRead
  exact rootFrame.trans (expandPartial_frame graph fuel fragment middle after term
    (rootFrame.total total) rendered)

/-- Independent successful public rendering sequences give the same partial term. -/
theorem rootPartial_agrees (graph : Graph Symbol Guard) (leftFuel rightFuel : Nat)
    (left right leftAfter rightAfter : State Symbol Guard)
    (leftTerm rightTerm : Term (PartialSymbol Symbol)) (frame : Frame left right)
    (total : UnionFind.Total left.representatives)
    (leftRead : Success (rootFragment leftFuel >>= expandPartial graph leftFuel) left leftTerm leftAfter)
    (rightRead : Success (rootFragment rightFuel >>= expandPartial graph rightFuel) right rightTerm rightAfter) :
    leftTerm = rightTerm ∧ Frame leftAfter rightAfter := by
  obtain ⟨leftFragment, leftMiddle, leftRoot, leftRendered⟩ := (success_bind _ _ _ _ _).mp leftRead
  obtain ⟨rightFragment, rightMiddle, rightRoot, rightRendered⟩ := (success_bind _ _ _ _ _).mp rightRead
  obtain ⟨same, middleFrame⟩ := rootFragment_agrees leftFuel rightFuel left right leftMiddle rightMiddle
    leftFragment rightFragment frame total leftRoot rightRoot
  subst rightFragment
  have middleTotal := (rootFragment_frame leftFuel left leftMiddle leftFragment total leftRoot).total total
  exact expandPartial_agrees graph leftFuel rightFuel leftFragment leftMiddle rightMiddle
    leftAfter rightAfter leftTerm rightTerm middleFrame middleTotal leftRendered rightRendered

/-- More fuel retains the exact public rendering result and complete final state. -/
theorem rootPartial_moreFuel (graph : Graph Symbol Guard) (fuel extra : Nat) :
    Retains (rootFragment fuel >>= expandPartial graph fuel)
      (rootFragment (fuel + extra) >>= expandPartial graph (fuel + extra)) :=
  retains_bind _ _ _ _ (rootFragment_moreFuel fuel extra)
    (fun fragment => expandPartial_moreFuel graph fuel extra fragment)

/-- One public rendering sequence constructs a matching finite sequence. -/
theorem rootPartial_transport (graph : Graph Symbol Guard) (leftFuel : Nat)
    (left right leftAfter : State Symbol Guard) (term : Term (PartialSymbol Symbol))
    (frame : Frame left right) (total : UnionFind.Total left.representatives)
    (leftRead : Success (rootFragment leftFuel >>= expandPartial graph leftFuel) left term leftAfter) :
    ∃ rightFuel rightAfter,
      Success (rootFragment rightFuel >>= expandPartial graph rightFuel) right term rightAfter ∧
      Frame leftAfter rightAfter := by
  obtain ⟨fragment, leftMiddle, leftRoot, leftRendered⟩ := (success_bind _ _ _ _ _).mp leftRead
  have middleTotal := (rootFragment_frame leftFuel left leftMiddle fragment total leftRoot).total total
  obtain ⟨rootFuel, rightMiddle, rightRoot, rootFrame⟩ :=
    rootFragment_transport leftFuel left right leftMiddle fragment frame total leftRoot
  obtain ⟨renderFuel, rightAfter, rightRendered, finalFrame⟩ :=
    expandPartial_transport graph leftFuel fragment leftMiddle rightMiddle leftAfter term
      rootFrame middleTotal leftRendered
  refine ⟨rootFuel + renderFuel, rightAfter, ?_, finalFrame⟩
  apply (success_bind _ _ _ _ _).mpr
  refine ⟨fragment, rightMiddle,
    rootFragment_moreFuel rootFuel renderFuel right fragment rightMiddle rightRoot, ?_⟩
  have raised := expandPartial_moreFuel graph renderFuel rootFuel fragment rightMiddle term rightAfter rightRendered
  simpa only [Nat.add_comm] using raised

end MicroCFTA.EnumerationObservations
