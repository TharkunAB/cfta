import MicroCFTA.EnumerationObservations

/-!
# Public unexpanded-node observation through compression frames

The observer returns the stored optional node. It changes only the forest
through the existing value read. The two observed bounds are independent.
-/
namespace MicroCFTA.EnumerationObservations
open EnumerationState EnumerationCorrectness EnumerationCompressionFrame

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

variable {Symbol Guard : Type}

/-- Read the stored pending node without enumeration. -/
def getUnexpandedNode (fuel uv : Nat) : EnumerateM Symbol Guard (Option Nat) := do
  let value ← getValue fuel uv
  pure (match value with | .unenumerated node _ => node | _ => none)

/-- A successful node observation is the actual value read and its projection. -/
theorem getUnexpandedNode_success (fuel uv : Nat) (before after : State Symbol Guard) (node : Option Nat) :
    Success (getUnexpandedNode fuel uv) before node after ↔
      ∃ value, Success (getValue fuel uv) before value after ∧
        node = (match value with | .unenumerated stored _ => stored | _ => none) := by
  unfold getUnexpandedNode
  constructor
  · intro success
    obtain ⟨value, middle, reading, final⟩ := (success_bind _ _ _ _ _).mp success
    obtain ⟨projected, same⟩ := (success_pure _ node middle after).mp final
    subst after
    exact ⟨value, reading, projected⟩
  · rintro ⟨value, reading, projected⟩
    exact (success_bind _ _ _ _ _).mpr
      ⟨value, after, reading, (success_pure _ node after after).mpr ⟨projected, rfl⟩⟩

/-- Actual observations agree and retain the complete frame between final states. -/
theorem getUnexpandedNode_agrees (leftFuel rightFuel uv : Nat)
    (left right leftAfter rightAfter : State Symbol Guard) (leftNode rightNode : Option Nat)
    (frame : Frame left right) (total : UnionFind.Total left.representatives)
    (leftRead : Success (getUnexpandedNode leftFuel uv) left leftNode leftAfter)
    (rightRead : Success (getUnexpandedNode rightFuel uv) right rightNode rightAfter) :
    leftNode = rightNode ∧ Frame leftAfter rightAfter := by
  obtain ⟨leftValue, leftReading, leftProjected⟩ :=
    (getUnexpandedNode_success leftFuel uv left leftAfter leftNode).mp leftRead
  obtain ⟨rightValue, rightReading, rightProjected⟩ :=
    (getUnexpandedNode_success rightFuel uv right rightAfter rightNode).mp rightRead
  obtain ⟨same, finalFrame⟩ := getValue_agrees leftFuel rightFuel uv left right leftAfter rightAfter
    leftValue rightValue frame total leftReading rightReading
  refine ⟨?_, finalFrame⟩
  rw [leftProjected, rightProjected, same]

/-- One successful observation supplies a finite observation from the framed input. -/
theorem getUnexpandedNode_transport (leftFuel uv : Nat) (left right leftAfter : State Symbol Guard)
    (node : Option Nat) (frame : Frame left right) (total : UnionFind.Total left.representatives)
    (leftRead : Success (getUnexpandedNode leftFuel uv) left node leftAfter) :
    ∃ rightFuel rightAfter, Success (getUnexpandedNode rightFuel uv) right node rightAfter ∧
      Frame leftAfter rightAfter := by
  obtain ⟨value, reading, projected⟩ :=
    (getUnexpandedNode_success leftFuel uv left leftAfter node).mp leftRead
  obtain ⟨rightFuel, rightAfter, rightReading, finalFrame⟩ :=
    getValue_transport leftFuel uv left right leftAfter value frame total reading
  exact ⟨rightFuel, rightAfter,
    (getUnexpandedNode_success rightFuel uv right rightAfter node).mpr ⟨value, rightReading, projected⟩,
    finalFrame⟩

/-- More fuel retains an actual successful observation and its exact final state. -/
theorem getUnexpandedNode_moreFuel (fuel extra uv : Nat) :
    EnumerationExecution.Retains (getUnexpandedNode (Symbol := Symbol) (Guard := Guard) fuel uv)
      (getUnexpandedNode (fuel + extra) uv) := by
  intro before node after success
  obtain ⟨value, reading, projected⟩ := (getUnexpandedNode_success fuel uv before after node).mp success
  exact (getUnexpandedNode_success (fuel + extra) uv before after node).mpr
    ⟨value, EnumerationExecution.getValue_moreFuel fuel extra uv before value after reading, projected⟩

end MicroCFTA.EnumerationObservations
