import MicroCFTA.EnumerationObservations
import MicroCFTA.EnumerationUntil

/-!
# Root-fragment observation under path compression

The public partial path reads the root before rendering. The read retains
the original root hole when the stored value is not enumerated.
-/
namespace MicroCFTA.EnumerationObservations
open Fragments EnumerationState EnumerationCorrectness EnumerationCompressionFrame EnumerationUntil

local instance rootObservationMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

variable {Symbol Guard : Type}

/-- A root-fragment observation is the actual value read and its projection. -/
theorem rootFragment_success (fuel : Nat) (before after : State Symbol Guard)
    (fragment : Fragment Symbol) :
    Success (rootFragment fuel) before fragment after ↔
      ∃ value, Success (getValue (fuel + 1) 0) before value after ∧
        fragment = (match value with | .enumerated stored => stored | _ => .hole 0) := by
  unfold rootFragment
  constructor
  · intro success
    obtain ⟨value, middle, reading, final⟩ := (success_bind _ _ _ _ _).mp success
    cases value with
    | enumerated stored =>
        obtain ⟨projected, same⟩ := (success_pure stored fragment middle after).mp final
        subst after
        exact ⟨.enumerated stored, reading, projected⟩
    | unenumerated node scs =>
        obtain ⟨projected, same⟩ := (success_pure (.hole 0) fragment middle after).mp final
        subst after
        exact ⟨.unenumerated node scs, reading, projected⟩
    | eliminated =>
        obtain ⟨projected, same⟩ := (success_pure (.hole 0) fragment middle after).mp final
        subst after
        exact ⟨.eliminated, reading, projected⟩
  · rintro ⟨value, reading, projected⟩
    apply (success_bind _ _ _ _ _).mpr
    refine ⟨value, after, reading, ?_⟩
    cases value <;> exact (success_pure _ fragment after after).mpr ⟨projected, rfl⟩

/-- Reading the root fragment preserves every field and exact root paths. -/
theorem rootFragment_frame (fuel : Nat) (before after : State Symbol Guard)
    (fragment : Fragment Symbol) (total : UnionFind.Total before.representatives)
    (success : Success (rootFragment fuel) before fragment after) : Frame before after := by
  obtain ⟨value, reading, _⟩ := (rootFragment_success fuel before after fragment).mp success
  exact (getValue_frame (fuel + 1) 0 before after value total reading).1

/-- Independent successful root observations agree and preserve the final frame. -/
theorem rootFragment_agrees (leftFuel rightFuel : Nat)
    (left right leftAfter rightAfter : State Symbol Guard) (leftFragment rightFragment : Fragment Symbol)
    (frame : Frame left right) (total : UnionFind.Total left.representatives)
    (leftRead : Success (rootFragment leftFuel) left leftFragment leftAfter)
    (rightRead : Success (rootFragment rightFuel) right rightFragment rightAfter) :
    leftFragment = rightFragment ∧ Frame leftAfter rightAfter := by
  obtain ⟨leftValue, leftReading, leftProjected⟩ :=
    (rootFragment_success leftFuel left leftAfter leftFragment).mp leftRead
  obtain ⟨rightValue, rightReading, rightProjected⟩ :=
    (rootFragment_success rightFuel right rightAfter rightFragment).mp rightRead
  obtain ⟨same, finalFrame⟩ := getValue_agrees (leftFuel + 1) (rightFuel + 1) 0
    left right leftAfter rightAfter leftValue rightValue frame total leftReading rightReading
  refine ⟨?_, finalFrame⟩
  rw [leftProjected, rightProjected, same]

/-- One root observation constructs a finite observation in the related input. -/
theorem rootFragment_transport (leftFuel : Nat) (left right leftAfter : State Symbol Guard)
    (fragment : Fragment Symbol) (frame : Frame left right) (total : UnionFind.Total left.representatives)
    (leftRead : Success (rootFragment leftFuel) left fragment leftAfter) :
    ∃ rightFuel rightAfter, Success (rootFragment rightFuel) right fragment rightAfter ∧
      Frame leftAfter rightAfter := by
  obtain ⟨value, reading, projected⟩ := (rootFragment_success leftFuel left leftAfter fragment).mp leftRead
  obtain ⟨rightFuel, rightAfter, rightReading, finalFrame⟩ :=
    getValue_transport (leftFuel + 1) 0 left right leftAfter value frame total reading
  have extended := EnumerationExecution.getValue_moreFuel rightFuel 1 0 right value rightAfter rightReading
  exact ⟨rightFuel, rightAfter,
    (rootFragment_success rightFuel right rightAfter fragment).mpr ⟨value, extended, projected⟩, finalFrame⟩

/-- More fuel retains the exact root-fragment observation and final state. -/
theorem rootFragment_moreFuel (fuel extra : Nat) :
    EnumerationExecution.Retains (rootFragment (Symbol := Symbol) (Guard := Guard) fuel)
      (rootFragment (fuel + extra)) := by
  intro before fragment after success
  obtain ⟨value, reading, projected⟩ := (rootFragment_success fuel before after fragment).mp success
  have extended := EnumerationExecution.getValue_moreFuel (fuel + 1) extra 0 before value after reading
  apply (rootFragment_success (fuel + extra) before after fragment).mpr
  exact ⟨value, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using extended, projected⟩

end MicroCFTA.EnumerationObservations
