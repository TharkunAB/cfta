import MicroCFTA.EnumerationCompressionFrame
import MicroCFTA.EnumerationExecution

/-!
# Enumeration observations under path compression

Related inputs have the same values and root paths. Successful primitive
observations return equal results and retain a complete frame. A successful
observation also gives a finite bound for the related input.
-/

namespace MicroCFTA.EnumerationCompressionFrame

/-- Reverse every field equality and every root-path equivalence. -/
theorem Frame.symm (frame : Frame before after) : Frame after before :=
  ⟨frame.counter.symm, frame.values.symm, frame.obligations.symm,
    frame.recursionAncestry.symm, frame.expansionAncestry.symm,
    fun uv root size => (frame.reaches uv root size).symm⟩

end MicroCFTA.EnumerationCompressionFrame

namespace MicroCFTA.EnumerationObservations
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

variable {Symbol Guard : Type}

/-- Independent successful representative reads give the same root and a final frame. -/
theorem representative_agrees (leftFuel rightFuel uv : Nat)
    (left right leftAfter rightAfter : State Symbol Guard) (leftRoot rightRoot : Nat)
    (frame : Frame left right) (total : UnionFind.Total left.representatives)
    (leftRead : Success (representative leftFuel uv) left leftRoot leftAfter)
    (rightRead : Success (representative rightFuel uv) right rightRoot rightAfter) :
    leftRoot = rightRoot ∧ Frame leftAfter rightAfter := by
  obtain ⟨leftFound, leftLookup, leftRootEq, _⟩ :=
    (representative_success leftFuel uv left leftAfter leftRoot).mp leftRead
  obtain ⟨rightFound, rightLookup, rightRootEq, _⟩ :=
    (representative_success rightFuel uv right rightAfter rightRoot).mp rightRead
  have leftPath := (UnionFind.findRoot_correct leftFuel left.representatives uv leftFound leftLookup).1
  have rightPath := (UnionFind.findRoot_correct rightFuel right.representatives uv rightFound rightLookup).1
  have same := (UnionFind.reaches_unique leftPath
    ((frame.reaches uv rightFound.representative rightFound.size).mp rightPath)).1
  have leftFrame := representative_frame leftFuel uv leftRoot left leftAfter total leftRead
  have rightFrame := representative_frame rightFuel uv rightRoot right rightAfter (frame.total total) rightRead
  exact ⟨leftRootEq.trans (same.trans rightRootEq.symm), leftFrame.symm.trans (frame.trans rightFrame)⟩

/-- Independent successful slot reads give the same complete value and a final frame. -/
theorem getValue_agrees (leftFuel rightFuel uv : Nat)
    (left right leftAfter rightAfter : State Symbol Guard) (leftValue rightValue : UVarValue Symbol)
    (frame : Frame left right) (total : UnionFind.Total left.representatives)
    (leftRead : Success (getValue leftFuel uv) left leftValue leftAfter)
    (rightRead : Success (getValue rightFuel uv) right rightValue rightAfter) :
    leftValue = rightValue ∧ Frame leftAfter rightAfter := by
  obtain ⟨leftFrame, leftRoot, leftSize, leftPath, _, leftStored⟩ :=
    getValue_frame leftFuel uv left leftAfter leftValue total leftRead
  obtain ⟨rightFrame, rightRoot, rightSize, rightPath, _, rightStored⟩ :=
    getValue_frame rightFuel uv right rightAfter rightValue (frame.total total) rightRead
  have same := (UnionFind.reaches_unique leftPath
    ((frame.reaches uv rightRoot rightSize).mp rightPath)).1
  have rightStoredAtLeft : left.values[leftRoot]? = some rightValue := by
    rw [frame.values, ← same] at rightStored
    exact rightStored
  exact ⟨Option.some.inj (leftStored.symm.trans rightStoredAtLeft),
    leftFrame.symm.trans (frame.trans rightFrame)⟩

/-- One successful representative read gives an actual finite read in the related state. -/
theorem representative_transport (leftFuel uv : Nat)
    (left right leftAfter : State Symbol Guard) (root : Nat)
    (frame : Frame left right) (total : UnionFind.Total left.representatives)
    (leftRead : Success (representative leftFuel uv) left root leftAfter) :
    ∃ rightFuel rightAfter,
      Success (representative rightFuel uv) right root rightAfter ∧ Frame leftAfter rightAfter := by
  obtain ⟨rightFuel, rightRoot, rightAfter, rightRead, _⟩ :=
    EnumerationExecution.representative_terminates right (frame.total total) uv
  obtain ⟨same, finalFrame⟩ :=
    representative_agrees leftFuel rightFuel uv left right leftAfter rightAfter root rightRoot
      frame total leftRead rightRead
  exact ⟨rightFuel, rightAfter, same.symm ▸ rightRead, finalFrame⟩

/-- An observed slot supplies the readability needed by the related finite read. -/
theorem getValue_transport (leftFuel uv : Nat)
    (left right leftAfter : State Symbol Guard) (value : UVarValue Symbol)
    (frame : Frame left right) (total : UnionFind.Total left.representatives)
    (leftRead : Success (getValue leftFuel uv) left value leftAfter) :
    ∃ rightFuel rightAfter,
      Success (getValue rightFuel uv) right value rightAfter ∧ Frame leftAfter rightAfter := by
  obtain ⟨_, root, size, path, _, stored⟩ := getValue_frame leftFuel uv left leftAfter value total leftRead
  have rightPath := (frame.reaches uv root size).mpr path
  obtain ⟨rightFuel, found, lookup⟩ := UnionFind.findRoot_terminates rightPath
  have actual := (UnionFind.findRoot_correct rightFuel right.representatives uv found lookup).1
  have same := (UnionFind.reaches_unique actual rightPath).1
  have rightStored : right.values[found.representative]? = some value := by
    rw [frame.values, same]
    exact stored
  let rightAfter : State Symbol Guard := {right with representatives := found.forest}
  have rightRead : Success (getValue rightFuel uv) right value rightAfter :=
    (getValue_success rightFuel uv right rightAfter value).mpr ⟨found, lookup, rightStored, rfl⟩
  exact ⟨rightFuel, rightAfter, rightRead,
    (getValue_agrees leftFuel rightFuel uv left right leftAfter rightAfter value value
      frame total leftRead rightRead).2⟩

end MicroCFTA.EnumerationObservations
