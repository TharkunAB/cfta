import MicroCFTA.FiniteSource
import MicroCFTA.RecursionProbe

/-!
# Minimum sizes of finite generator source expressions

The metadata follows source, pure, pay, atomic, choice, product, and sized
construction. Every represented member proves that the computed minimum is
finite and is a lower bound for its size. Recursive guard proofs use this
derived fact to justify positive sibling costs.
-/

namespace MicroCFTA.SourceMinimum
open FiniteSource

/-- Live classes of a bounded sized source, in ascending size order. -/
def liveSizes (classes : Nat → Probability.Distribution α) (bound : Nat) : List Nat :=
  (List.range (bound + 1)).filter fun size => !(classes size).isEmpty

/-- Compute the finite source's minimum with the actual source metadata operations. -/
def minimum : Source α → Option Nat
  | .source outcomes _ => if outcomes.isEmpty then none else some 1
  | .pure _ => some 0
  | .map _ inner | .shared _ inner => minimum inner
  | .pay inner => (minimum inner).map (· + 1)
  | .atomic inner => if (members inner).isEmpty then none else some 1
  | .choice _ _ _ _ left right => MinimumSize.best (minimum left) (minimum right)
  | .ap functions arguments => RecursionProbe.productMinimum (minimum functions) (minimum arguments)
  | .sized classes _ bound => (liveSizes classes bound).min?

/-- Any size member gives a finite minimum no larger than that member's size. -/
theorem member_bound (description : Source α) (size : Nat) (value : α)
    (present : value ∈ classMembers description size) :
    ∃ lower, minimum description = some lower ∧ lower ≤ size := by
  induction description generalizing size with
  | source outcomes positive =>
      by_cases same : size = 1
      · have member : value ∈ outcomes.map Prod.snd := by simpa [classMembers, same] using present
        have nonempty : outcomes ≠ [] := by intro empty; simp [empty] at member
        exact ⟨1, by simp [minimum, List.isEmpty_eq_false_iff.mpr nonempty], by omega⟩
      · simp [classMembers, same] at present
  | pure original =>
      by_cases same : size = 0
      · exact ⟨0, rfl, by omega⟩
      · simp [classMembers, same] at present
  | map transform inner ih =>
      obtain ⟨original, member, _⟩ := List.mem_map.mp present
      exact ih size original member
  | pay inner ih =>
      cases size with
      | zero => simp [classMembers] at present
      | succ size =>
          obtain ⟨lower, found, bound⟩ := ih size value present
          exact ⟨lower + 1, by simp [minimum, found], by omega⟩
  | atomic inner ih =>
      by_cases same : size = 1
      · have member : value ∈ members inner := by simpa [classMembers, same] using present
        have nonempty : members inner ≠ [] := List.ne_nil_of_mem member
        exact ⟨1, by simp [minimum, List.isEmpty_eq_false_iff.mpr nonempty], by omega⟩
      · simp [classMembers, same] at present
  | shared key inner ih => exact ih size value present
  | choice lw rw lp rp left right ihl ihr =>
      rcases List.mem_append.mp present with leftMember | rightMember
      · obtain ⟨lower, found, bound⟩ := ihl size value leftMember
        obtain ⟨smallest, kept, smaller⟩ := MinimumSize.best_improves_left (minimum left) (minimum right) lower found
        exact ⟨smallest, kept, by omega⟩
      · obtain ⟨lower, found, bound⟩ := ihr size value rightMember
        obtain ⟨smallest, kept, smaller⟩ := MinimumSize.best_improves_right (minimum left) (minimum right) lower found
        exact ⟨smallest, kept, by omega⟩
  | ap functions arguments ihf iha =>
      obtain ⟨split, within, member⟩ := List.mem_flatMap.mp present
      obtain ⟨function, functionMember, argument, argumentMember, _⟩ :=
        (by simpa [Decoder.applyValues] using member :
          ∃ function, function ∈ classMembers functions split ∧
            ∃ argument, argument ∈ classMembers arguments (size - split) ∧ function argument = value)
      obtain ⟨leftMinimum, leftFound, leftBound⟩ := ihf split function functionMember
      obtain ⟨rightMinimum, rightFound, rightBound⟩ := iha (size - split) argument argumentMember
      have splitBound : split ≤ size := by have := List.mem_range.mp within; omega
      exact ⟨leftMinimum + rightMinimum, by simp [minimum, RecursionProbe.productMinimum, leftFound, rightFound], by omega⟩
  | sized classes positive bound =>
      by_cases within : size ≤ bound
      · have member : value ∈ (classes size).map Prod.snd := by simpa [classMembers, within] using present
        have nonempty : classes size ≠ [] := by intro empty; simp [empty] at member
        have live : size ∈ liveSizes classes bound := by
          simp [liveSizes, show size < bound + 1 by omega, List.isEmpty_eq_false_iff.mpr nonempty]
        cases found : (liveSizes classes bound).min? with
        | none => have empty := List.min?_eq_none_iff.mp found; simp [empty] at live
        | some smallest => exact ⟨smallest, found, (List.min?_eq_some_iff.mp found).2 size live⟩
      · simp [classMembers, within] at present

/-- A source with no finite minimum has no member in any size class. -/
theorem none_is_empty (description : Source α) (absent : minimum description = none) (size : Nat) :
    classMembers description size = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro value present
  obtain ⟨lower, found, _⟩ := member_bound description size value present
  simp [absent] at found

end MicroCFTA.SourceMinimum
