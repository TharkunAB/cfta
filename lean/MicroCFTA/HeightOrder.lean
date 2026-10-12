import Std

/-!
# Well-founded finite height counts

A larger height has higher priority. A step can add any number of smaller
items if it removes an item at one height and does not increase counts above
that height. No fixed bound on the lower counts is required.
-/

namespace MicroCFTA.HeightOrder

/-- Compare a fixed prefix of natural counts, with the highest index first. -/
def Below : Nat → (Nat → Nat) → (Nat → Nat) → Prop
  | 0, _, _ => False
  | bound + 1, left, right => Prod.Lex Nat.lt (Below bound) (left bound, left) (right bound, right)

/-- A fixed finite height range gives a well-founded count order. -/
theorem below_wellFounded (bound : Nat) : WellFounded (Below bound) := by
  induction bound with
  | zero => exact ⟨fun counts => .intro counts (fun _ impossible => False.elim impossible)⟩
  | succ bound ih =>
    have pairs : WellFounded (Prod.Lex Nat.lt (Below bound)) :=
      (Prod.lex Nat.lt_wfRel ⟨Below bound, ih⟩).wf
    exact InvImage.wf (fun counts : Nat → Nat => (counts bound, counts)) pairs

/-- One strict decrease and nonincrease at every higher height give a strict step. -/
theorem below_of_decrease (bound : Nat) (left right : Nat → Nat) (height : Nat)
    (inside : height < bound) (strict : left height < right height)
    (higher : ∀ index, height < index → index < bound → left index ≤ right index) :
    Below bound left right := by
  induction bound with
  | zero => omega
  | succ bound ih =>
    by_cases last : height = bound
    · subst height
      exact .left _ _ strict
    · have before : height < bound := by omega
      have top := higher bound before (by omega)
      by_cases less : left bound < right bound
      · exact .left _ _ less
      · have same : left bound = right bound := by omega
        change Prod.Lex Nat.lt (Below bound) (left bound, left) (right bound, right)
        rw [same]
        exact .right _ (ih before (fun index above below => higher index above (by omega)))

/-- Extend a finite count vector by zero beyond its declared height range. -/
def extend (counts : Fin bound → Nat) (index : Nat) : Nat :=
  if inside : index < bound then counts ⟨index, inside⟩ else 0

/-- The finite-vector order uses the same descending height priorities. -/
def VectorBelow (bound : Nat) (left right : Fin bound → Nat) : Prop :=
  Below bound (extend left) (extend right)

/-- Finite vectors inherit well-foundedness without an upper bound on their entries. -/
theorem vector_wellFounded (bound : Nat) : WellFounded (VectorBelow bound) :=
  InvImage.wf extend (below_wellFounded bound)

/-- A concrete height histogram can decrease at one position and grow freely below it. -/
theorem vector_decreases (bound : Nat) (left right : Fin bound → Nat) (height : Fin bound)
    (strict : left height < right height)
    (higher : ∀ index : Fin bound, height.val < index.val → left index ≤ right index) :
    VectorBelow bound left right := by
  apply below_of_decrease bound (extend left) (extend right) height.val height.isLt
  · simpa only [extend, dite_eq_left height.isLt] using strict
  · intro index above inside
    simpa only [extend, dite_eq_left inside] using higher ⟨index, inside⟩ above

end MicroCFTA.HeightOrder
