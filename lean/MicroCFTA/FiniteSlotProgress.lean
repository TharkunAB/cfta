import Std

/-! Finite slot counts decrease when a present true target becomes false. -/
set_option autoImplicit false
namespace MicroCFTA.FiniteSlotProgress

private theorem countP_le_of_pointwise {α : Type _} (slots : List α) (before after : α → Bool)
    (monotone : ∀ other ∈ slots, after other = true → before other = true) :
    slots.countP after ≤ slots.countP before := by
  revert monotone
  induction slots with
  | nil => intro _; simp
  | cons head tail inductionHyp =>
      intro monotone
      have tailLe := inductionHyp (by
        intro other member observed
        exact monotone other (by simp [member]) observed)
      have headMono := monotone head (by simp)
      cases beforeHead : before head with
      | false =>
          cases afterHead : after head with
          | false =>
              simpa [List.countP_cons, beforeHead, afterHead, Nat.one_add] using tailLe
          | true =>
              have impossible := headMono afterHead
              simp [beforeHead] at impossible
      | true =>
          cases afterHead : after head with
          | false =>
              simpa [List.countP_cons, beforeHead, afterHead, Nat.one_add] using
                Nat.le_succ_of_le tailLe
          | true =>
              simpa [List.countP_cons, beforeHead, afterHead, Nat.one_add] using
                Nat.succ_le_succ tailLe

/-- Duplicate targets are allowed. Every other listed slot keeps its original predicate value. -/
theorem countP_lt_of_target_cleared (slots : List Nat) (before after : Nat → Bool)
    (target : Nat) (present : target ∈ slots)
    (beforeTarget : before target = true) (afterTarget : after target = false)
    (unchanged : ∀ other ∈ slots, other ≠ target → after other = before other) :
    slots.countP after < slots.countP before := by
  revert present unchanged
  induction slots with
  | nil => intro present _; simp at present
  | cons head tail inductionHyp =>
      intro present unchanged
      have tailUnchanged : ∀ other ∈ tail, other ≠ target → after other = before other := by
        intro other member different
        exact unchanged other (by simp [member]) different
      by_cases headTarget : head = target
      · subst head
        have tailLe := countP_le_of_pointwise tail before after (by
          intro other member observed
          by_cases same : other = target
          · subst other
            simp [afterTarget] at observed
          · rw [tailUnchanged other member same] at observed
            exact observed)
        simpa [List.countP_cons, beforeTarget, afterTarget, Nat.one_add] using
          Nat.lt_succ_of_le tailLe
      · have targetTail : target ∈ tail := by
          rcases List.mem_cons.mp present with same | member
          · exact False.elim (headTarget same.symm)
          · exact member
        have tailLt := inductionHyp targetTail tailUnchanged
        have headSame : after head = before head := unchanged head (by simp) headTarget
        cases beforeHead : before head with
        | false =>
            simpa [List.countP_cons, headSame, beforeHead, Nat.one_add] using tailLt
        | true =>
            simpa [List.countP_cons, headSame, beforeHead, Nat.one_add] using
              Nat.succ_lt_succ tailLt

/-- Duplicate slots are allowed. Other slots can also change from true to false. -/
theorem countP_lt_of_pointwise_target_cleared {α : Type _}
    (slots : List α) (before after : α → Bool) (target : α)
    (monotone : ∀ other ∈ slots, after other = true → before other = true)
    (present : target ∈ slots) (beforeTarget : before target = true)
    (afterTarget : after target = false) :
    slots.countP after < slots.countP before := by
  revert present monotone
  induction slots with
  | nil => intro _ present; simp at present
  | cons head tail inductionHyp =>
      intro monotone present
      have tailMono : ∀ other ∈ tail, after other = true → before other = true := by
        intro other member observed
        exact monotone other (by simp [member]) observed
      have headMono := monotone head (by simp)
      rcases List.mem_cons.mp present with same | targetTail
      · subst head
        have tailLe := countP_le_of_pointwise tail before after tailMono
        simpa [List.countP_cons, beforeTarget, afterTarget, Nat.one_add] using
          Nat.lt_succ_of_le tailLe
      · have tailLt := inductionHyp tailMono targetTail
        cases beforeHead : before head with
        | false =>
            cases afterHead : after head with
            | false =>
                simpa [List.countP_cons, beforeHead, afterHead, Nat.one_add] using tailLt
            | true =>
                have impossible := headMono afterHead
                simp [beforeHead] at impossible
        | true =>
            cases afterHead : after head with
            | false =>
                simpa [List.countP_cons, beforeHead, afterHead, Nat.one_add] using
                  Nat.lt_succ_of_le (Nat.le_of_lt tailLt)
            | true =>
                simpa [List.countP_cons, beforeHead, afterHead, Nat.one_add] using
                  Nat.succ_lt_succ tailLt

end MicroCFTA.FiniteSlotProgress
