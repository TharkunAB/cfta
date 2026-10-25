theorem getElem?_append_left {l₁ l₂ : List α} {i : Nat} (hn : i < l₁.length) :
    (l₁ ++ l₂)[i]? = l₁[i]? := by
  have hn' : i < (l₁ ++ l₂).length := Nat.lt_of_lt_of_le hn <|
    length_append .. ▸ Nat.le_add_right ..
  simp_all

theorem getElem?_append_right : ∀ {l₁ l₂ : List α} {i : Nat}, l₁.length ≤ i →
  (l₁ ++ l₂)[i]? = l₂[i - l₁.length]?
| [], _, _, _ => rfl
| a :: l, _, i+1, h₁ => by
  rw [cons_append]
  simp [Nat.succ_sub_succ_eq_sub, getElem?_append_right (Nat.lt_succ_iff.1 h₁)]
