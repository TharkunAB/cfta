theorem getElem?_append_left {l₁ l₂ : List α} {i : Nat} (hn : i < l₁.length) :
    (l₁ ++ l₂)[i]? = l₁[i]? := by
  have hn' : i < (l₁ ++ l₂).length := Nat.lt_of_lt_of_le hn <|
    length_append .. ▸ Nat.le_add_right ..
