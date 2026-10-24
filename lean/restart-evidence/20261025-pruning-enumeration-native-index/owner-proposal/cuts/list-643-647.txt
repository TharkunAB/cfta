@[simp] theorem getElem?_set_ne {l : List α} {i j : Nat} (h : i ≠ j) {a : α}  :
    (l.set i a)[j]? = l[j]? := by
  by_cases hj : j < (l.set i a).length
  · rw [getElem?_eq_getElem hj, getElem?_eq_getElem (by simp_all)]
    simp_all
