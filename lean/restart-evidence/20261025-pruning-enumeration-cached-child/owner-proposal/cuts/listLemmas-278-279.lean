theorem getElem?_singleton {a : α} {i : Nat} : [a][i]? = if i = 0 then some a else none := by
  simp [getElem?_cons]
