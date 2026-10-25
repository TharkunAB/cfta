@[local simp] theorem getElem?_eq_none_iff : l[i]? = none ↔ length l ≤ i :=
  match l with
  | [] => by simp; rfl
  | _ :: l => by
    cases i with
    | zero => simp
    | succ i =>
      simp only [length_cons, Nat.add_le_add_iff_right]
      exact getElem?_eq_none_iff (l := l) (i := i)

theorem none_eq_getElem?_iff {l : List α} {i : Nat} : none = l[i]? ↔ length l ≤ i := by
  simp [eq_comm (a := none)]

theorem getElem?_eq_none (h : length l ≤ i) : l[i]? = none := getElem?_eq_none_iff.mpr h
