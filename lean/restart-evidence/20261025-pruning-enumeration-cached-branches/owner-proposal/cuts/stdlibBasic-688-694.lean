@[simp, grind =] theorem flatMap_nil {f : α → List β} : List.flatMap f [] = [] := by simp [List.flatMap]
@[simp, grind =] theorem flatMap_cons {x : α} {xs : List α} {f : α → List β} :
  List.flatMap f (x :: xs) = f x ++ List.flatMap f xs := by simp [List.flatMap]

@[simp, grind _=_] theorem flatMap_append {xs ys : List α} {f : α → List β} :
    (xs ++ ys).flatMap f = xs.flatMap f ++ ys.flatMap f := by
  induction xs; {rfl}; simp_all [flatMap_cons, append_assoc]
