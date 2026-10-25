theorem flatMap_singleton (f : α → List β) (x : α) : [x].flatMap f = f x :=
  append_nil (f x)

-- The argument `l : List α` is intentionally explicit, to allow rewriting from right to left.
@[simp] theorem flatMap_singleton' (l : List α) : (l.flatMap fun x => [x]) = l := by
  induction l <;> simp [*]

