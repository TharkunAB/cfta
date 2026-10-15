import Oracle.Tactic

/-!
Tests of `hectare?` on goals with classes and higher kinds. Run them with
`lake env lean OracleTest/Tactic.lean` after `lake build`, with the variable
`HECTARE_PROPOSER` naming `hectare-propose`, so that the portfolio's mode (a)
runs.
-/

/--
info: Try this:
  [apply] exact List.count x xs
-/
#guard_msgs in
example {α : Type} [BEq α] (x : α) (xs : List α) : Nat := by
  hectare? (suggestions := 1)

/--
info: Try this:
  [apply] exact (List.lookup k xs).getD d
-/
#guard_msgs in
set_option maxHeartbeats 0 in
example {α β : Type} [BEq α] (k : α) (d : β) (xs : List (α × β)) : β := by
  hectare? (suggestions := 1) (seconds := 30)

/--
info: Try this:
  [apply] exact xs.sum
-/
#guard_msgs in
example {α : Type} [Add α] [Zero α] (xs : List α) : α := by
  hectare? (suggestions := 1)

/--
info: Try these:
  [apply] exact max x y
  [apply] exact max y x
-/
#guard_msgs in
example {α : Type} [Max α] (x y : α) : α := by
  hectare? (suggestions := 2)

/--
info: Try these:
  [apply] exact Add.add x y
  [apply] exact Add.add y x
-/
#guard_msgs in
example {α : Type} [Add α] (x y : α) : α := by
  hectare? (suggestions := 2)

/--
info: Try these:
  [apply] exact Option.map f o
  [apply] exact #[Option.map f o].back!
  [apply] exact (Array.singleton (Option.map f o)).back!
-/
#guard_msgs in
example {α β : Type} (f : α → β) (o : Option α) : Option β := by
  hectare?

/-! The search over states alone (`budget := 0`) finds `Functor.map`, which
has no erased type, where mode (a) lists programs over `Array`. -/

/--
info: Try these:
  [apply] exact Option.map f o
  [apply] exact f <$> o
  [apply] exact (Option.map f o).getM
-/
#guard_msgs in
example {α β : Type} (f : α → β) (o : Option α) : Option β := by
  hectare? (budget := 0)

/--
info: Try this:
  [apply] exact x >>= f
-/
#guard_msgs in
example {m : Type → Type} [Monad m] {α β : Type} (x : m α) (f : α → m β) : m β := by
  hectare? (suggestions := 1)

/-! Without `useAll`, the smallest programs need not use the locals. -/

/--
info: Try these:
  [apply] exact Char.numCodePoints
  [apply] exact Char.numSurrogates
-/
#guard_msgs in
set_option linter.unusedVariables false in
example (xs : List Nat) : Nat := by
  hectare? (useAll := false) (suggestions := 2)

/-- error: hectare? found no program of at most 2 leaves -/
#guard_msgs in
example {α : Type} (x : α) : List (Option Bool) := by
  hectare? (size := 2)
