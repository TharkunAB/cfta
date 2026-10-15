-- Candidate examples for a Lean solver behind cfta's Entailment.
example (x : Int) : (x * x - x) % 2 = 0 := by grind
example (x : Int) : (x * x) % 4 = 0 ∨ (x * x) % 4 = 1 := by grind
example (x : Int) : (x * x * x - x) % 6 = 0 := by grind
example (x y : Int) (h : x > 0 ∧ y > 0) : x * y ≥ x := by grind
example (xs ys : List Int) : (xs ++ ys).length = xs.length + ys.length := by simp
example (xs ys : List Int) : (xs ++ ys).length = xs.length + ys.length := by grind
