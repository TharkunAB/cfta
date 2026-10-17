# Numeric Merge control

Reviewed at 2026-10-17 09:49 CEST.

The source SHA-256 is `f40da3d9a17e91e4e21bcd6d50033952e3de844a2338df95348602ae2b0a4ba5`.
The module defines exactly these numeric functions:

- `width q = (q + 1)^2`.
- `step w child q = q + 1 + max (primitiveGrowth w q) (max (selectionGrowth q) (child q))`.
- `bound 0 q = q + 2`.
- `bound (h + 1) q = iterate (step (width q) (bound h)) (bodyBudget q) q + 1`.

`iterate` is the existing `HeightOrderControlled.iterate`.
The module does not define a second iterator.
The public iteration laws cover inflation, seed monotonicity, count monotonicity, block addition, and the final step.
`iterate_compare` compares pointwise ordered functions at ordered seeds.
It requires monotonicity only of the upper function.
It does not require inflation or monotonicity of the lower function.
`iterate_count_mono` requires inflation but does not require monotonicity.
These premises match the exact arithmetic proofs.

`width_mono` and `bodyBudget_mono` retain their original input order.
The corresponding lower bounds are `q + 1 ≤ width q` and `q + 1 ≤ bodyBudget q`.
Each step pays at least `q + 1`.
It separately covers primitive growth, selection growth, and the child bound.
`step_pays_child` also pays `q + child q + 1`.
`step_compare` retains larger width and pointwise larger children.
`step_mono` uses a monotone child together with the existing monotonicity of both local growth functions.

`bound_ge` proves `q + 2 ≤ bound h q` for every height.
At a positive height it uses the positive direct instruction budget and the first paid step.
`bound_mono` compares the two width parameters, then the two seeds, then the two direct instruction counts.
It uses the same smaller-height function on both sides.
No body execution or future successful call is a premise.

The imported public checks contain 22 complete signature and axiom pairs.
The three integration checks evaluate small envelopes and an ordered bind schedule.
The bind schedule applies three steps, then two steps, then one bind step.
Its successive scalars are 23, 95, and 191 from initial scalar 2.
The third check proves that a shorter schedule remains covered after the initial scalar increases.
It combines child monotonicity, pointwise step comparison, count monotonicity, and the final height envelope.
It also proves that every literal step pays one count unit.

This module supplies arithmetic for a separate actual execution producer.
It does not construct a Merge graph or an initial full-query receipt.
It does not assert that arbitrary instruction lists satisfy the required width or child hypotheses.
The actual resource certificate and height induction must establish those facts at the same reached heaps.
All formulas use natural numbers.
Finite machine-word admission is a separate use of the resulting bounds.
No Haskell source changed and no new Haskell defect was found.
