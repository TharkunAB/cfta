# Projection numeric control

Reviewed at 2026-10-17 10:08 CEST.

The frozen source is `SourceCurrentProjectionNumericControl.lean`.
Its SHA-256 is `6683ba7b88f971c199d6455598ade439e23bb1547b55295e72878df716bbe725`.
The final growth dependency is `SourceCurrentProjectionUnionResources.lean` at SHA-256 `54824c9fa36fde497d83fe1cf02414de350279663fb54bbf879f2a4a052e7007`.

The formulas retain the original row count separately from the current scalar:

- `rowsStep child q = q + 1 + child q`.
- `rowsBound child count q = HeightOrderControlled.iterate (rowsStep child) count q`.
- `ordinary child q = unionGrowth q (rowsBound child q q)`.
- `bound 0 q = q + 1`.
- `bound (depth + 1) q = ordinary (bound depth) (headGrowth q)`.

The iterator is the existing public definition.
The module reuses the public iteration laws from MergeNumericControl.
It does not define a second iterator.
Each row step pays its current scalar, the child at that scalar, and one unit.
`rowsBound_paid` proves `q + count ≤ rowsBound child count q`.
It is an upper schedule for original rows even when a missing index skips a child call.
It does not assert that a skipped row allocates.

`rowsBound_compare` accepts separate count and seed inequalities.
It also accepts pointwise child inequalities and monotonicity only of the larger child.
`rowsBound_first`, `rowsBound_succ`, and `rowsBound_add` retain the exact order and intermediate scalar.
`ordinary_compare` widens the row count and current scalar together, then uses union growth monotonicity.
`bound_mono` follows structural path depth and uses the already proved child monotonicity.
`bound_ge` proves initial scalar retention.
It does not claim one additional unit at every positive depth.

`ordinary_le_bound` lets a direct ordinary branch use the same envelope as a possible recursive Head.
`head_ordinary_eq` preserves the exact scalar at the Head return.
The two row-to-bound lemmas cover rows before and after Head.
The first-child lowering lemmas require a positive scalar because they use a nonempty row schedule.
This condition is arithmetic; it is not a result-profile premise.

The actual projection proof must establish the input row-count bound from its resident payload mass.
After a recursive Head, that proof must establish an ordinary or empty exposed result.
It can then use the ordinary branch at the same path without another unbounded Head step.
This module does not assume any of those future facts.
It proves arithmetic implications for all natural scalar and depth values.
It does not restrict original values to finite ordinary syntax.
The selected-path domain and treatment of unrelated open siblings belong to the actual projection producer.

The public checks contain 32 complete signature and axiom pairs.
The three arithmetic integration checks evaluate row scalars 2, 6, 14, and 30.
They also compare a shorter row prefix followed by union with the complete direct ordinary envelope.
The last check performs that comparison after the Head scalar and retains the same complete path bound.
These checks construct arithmetic schedules.
They do not construct an actual projection graph or claim a whole Operand completion.
No Haskell source changed and no new Haskell defect was found.
