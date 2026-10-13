# Weighted QuickCheck selection and safe machine arithmetic

`SourceQuickCheckFrequency` follows the actual cumulative `mapAccumL` table,
first-upper-bound binary search, and selected array occurrence. It derives
finite search and the exact ticket interval of each original alternative.
Alternative order and duplicate values remain observable occurrences.
The empty-alternative error remains separate from selection.

`SourceQuickCheckFrequencyProbability` derives each event's selected weight
divided by total weight from an external uniform ticket draw. Running the
selected generator agrees with the Exact backend's mixture. Duplicate output
keys aggregate normally. The concrete `Ranked.fromWeighted` composition
retains the original list position as its sampled replay rank.

The machine review found an unchecked midpoint sum. The former expression
`(low + high) quot 2` can overflow even when both indices fit. The source
checks total ticket weight before choosing Int or Integer tickets; that
check does not bound the sum of two array indices. The historical machine
module preserves a kernel-checked 64-bit example that reaches a negative
second midpoint. It requires a hypothetical enormous array. It is an
arithmetic counterexample, not a feasible allocated-array reproduction.

Repair `a8b32869` uses `low + (high - low) quot 2`.
`SourceQuickCheckFrequencyRepair` proves equality with the original
mathematical midpoint and exact signed subtraction, quotient, and addition.
The complete repaired search needs only a representable array length.
Positive weights and the existing small-ticket total guard derive that bound.
The wide-ticket path retains its separate array representation bound.
Actual branch probabilities and sampled rank replay remain unchanged.

`repro/WeightedMidpoint.hs` checks the arithmetic without allocating an array.
On the current 64-bit host the old midpoint is `-2305843009213693953`.
The repair and mathematical result are both `6917529027641081855`.
The 206-example generator suite, fixture, Fourmolu, and cabal-gild pass in Nix.
Log: `/tmp/mcfta-weighted-midpoint-20261014-tests.log`.

Proof checkpoint: `dd038904`. The aggregate audit passes 1,180 targets and
39,689 theorem dependency checks.
Log: `/tmp/mcfta-closing-20261014-audit.log`.
Uniform `chooseInt`/`chooseInteger` behavior, concrete array storage, and
resource availability remain external contracts. The theorem derives the
weighted backend's distribution; it does not assume that distribution.
