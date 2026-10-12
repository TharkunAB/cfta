# Probability proof scope

`MicroCFTA/Probability.lean` has 63 kernel-checked theorems. It imports only
`Std`. It has no omitted proof or custom axiom. The concrete examples use
`decide +kernel`.

The model uses finite lists of runs with rational masses. A run can have the
same output value as another run. An event probability sums all matching run
masses. This matches the distinction between stable replay ranks and values in
the generator API.

After the initial fixes, [Sized.lean](MicroCFTA/Sized.lean) extends these laws
to explicit size annotations and a concrete key partition.
[Decoder.lean](MicroCFTA/Decoder.lean) proves exact rank-order preservation
under plan normalization. `SizeMass.lean` proves the count-scaled per-size
weight formulas and concrete split/merge laws. `Sparse.lean` proves finite
mass convolution. `MassRetention` proves the repaired observed atomic-pair
policy. [SYSTEM.md](SYSTEM.md) contains current findings;
[SECOND-REPAIRS.md](SECOND-REPAIRS.md) retains the historical defect report.

| Haskell code | Lean results | Scope |
| --- | --- | --- |
| `microcfta/src/Data/CFTA/Index.hs`, `pairRank`, `splitRank`, offsets | `split_pair`, `pair_split`, `pairRank_lt`, `split_lt`, `pairRank_injective`, `offset_interval` | Mixed-radix encoding is a bijection on valid product ranks. Offsets preserve branch bounds. |
| `Ranked/Internal.hs`, `fromWeighted`, `frequency`; `Ranked/QuickCheck.hs`, ticket intervals | `tickets_length`, `tickets_event_count`, `selectTicket_eq_getElem?`, `selectTicket_exists`, `uniform_tickets_probability` | Ordered intervals have exactly their declared ticket counts. The proof covers a linear decoder, not the Haskell binary search. |
| `Ranked/Internal/Sampler.hs`, `Exact`, `uniformSampler`, `productSampler` | `uniform_event_probability`, `eventMass_map`, `eventMass_product`, `uniform_probability`, `product_probability` | Uniform occurrence sampling, duplicate outputs, independent products, nonnegative mass, and normalization. |
| `Ranked/Internal/Sampler.hs`, `Exact.frequencyGen` | `eventMass_frequency`, `frequency_probability` | Each branch contributes its external weight times its conditional event probability. Positive total weight and probability distributions for the branches suffice. |
| `Ranked/Internal/Sampler.hs`, `Exact.filterGen` | `eventMass_condition`, `condition_probability` | Accepted event mass is divided by total accepted mass. The probability theorem requires positive acceptance mass. |
| `Gen/Internal/Bucket.hs`, bucket normalization and merging | `restore_normalized`, `regrouping_preserves_distribution` | Conditional buckets selected in proportion to their retained mass recover the original distribution. Every bucket must have nonzero mass. |
| `Gen/Internal/Join.hs`, `joinGroupMass`, `joinSampler` | `join_group_pair_probability`, `eventMass_product`, `regrouping_preserves_distribution` | Selecting a matched group by product mass, then sampling its two conditional sides, gives the original pair mass divided by accepted mass. |
| `Ranked/Internal/Sampler.hs`, count-weighted size choices and splits | `count_weighted_uniform_rank`, `count_weighted_uniform_product` | Count weights yield uniform ranks when the distributions inside the selected parts are uniform. Atomic nonuniform weights remain nonuniform. |
| `Ranked/Internal/Sampler.hs`, `integerMasses`, weight regrouping | `normalize_scale`, `normalized_perm_event` | A common nonzero scale and a permutation preserve all event probabilities. The concrete gcd/lcm calculation is not verified. |
| `Ranked/Internal/Sampler.hs`, `compileWeighted` | `compiled_block_decode`, `compiled_block_range` | Division by positive ticket width selects the correct payload inside one equal-weight block. |

The `Index.hs` path is relative to the repository root. The other source
paths are relative to
`microcfta-generator/src/Data/CFTA/`.

## Checked distinctions

- Uniform ranks need not give uniform output values. The checked example
  `[true, true, false]` gives `true` mass `2/3`.
- Equal branch weights need not give uniform ranks. Equal choice between
  `[0]` and `[1, 2]` gives masses `1/2`, `1/4`, and `1/4`.
- A size bound depends on the retained size measure. With two equiprobable
  atomic alternatives of size one, the second alternative has mass `1/2`
  under bound one. If reconstruction changes its size to two, its mass under
  that bound is zero. `atomic_size_bound_preserves_distribution` and
  `reconstructed_size_bound_changes_distribution` prove this numerical
  consequence of changing the size measure. The top-level atomic reproduction
  is repaired at `ae6b97b`. `8fa39f0` repairs the non-atomic built-source and
  nested atomic size cases. All those exact reproductions now pass.

## Remaining proof obligations

This is a mathematical model of the selected design operations. It is not a
verified translation of the Haskell implementation. It does not prove:

- QuickCheck's pseudorandom distribution, independence, or termination of
  rejection sampling.
- The two binary searches, array bounds, machine `Int` conversions, or the
  concrete gcd/lcm weight conversion.
- Validity, positivity, or coverage of caller-supplied `WeightedIndexed`
  callbacks. The Haskell API states these as caller obligations.
- Construction of all Haskell size classes, recursive counts, observation
  groups, or accepted join groups. The new modules prove finite sparse
  arithmetic and a concrete first-key partition, with the listed invariants.
- That arbitrary Haskell `GenBackend` instances obey probability laws.
- The `Map.fromListWith (+)` implementation used for output aggregation.

The algebraic `condition` function uses rational normalization. Its probability
claim applies to nonnegative masses and positive acceptance mass. Haskell's
`Exact.filterGen` returns an empty list when acceptance mass is nonpositive.
The Lean model does not identify that empty list with a list of zero-mass runs.

The per-size arithmetic is correct when the retained group masses satisfy its
invariants. The current atomic-pair reproduction violates that requirement:
an observation preserves the unbounded 9:1 distribution but changes bounded
sampling to 1:1. The verified identities do not establish construction of
those group masses in every Haskell path.
