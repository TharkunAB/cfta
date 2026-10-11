# Observed atomic weights

The repaired `Compile.groupBuilt` retains `staticSampling`'s per-rank weight
for atomic sources as well as other finite sources. The original code omitted
this field for atomic sources. That omission was safe only while the rebuilt
singleton remained atomic. Pairing makes the result non-atomic. The later
merge then used member counts and changed a 9:1 choice to 1:1 when bounded.

The source change removes the atomic-source exception. The existing product
and merge paths already propagate explicit size masses. Public `groupOn`
continues to use its documented size-one policy. Ordinary finite branch
weights continue to become counts inside recursion. Atomic internal weights
remain relative member weights, with their sum equal to the class count.

`MassRetention.observed_fields` proves that reconstruction changes none of
the member's original probability, size, count, or atomic marker.
`nonatomic_unchanged` proves the non-atomic metadata branch is unchanged.
`recursive_atomic_policy` proves the retained atomic weight equals the
existing recursive atomic fallback: source count times member probability.

The distribution proof uses arbitrary positive member weights and arbitrary
valid sibling groups. `expand` interprets a group's retained mass and its
count-scaled internal weights as one complete weighted member stream.
`expand_pair` derives exact independent-product semantics from the product
fields. `expand_observe` and `expand_observedPairs` prove that reconstruction
retains every weighted member in replay order. `sampler_expansion` connects
the actual group-choice formula to normalization of this stream.
`atomic_observed_pair_distribution` proves that the repaired observation,
product, and merge path has the original conditional distribution. The
source's common count factor cancels during normalization. This theorem is
general; `repaired_atomic_pair` also checks the former 9:1 counterexample.

The existing `CompileSpec` atomic-choice regression now checks bounded PMF,
exact backend lowering, and repeated recursive use at sizes three and six.
All nine weighting examples pass in the project Nix environment.
`CurrentFindings.atomicPair` now fails if observation changes the probability
or size. `fourmolu` and `cabal-gild --mode=check` pass for the touched files.

`RecipeCompile.atomic_pair_metadata_counterexample` remains a theorem about
the old metadata branch. It does not describe the repaired source.
The new theorem covers this observation/product/merge path; it does not
establish every source record or the complete refinement compiler invariant.
