# Static sampling and bucket merge dispatch

`StaticSamplingDispatch` and `BucketMergeDispatch` connect the source flag
checks to the finite size-field proofs. They cover every finite branch of
`Static.staticSampling` and `Bucket.mergeBucketGroup`.

## Static sampling

`StaticSamplingDispatch.Fields` contains the plan, global outcome masses,
atomic marker, minimum size, optional common global mass, and optional stored
class weights. The external `KeyedBucket` mass table is a separate field.
The dispatcher follows this priority:

1. An atomic marker selects the global outcome distribution at the atom's
   minimum size. It ignores any stored class sampler.
2. A non-atomic record with stored class weights uses those weights.
3. A non-atomic record without stored class weights uses member counts.

The atomic weights are the global probabilities multiplied by the total
member count. The common global mass flag suppresses the weight callback.
`common_mass_atomic_weights` derives this suppression from the local
common-mass observation and normalization. It does not assume the desired
uniform sampler equation. `missing_callback_rank` proves that each valid
rank then has relative weight one.

`sampling_valid` combines the complete dispatcher with local field laws.
The atomic branch uses normalized positive global masses, the count of the
actual plan, and constructor size provenance. The stored branch uses its
local class-weight invariant. `FiniteSizeFields` and `FiniteSizeSampling`
derive that invariant for the existing finite constructors. Removing the
external retained mass table preserves the static class-weight invariant.

`Origin` records the source atomic flag behavior. Ordinary constructors clear
the flag. `atomicStatic` sets the flag and resets size to one. Map preserves
the flag and size. Pay and label preserve the flag and increase size. Resize
preserves the flag and replaces the size. Its atomic case therefore needs a
positive requested size. The relation derives that every nonempty atom has
one positive size and the original rank order.

The source permits unrestricted internal `resizedStatic`. In particular,
resizing an atom to zero can preserve its atomic flag. This is not accepted
by the positive-atom provenance theorem. No public compiler path to that
state was established. Size-zero ordinary values and placeholders remain
valid and select the ordinary branch.

`boundedFields` records the actual flag update in `boundedStatic`.
The wrapper always clears the atomic marker. A weighted recursive source
retains its class sampler. An unweighted recursive source uses the uniform
fallback. The theorem covers this finite wrapper decision. It does not
prove lazy recursive sampler productivity.

## Bucket merging

`BucketMergeDispatch.Input` adds the atomic marker and minimum-size metadata
to the already constructed global and size records. The dispatcher covers:

- Empty input and any nonpositive outer mass return `EmptyGenerator`.
- A positive singleton returns every input field unchanged.
- A non-singleton with any retained mass table uses the retained-mass branch.
  This check takes priority over all atomic markers. The output table stores
  the sum of the original unnormalized class masses.
- Without retained tables, a nonempty list of atomic markers with the same
  finite minimum selects the atomic branch.
- Every other non-singleton uses the ordinary class-count branch.

The error model uses `Except Unit` because these source failures all return
`EmptyGenerator`. It does not treat an error as an empty successful language.
`checked_exact` proves the exact successful mass-check domain. Singleton
identity, atomic marker updates, retained table presence, and branch selection
are separate theorems.

`commonAtomicSize_exact` derives the full atom guard from its component flags
and minima. `selected_size_positive` derives a positive selected size from
constructor provenance, global normalization, and count alignment. This
prevents the negative list index in the source `size - 1` expression.
`source_atomic_fields` compares the actual atom followed by `size - 1` pays
with the fixed-size atomic record. It proves equality of the counts, ordered
class ranks, and class weights.

`merge_aligned`, `merge_global`, `class_decoder`, and `class_probability`
compose the branch constructors. Every successful branch retains the global
decoder and declared conditional law. Each live class has a normalized
sampler with distinct original ranks. Its decoder succeeds exactly on the
counted class interval. Global term uniqueness still requires the separate
term-injectivity condition; distinct ranks can describe equal user values.

## Scope

The proofs extract every finite flag branch. They do not claim that arbitrary
hand-built internal records satisfy the local input laws. A false common-mass
flag, a stored sampler that disagrees with its callback, an inaccurate count,
or an atomic resize to zero can violate those laws. Existing constructor
proofs provide the size, weight, count, and global-index laws for their stated
source fragments. The new modules combine them without a premise that the
whole merge or whole dispatched sampler is correct.

The model compares exact finite fields. It does not extract Haskell code,
prove container or runtime behavior, or prove the evaluation cost of metadata
checks. The `boundedStatic` result covers its flag and stored-sampler decision;
it uses the existing recursive field proofs for the actual class law.
No source change or additional public defect is claimed by these modules.
