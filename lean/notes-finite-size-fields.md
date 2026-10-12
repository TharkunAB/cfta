# Finite compiler size fields

Six modules connect finite compiler constructors to size positions, class
weights, retained mass tables, and class samplers. They build the fields.
They do not assume that an entire compiled record is coherent.

## Source distinction

The source has three different mass scales:

- The global outcome mass describes the declared finite distribution.
- A member's relative weight inside a size class has the count scale. The
  weights of that class sum to its member count.
- A retained `MassIndex` describes the unnormalized mass of an observed
  group in that class. An absent table means the structural class count.

Ordinary `frequencyStatic` chooses alternatives within a size class by
member count. It retains each child's internal relative weights.
`frequencyStaticWithMasses` instead uses the retained class masses to choose
alternatives. `pairStaticWithMasses` uses products of retained masses to
choose size splits. These operations do not replace the global distribution.

The current source has no helper named `preservedMassIndex`. Its retention
path is `Compile.keyedMember`, `sourceWeight`, the optional mass table in
`pairBucket`, and `closedMasses`.

## Constructed fields

`FiniteSizeFields.Record` contains the actual finite plan structure, class
member weights indexed by original rank, and optional retained class masses.
Its `Valid` property relates these fields to the independent class rank lists
from `SourcePlanPositions` and `SourcePlanPartition`.

The module derives `Valid` for ordinary uniform sources, fixed-size rows,
maps, pay, atomic sources, rebuilt observed members, products, and choices.
Pure and placeholder sources have size zero. `fixedPlan_classes` and
`fixedPlan_count` cover the source's singleton `PlanSized` rows.
`observe_member_valid` derives the original size position and positive weight
that `Compile.keyedMember` stores for one rebuilt member.

The source pair plan is not represented only by a binary-product assumption.
`pairPlan` contains the resized size-zero operation and the two `PlanShared`
arguments from `chainPlan`. `zero_left_classes`, `pairPlan_classes`, and
`pairPlan_count` derive its binary product rank and size order.

## Source callbacks and samplers

`FiniteSizeSampling.weightAt` reads the original rank's source position and
its corresponding class weight. `weightAt_exists` proves that its successful
interval is exactly the plan count. `class_lookup` and `weightAt_member`
connect this callback to the original rank stored by the class partition.

`pair_weightAt` derives the full source `pairStaticWithMasses.weightAt`
formula from child rank positions and child callbacks. `choice_weightAt`
does the same for `frequencyStaticWithMasses`, with the actual cumulative
global-rank offset. The formulas use the derived class counts and retained
mass totals. They do not receive a desired result probability as a premise.

`pair_without_retained` and `choice_without_retained` prove that the common
class construction reduces to the source's ordinary branch when both mass
tables are absent. In that branch a pair multiplies child relative weights,
and a choice keeps child relative weights unchanged.

`sample_probability`, `sample_ranks`, and `sample_support` prove normalization,
unique original ranks, and exact rank support for every live class.
`pair_sampler` and `choice_sampler` connect the resulting distributions to
the existing executable `Sampler.chooseMassWeighted` model. This includes
positive-mass filtering, rational-to-integer conversion, and the singleton
backend shortcut.

## Stored mass tables

`FiniteSizeSeries` constructs the ascending finite class table with empty
classes omitted. Its coefficient and early-stop lookup proofs derive the
class mass that the sampler reads.

`Matches` is a local relation between one stored mass table and its record.
The source operations preserve it:

- `observed_matches` initializes the one-member retained table.
- `fixed_matches` covers pure, holes, and resized indexed point sources.
- `countTable_matches` derives `bucketMassIndex`'s count fallback.
- `pay_matches` shifts existing rows with the class fields.
- `pair_matches` proves the actual `mulSparse` product against the product
  class sampler. Its split sum includes size zero.
- `choice_matches` proves the actual right fold of `addSparse`.

The last two results operate on the stored input tables. They do not require
the caller to rebuild canonical tables. Coefficient extensionality supplies
the representation step.

## Integer closure

`IntegerSizeClosure` models `pointsStatic`'s ordinary application to a
resized indexed point source. Every point has size equal to the coordinate
width. The point rank is the less significant rank digit.

`close_weights` proves the actual ordinary application weight product. At
each result size only one size split can be live, so the normalized split
formula retains the original relative member weight for each point.
`close_count_at_size` derives the original class count times the point count.
`close_position` and `close_class_rank` give both directions of the source
class-rank conversion.

`closedMasses_matches` proves the actual stored sparse product with
`[(width, pointCount)]`. It shifts every retained class by `width` and
multiplies its mass by `pointCount`. It composes with earlier stored tables.

## Generated compiler and final observations

`OpenGroupedSize` constructs these records from the same generated,
repeated-key, and grouped application constructors as
`OpenGroupedApplication.Source`. `source_count` derives equality with the
private term decoder's count. A parent label pays once. Integer closure then
adds the coordinate width. `settled_class_decoder` uses actual successful
settlement and the earlier term-index proof to obtain complete exact-size
term decoding.

`FinalSizeFields` combines global and size records through the final
observation partition, accepted-mass normalization, and unit-key ungroup.
`result_aligned`, `result_class_decoder`, `result_class_replay`, and
`result_class_probability` derive a shared member interval, complete class
decoding, replay agreement, and normalized size-class sampling.

The all-atomic same-size branch is separate. `mergeBucketGroup` uses
`retainAtomic` in that branch, so its within-class distribution is the merged
global distribution. `atomicMerge_aligned` derives the resulting fixed-size
record from the actual merged global law. `atomicMerge_probability` proves
that law directly. `merge_positive` derives the positive output weights from
the validated child weights. This is not the count-weighted ordinary branch.

## Scope

The generated-source theorem covers the existing bare finite open recipe
fragment and its parent closure. Its closed `pointsStatic` records are
non-atomic. The regular final-merge theorem applies to that path and to
merges with retained mass tables. The separate atomic theorem covers the
source's common-size atomic branch once its constructor flags select that
branch. This module does not extract the complete flag dispatcher for every
arbitrary imported `Static` value.

The rank and class proofs are finite. They do not add a new proof of lazy
recursive mass-table productivity. The source's shared-choice threshold
changes sharing; `SourcePlanPositions` gives shared wrappers the same pure
count, class, and position behavior. Cache allocation remains separate.

## Validation

The six modules build with pinned Lean 4.34.1: 107 jobs and 144 new theorems.
There are no `sorry`, new axioms, or native decision proofs. No production
Haskell file changed, and no Cabal run was needed. The preceding 618-test
Haskell result remains the latest source validation for this work.
