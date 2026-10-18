# Actual untouched continuation progress

Reviewed and frozen at 2026-10-18 22:55 CEST.

The source is `lean/MicroCFTA/SourceCurrentOuterUntouchedProgress.lean`.
Its SHA256 is `68e838a0608824e2cb11aba12e2b02b00fc13b57748f08c7ecc63483e6305e06`.
The module exports three theorems: `walk_prefix`, `dispatch`, and `budget`.

## Checked claim

`walk_prefix` derives an exact `OuterExecutionAncestry.Reached` dispatch.
Its only successful outer call premise is the completed prefix of earlier
siblings. The selected child has not returned. No whole walk or enclosing
node return is a premise.

`dispatch` starts with initial `Good`, phase `Inputs`, causal plain Mu guard
heap, and positional `Origins`. An actual unfinished prefix reaches the
chosen source row. The theorem derives all four current facts at that row.
The actual Parent call can be cold or warm. Its captured full request gives
`EdgeLink` for the returned edge. An explicit untouched footprint at the
current slot and independently chosen next slot gives `Link` for the source
anchor and the actual dispatched value. A positive row of that value and a
present next child give `Below` and strict `InternedValueMass` decrease.
The conclusion retains the exact inherited descent, full caller state, and
literal reached node dispatch.

`budget` sums these strict decreases over a finite chain. Its child index
can change at every step. The `Below` steps remain explicit inputs.
It does not assert that every actual execution is such a chain.

## Source-built check

The fixture builds an ordinary parent with own class `[[0],[1]]` and children
`[leaf, leaf, B]`. The value B has own class `[[0],[1]]` and two leaf children.
Actual construction and equality allocation derive the initial physical
support, empty outer memo origins, resident inputs, and causal guard heap.
The fixture executes the cold Parent call. It executes exactly the first
two sibling calls. The selected dispatch uses slot 2 and its retained
continuation uses slot 0. It applies `dispatch` to derive the exact reached
node, `Link 0`, `Below 0`, and strict anchor decrease. The fixture defines no
successful whole walk or node call. The public theorem forwards a private
checked proof with the identical complete statement.

## Relation to general termination

The old `OuterParentHeightGrowth.supported_parent_growth` already refutes
strict ordinary-height descent. The old `OuterOriginalRepeat` already shows
that the same physical node can recur while its first owner is active, with
a different inherited key. Neither witness is new here.

`OuterInheritedDescent` lowers nonempty inherited height only between local
combinations. `OuterInheritedGain.collision` derives an intervening gain for
a key return to a nonempty owner. `OuterOriginDependencies` preserves input
class coverage and strict-prefix dependencies through one combine/descent.
These facts do not bound new local combinations or generated requests.
`InheritedGainDomain` gives a finite domain for one combination, not a
uniform domain for an arbitrary sequence.

The new result supplies an actual dispatch producer for one decreasing
relation. A global proof still has to control selected continuation edits
and intervals that do not meet the positive-row hypotheses. A ghost anchor
rank alone does not exclude a repeated physical memo key. Such an exclusion
must use the exact captured owner and full key equality. Fresh-key request
bounds and repeated-pass convergence remain separate obligations.

The Haskell worker calls Parent before it recurses into returned children:
`cfta/src/Data/CFTA/Equality/Operations.hs:80-96`, `:143-168`.
Its source comment records the unequal-length copying gap at `:129-142`.
The modeled physical keys are the canonical inherited identity paired with
the tagged node reference or complete edge identity:
`SourceCurrentAllocatedPartialState.lean:27-49`.
No new infinite execution, runtime defect, or Haskell correspondence claim
is made.

## Selected checks and retained attempts

Production strict: `untouched-progress-direct-3`, terminal 0, zero-byte log.
Canonical: `untouched-progress-canonical-1`, terminal 0, 1850 jobs.
It replays only the existing `InternedFreshOrdinaryClosedCompletion:24:5`
unused-input warning. The new module has no warning. No old file is changed.
Public: `untouched-progress-public-1`, three full proof/axiom pairs.
Constructed strict: `untouched-progress-kernels-direct-5`, terminal 0,
zero-byte log. Constructed public: `untouched-progress-kernels-public-1`,
one full proof/axiom pair. All probes use all eight printer/linter settings
and permit only `propext`, `Classical.choice`, and `Quot.sound`.
Every Lean job records effective 4 GiB maximum/high limits and zero swap.

Production attempts 1 and 2 retain parser, section-scope, and argument
alignment diagnostics. Fixture attempt 1 retains an unresolved phase
inference diagnostic. Attempts 2 through 4 retain only source coverage and
finite footprint proof diagnostics. All attempts are preserved. None is
selected as a successful theorem check. No attempt was interrupted.

This component owns 3 public pairs and 1 constructed pair. It owns no
auxiliary pair. Root performs Audit and checkpoint integration separately.
