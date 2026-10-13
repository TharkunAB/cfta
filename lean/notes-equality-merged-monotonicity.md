# Saturated target merge is not monotone

Checkpoint: 2026-10-13 17:24 Europe/Stockholm.

## Counterexample

Use unconstrained finite ordinary trees. Let `a`, `b`, and `c` be distinct
nullary symbols. Let `ab` accept exactly `a` or `b`.

```text
expanded = p(a,a) | p(a,b) | p(b,a) | p(b,b) | p(c,c)
compact  = p(ab,ab) | p(c,c)
```

The actual source structural comparator accepts `compact` as a cover of
`expanded`. The two inputs also have the same finite accepted language;
the native source enumeration check confirms this equality.

The source merges the five `expanded` rows into one row. Both child
columns become the union `{a,b,c}`. Its result accepts nine pairs. The
source retains the two `compact` rows. Its result accepts five pairs.
The term `p(a,c)` belongs to the first result and not the second.

Both results already have exact merge replay. They retain the same full
value and runtime cache in the next call at every comparison-fuel bound.
Thus repeated merging to the height bound does not fix monotonicity.

## Formal result

`EqualityMergedTargetMonotonicity.lean` builds both inputs with actual
nested source constructor requests. It derives source Facts, Prepared,
and input availability. No fabricated record cache is used.

- `source_cover` checks the actual ordered structural comparator.
- `expanded_done` and `compact_done` prove actual merge completion.
- `fixed_execution` and `all_fuels` prove exact fixed-point replay.
- `output_cover_fails` proves that source structural coverage fails after
  both merges.
- `ordinary_language` connects constructor acceptance to the actual-cache
  epsilon semantics for finite ordinary trees.
- `output_separation` proves the accepted and rejected witness in each
  actual returned cache.
- `saturation_not_monotone` proves input language inclusion and failure
  of output language inclusion. The Lean theorem needs only inclusion;
  it does not use the native input-language equality check as a premise.

This rules out a monotone closure argument under language inclusion or
source childwise row coverage. The source threshold depends on the row
representation. A structural order designed for another termination
argument must account for that threshold and its correlation loss.

This is not a cycle of a fixed equality schedule. It does not refute
termination. It also does not prove that arbitrary interleaved intersection
and one-pass target merging makes progress. A finite generated ordinary
carrier alone would only imply eventual repetition; a separate argument
must exclude nontrivial cycles.

## Checks

Pinned Lean build passed all 380 dependency jobs:

```sh
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.EqualityMergedTargetMonotonicity
```

The focused audit also includes the two actual Work-result helpers in
`EqualityNestedUnaryWorkFacts.lean`. All 21 declarations passed. Only
`propext`, `Classical.choice`, and `Quot.sound` occur. There are no admitted
obligations, custom axioms, or native decisions. The audit input and log are:

```text
/tmp/mcfta-merge-monotonicity-axioms-20261013.lean
/tmp/mcfta-merge-monotonicity-axioms-20261013.log
```

The native source fixture is local-only at
`/tmp/mcfta-merge-monotonicity.hs`. It ran in the repository Nix environment.
The log is `/tmp/mcfta-merge-monotonicity.log`:

```text
("merge-monotonicity",True,True,True,5,9,5)
```

The Booleans check input language equality, exact merge fixed points, and
the separating witness. The counts are the original language size and
the two merged language sizes. No new production test was added.
