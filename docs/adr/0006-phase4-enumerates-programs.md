# 6. Phase 4 enumerates programs and types them hole by hole

## Context

Phase 4 of Specftacular enumerated each skeleton of a bucket with its type
annotations, from the skeleton automaton. `generalizeCarriers` then typed
the program again and ignored the annotations. Most of the work was the
expansion of the annotations: 60.9 million choices at HugeLists 6-p4 with
`--type-depth 2`, size 6. With the defaults, 6-p4 did not complete in 900
seconds on one core, nor in a 14 GiB heap.

## Decision

Phase 4 enumerates only the programs of the skeleton automaton
(`prunedPrograms`, with `termsPruneUntil` of cfta). A branch stops when
only holes at type positions remain and no template check waits for one of
them. A typing of the partial program (`PartialTyping`) replaces the
annotations:

- each new fragment extends it by unification, with each generated
  variable at the type of its name, as in the automaton, and within the
  `--type-depth` bound;
- before each choice, a hole keeps only the constants that can have its
  type and the edges whose annotation node can hold it;
- after each typing, each open hole must keep an edge.

The compiled template pruning stays, and `generalizeCarriers` still types
each program again.

## Why

- A typing only becomes more specific, so these checks remove only branches
  without a typed program. The output is byte identical to #67 at
  HugeLists 5-p4 (defaults and `--type-depth 2`), at 6-p4 with
  `--type-depth 2`, with `--parallel` and `--enumerate-ahead`, and on
  Lists, ListMonad, Octonions and Regex 7-p4 and HugeLists 4-p4.
- 6-p4 with `--type-depth 2`, one core, alternate runs: allocation −37.5 %,
  MUT −37 % (with ADR 5). 6-p4 with the defaults completes: 577 seconds on
  one core, 595 seconds with `--enumerate-ahead`. 7-p4 with
  `--enumerate-ahead` takes 14,081 seconds against 24,715.

## Consequences

- The automaton still gives the shapes of the programs, and its type nodes
  still narrow a hole, but the typing decides which programs reach the
  tests.
- A template check that needs an annotation expands it, so the pruning is
  the pruning of #67.
- 7-p4 with `--enumerate-ahead` has a larger maximum residency: 19.5 GB
  against 7.3 GB. The cause is not known yet.

## Discussion points

- Fresh carriers for the generated variables in the typing: every carrier
  renaming of the variables was a new program (1.11 million programs at
  6-p4 size 6, against 39 thousand).
- A stop at a hole that a template check waits for: the type-dependent
  prunes went, with 267 more programs at 5-p4, other representatives, and
  2.6 times the test time at 6-p4.
- All templates in the oracle instead of their compilation into the
  automaton: exact, but 49 % more allocation. The compilation stays, and
  ADR 5 makes it cheaper.
- The type lookahead of the old phase 4 (skip an edge whose constrained
  child cannot fit) removed 99 % of its failures. Here it gives nothing, so
  it is not in.
- Feat-style tests before the QuickCheck cases, to separate candidates
  sooner: at 6-p4, the separation of distinct terms takes about 8 seconds.
  The test time goes to equalities, which need all 1064 cases, and to
  comparisons that reach the 1 GiB budget.
