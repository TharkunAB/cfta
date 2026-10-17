# Stored reconstruction and union normalization

Checked at proof commit `ca91ab34`. Starting checkpoint is `5f6d6f3b`.
Source main remains `c0cc8a05`, merged into formalize at `896b0a1c`.
The whole-library objective remains active. No Haskell behavior changes.

## Completed theorem

`SourceCurrentStoredUnionFusion.initial` requires only initial `Ready`,
available original values, and available environment replacements. It
constructs these actual operations in sequence:

1. Normalize the original members with `makeUnion`.
2. Execute stored substitution on that normalized value.
3. Execute stored substitution on each original member, in order.
4. Normalize those member results with `makeUnion`.

The theorem retains every intermediate heap and all four `Keeps` facts.
Both returned values remain available at the final heap. The two values
have `Same depth view` for every finite depth and every fixed view heap.
It assumes no future completed call, returned-result law, or child relation.
The two operation orders run in sequence in one growing cache. This is
not a comparison of physical values from independent cold executions.

`Same` retains exposed bare references at depth zero. Each additional
depth retains full row symbols, full guards, and ordered child relations.
Row order and duplicate occurrences can differ. Each comparison uses one
fixed view. The theorem does not transport observations between view heaps.

The endpoint permits closed and open roots, references, stored unions,
and arbitrary nested Mu values. The ordinary-only premise occurs inside
the ordinary merge case. It does not restrict the initial endpoint.

## Proof components

- `SourceCurrentStoredCallsReplay` derives validity and growth from actual
  ordered child calls. Each call replays its exact result at a common later
  heap. Two completed sequences of the same originals have equal results.
- `SourceCurrentStoredUnionObservations` constructs an actual stored union
  call and all its original member calls. Their results have the same
  observations. The closed branch retains the literal stored union.
- `SourceCurrentOpenObservationLists` composes observations under append
  and equal root membership. It requires no heap invariant.
- `SourceCurrentStoredCallSelection` derives selected warm calls from
  actual source calls. Coherence justifies complete-value retention under
  `distinctNodes`. Output membership is derived from deterministic calls.
- `SourceCurrentStoredNodeExpansion` exposes every original row before
  filtering. Each row retains ordered stored child calls and its exact
  edge request. Closed nodes retain their original rows. Open nodes expose
  all rebuilt rows. Exactly the surviving rows become row origins.
- `SourceCurrentStoredUnionFlattening` derives warm calls for the literal
  flattened members. It preserves observations of all original returns.
- `SourceCurrentStoredOrdinaryUnionObservations` aligns ordinary source
  rows with normalized rows. The same original child calls produce equal
  ordered child results. This proves the same survival test and exact row
  origins. Children may contain arbitrary Mu values.
- `SourceCurrentStoredUnionWarm` handles the actual selected list. Its
  empty, singleton, ordinary merge, and retained union cases use the exact
  `makeUnion` branch. It needs no flattening fixed-point premise.
- `SourceCurrentStoredUnionFusion` composes the warm result and constructs
  both complete schedules from initial inputs.

## Limits and counterexamples

Physical result equality remains false. The selected integration constructs
`union[A, B, z]` and `union[AB, z]` through actual source operations. The
new initial theorem proves equal observations at every depth and view for
these physically unequal results. All four actual cache histories and both
final availability facts are retained.

Equal observations at every depth do not imply physical empty agreement.
A checked closed unused raw Mu has the same observations as Empty while
remaining physically nonempty. A separate open raw Mu reconstructs to
Empty when its free capture becomes Empty. Do not infer row survival from
`Same` alone. The ordinary merge proof instead identifies exact child results.

`Ready` does not imply canonical row order for every resident ordinary
node. Closed substitution returns the literal stored node. The node
expansion proof uses exact origins and does not rebuild a closed parent
under an assumed canonical key.

The general retained-Mu writer relation remains open. This theorem handles
prior union normalization. It does not yet connect the actual selected Mu
body and ordinary probe through all recursive reconstruction, raw unused
Mu cleanup, and earlier warm winners. That connection must retain full
guards, ordered children, survival facts, bare references, and actual
issued-reference histories. Four-table growth does not supply the latter.

General outer progress, full mutual completion, repeated-pass convergence,
current frontend/runtime adapters, and complete public Haskell correspondence
also remain open. Read `notes-proof-status-20261017.md` for the full target.

## Validation and preservation

The full pinned Audit passes 3114 jobs and 68344 dependency checks. Its
effective MemoryMax and MemoryHigh are 4 GiB; swap is zero. Peak memory is
379 MiB. The Audit retains one existing unused-variable warning in
`InternedFreshOrdinaryClosedCompletion`; that old source is unchanged.
All nine new strict source logs are empty. All nine canonical builds pass.
Nineteen public and thirteen constructed checks pass across nineteen groups.
Selected axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`. Every public declaration has its full signature and proof printed.

Evidence is in `restart-evidence/20261017-mu-observation-fusion/`.
The directory retains failed attempts. The first flattening fixture process
ended with code -15 and no Lean output. Its cause was not established.
The later selected fixture uses symbolic length correspondence and passes.
An intermediate fixture had an incorrect namespace for `empty_available`.
Neither failed attempt is selected as validation.

Earlier proof sources, counterexamples, repairs, marked drafts, optimized
code, stashes, and other worktrees remain preserved. No Haskell source
changes. Its strict Nix build, 798 examples plus golden, Fourmolu, and
Cabal-gild validation remain the earlier source evidence.

Root `FINDINGS.md` keeps the external repair registry first. Field-pool
repair `b9219b9e` remains merged and validated. Record each later Haskell
repair there with its failure, reproducer, paths, commit, checks, and status.
