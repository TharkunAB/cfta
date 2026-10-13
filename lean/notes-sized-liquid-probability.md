# Main Sized theorem, liquid decisions, and probabilities

Updated: 2026-10-13 22:30 CEST.

## Main language contract

`SizedLanguageTheorem.grammar_correct` starts from the independent grammar
derivation. It proves exact node-count classes, finite reference evaluation,
complete distinct prefixes in size order, and both rank inverse laws.
It needs neither a finite language nor unambiguous accepting runs.
`public_correct` transfers these contracts to the public Sized source model.
The earlier direct-row dispatch proof connects the optimized and reference
query records. The old UVar enumerator retains its own depth/marker order.

`SourceSizedTableEvaluation` records finite evaluations of the optimized
count and compiled-plan recurrences. Each child query has a smaller size.
It also composes completed canonical sorting, ordinary minimum-size
preprocessing, and the product minimum-size ambiguity check.
The certificate bounds recursive query nesting, not primitive instructions
or Haskell lazy heap execution.

## Liquid logic and complete outcomes

`SourceSizedLiquidLogical` proves both positive and negative support for
complete guards. This includes ordered Boolean connectives, missing paths,
scoped substitutions, formula-level negation, and negative entailment.
`SourceSizedLiquidProgram` and `SourceSizedLiquidEvaluation` connect each
actual query occurrence to that complete evaluator. Repeated queries may
return different verdicts. Short-circuit order and exceptions are explicit.

`SourceSizedLiquidAmbient` specifies the actual mixed-sort environment:
explicit declarations, inherited fresh sorts, Int defaults, and ambient
assumptions. Guard substitution does not rename ambient assumptions.
`SourceSizedLiquidContext` gives independent guard propositions in that
context. `SourceSizedLiquidAmbientPublic.public_correct` derives exact
raw-row acceptance, canonical bounded classes, distinct size order, and
both signed inverse laws from correct external Sat/Unsat responses.
It does not assume evaluator adequacy or a deterministic callback.
The all-Int, empty-assumption result remains as a separate specialization.

`SourceSizedLiquidExecutionPublic` models the complete bounded IO result as
an outer solver exception or a returned `Either GuardUnknown Table`.
Finite external result witnesses give a finite whole-query outcome even
when the outcome is an exception. The first-stop theorem retains successful
size, state, and candidate prefixes. It identifies the unchanged exception
or the original constraint and term for `GuardUnknown`.
An Unknown at the time limit raises `TimeLimitReached`; an earlier Unknown
remains a returned verdict. Nonpositive bounds make no evaluator calls.
External solver correctness and completion remain explicit premises.

## Ambient freshness defect and repair

The former adapter checked fresh names against explicit declarations only.
An implicit free name in an ambient assumption could capture a generated
fresh value. Under the assumption `__microcfta_actual_0 == 0`, querying an
independent fresh value with that same name returned Yes. Renaming that
fresh value to `__microcfta_actual_1` returned No.

Repair `48024a69` reserves the free symbols of ambient assumptions as well
as declared symbols. The colliding query now returns Unknown before an SMT
call. Ordinary implicit ambient declarations still work. A name bound only
inside a quantifier does not cause a collision.
`SourceSizedLiquidAmbientRepair` proves the repaired preflight and preserves
all successful noncolliding requests. `SourceSizedLiquidAmbientCollision`
retains the former behavior and the independent-name counterexample.
`repro/AmbientFreshCollision.hs` retains the native reproduction.
The original `SolverAdapter` remains the historical preparation model;
the repaired wrapper is the current ambient preflight model.

## Probabilities, PMFs, weights, and sampled ranks

`SourceSizedSampling` composes public Sized queries with a uniform class
rank draw. Every distinct accepted term has probability one divided by the
class count. Nonnegative requested term weights with positive total mass
normalize correctly. The existing rational-ticket sampler realizes those
weights. Strict positivity remains the compiled constructor's contract.

`SourceSizedBoundedSampling` proves that count-weighted uniform classes give
a uniform distribution on their concatenation. Empty classes add no mass.
`SourceSizedSamplerReplay` connects the existing bounded sampler's offsets
to the public prefix and proves sampled-rank replay and reverse lookup.
These are verified client compositions. Sized exports no sampling operation.

`SourcePmfAggregation` models insert-with-add and ascending map readback.
Duplicate output values retain the sum of all their occurrence masses.
Every event mass, total, and nonnegativity property is preserved.
`SourcePmfQuery` includes finite/cyclic dispatch, failure order, empty and
negative classes, normalization, and exact occurrence-rank size conditioning.
Finite size PMFs condition global occurrence masses. Cyclic size PMFs read
the independently built class sampler. Those paths need not have one global
unbounded distribution.

`SourceWeightedIndexed` proves the on-demand callback API. Metadata checks
do not establish callback validity or coverage. Each ticket must select a
valid replay rank, and every declared rank must have a positive ticket
weight. Both obligations are documented source contracts. Checked and native
counterexamples show why each is necessary; they are not source defects.
See `repro/WeightedIndexedContract.hs`.
Generator members, accepting runs, distinct FTA terms, and PMF output keys
remain separate concepts.

## Other current source bridges

The `EnumerationCPS*` modules preserve ordered branches, local states,
errors, state operations, traversals, and the public accepted support.
`EnumerationCPSDescent` and `EnumerationCPSBatchedEdge` cover inherited/new
constraint order, maximum-child arity checks, allocation, child traversal,
and residual recording. Canonical tries have no empty stored child entry.
An invalid-trie counterexample preserves that boundary.
`SourceUnionFindCompression` proves equality of the complete result after
omitting redundant writes. `IntersectionEmptyDomain` proves zero/successor
separation and exact node/edge memo keys under the shifted machine bound.

## Validation and remaining boundaries

The source repair passed 285 core and 204 generator examples in Nix.
The native ambient fixture returned `(Unknown,No,Yes)` and `No`.
Fourmolu and cabal-gild passed. No production test was added.
Test log: `/tmp/mcfta-ambient-20261013-tests.log`.
Root `HANDOFF.md` records the final combined Lean audit.

These are checked handwritten algorithmic source models. Concrete host
containers, lazy heaps, machine conversions, serialization, external SMT
answers, random backend laws, and verified extraction remain boundaries.
The standard three Lean axioms are allowed. No project or native-evaluation
axiom is allowed. Older constructor and equality drafts remain unchanged.
