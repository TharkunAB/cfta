# Current proof objective and initial query word bounds

Updated: 2026-10-16. Source main is `c0cc8a05`, merged at `896b0a1c`.
This checkpoint starts at published `1bbb75c4`. Proof commits are
`ae8b53b5` and `ee54b123`. Root FINDINGS.md keeps the external Haskell
repair handoff first. No Haskell file changes.

## Top-level objective

Prove that the current Haskell library implements the intended constrained
tree languages and generators. Each public operation must implement its
contract on its stated domain. Each finite operation must construct a
terminating execution. Solver, callback, codec, machine, and host assumptions
must remain explicit. There is no completed whole-library theorem.

For an automaton A and node-count size n, let S(A,n) contain exactly its
distinct accepted terms of size n. The exact query contract requires:

- The size query returns exactly S(A,n), without duplicates.
- The count equals the cardinality of S(A,n).
- Enumeration follows the specified order of the original sorted graph rows.
- Rank and unrank satisfy both inverse laws on their stated domains.
- Finite queries terminate and return the specified public errors.

The remaining contracts are separate. Exact transformations preserve the
language. Over-approximations include it. Representative selection can remove
terms. Generator occurrences can contain duplicate values. Sampling must
implement the specified distribution over the specified objects. Construction,
readback, transformations, queries, generators, and sampling must compose at
the same actual states and returned values.

## Current state

| Area | Proved boundary | Remaining work |
| --- | --- | --- |
| Languages and transformations | Many semantic and source-model component laws, each with its own domain. | Complete current implementation adapters and composition. |
| Exact size queries | Exact accepted classes, distinctness, finite evaluation, counts, ordered prefixes, signed errors, and both rank inverses. `SourceSizedApiLaws.Exact` collects the laws. `SourceSizedFiniteKeysPublic.native_sized_exact` derives them for successful modeled dispatch on validated original finite rows. | Retain explicit solver and host assumptions. Complete current frontend, generator, and pipeline correspondence. |
| Constrained reduction | Actual completed-call correctness and constructed finite ordinary root execution. Arbitrary guards, equality classes, and unequal path lengths are admitted in this ordinary domain. | Derive root capacity from initial resources. Prove general Mu, reference, union, and repeated-pass progress. |
| One native intersection | Constructed finite checked execution from initial resident finite ordinary operands and initial key bounds. No future WordRanges input remains in the new endpoint. | Bound identities of generated operands at later query entries. |
| Generators and probability | Separate component laws for ranks, multiplicity, ticket decoding, choices, products, and distributions. | Connect current public frontends and random execution to those contracts. |
| Concrete Haskell and full pipeline | Source models and focused executable comparisons. | Complete containers, laziness, unfinished identities, memo publication, concurrency, solver IO, callbacks, codecs, random draws, machine bounds, and full composition. |

Read notes-current-constrained-outer-completion.md for the constructed
ordinary root. Its entry range plan is still an explicit premise. Mu,
references, and explicit unions are outside that finite ordinary domain.
The older plain Region permits Mu and unions as opaque stops. It restricts
ordinary equalities. These two proof domains remain separate.

Exact ranks use the original sorted explicit graph rows. A language-preserving
transformation can change ranks. The optimized interned core remains the
construction and transformation implementation. Read
docs/adr/0004-explicit-graph-boundary.md.

## New initial operand proof

`FiniteOrdinaryKeys` records recursive node and edge identity bounds. It
derives these bounds from initial coherent, linked resident records and the
two initial supply bounds. At width `bits + 2`, ordinary node identities are
less than `2^bits`. Edge identities are less than `2^(bits+2)`. Initial
supplies may equal these limits because each resident identity is below its
current supply. Tagged node packing retains its reserved tag bits.

`WordCode` certifies the actual ordinary request schedule. Recursive requests
use original operand subrecords. Constructor continuations permit arbitrary
returned values. They do not request the newly constructed output within the
same query. Driver finish frames retain the continuation certificate.

`WordExecution.Origins` fixes one initial machine. Every native memo cell
retains its checked captured request in that machine, in every cell phase.
The invariant puts no bound or semantic condition on returned values.
Lookup, demand, heap work, and finish preserve it. Checked key injectivity
identifies a warm evaluated owner before its body is compiled.

`WordExecution.reached` inducts over raw actual `Demand.Steps`. It derives the
origin invariant, certified next control, and current word check at every
finite yielded prefix. It assumes neither a completed physical Trace nor
future word checks. Busy or failed execution does not become successful
merely because its keys are safe.

`Words.node/edge` derive the existing checked WordRanges from initial Good,
resident operands, and recursive key certificates. `node_of_domain` and
`edge_of_domain` derive the certificates from the initial counters. No Idle,
SemanticReady, structural Stored, or completion premise is needed for this
key-safety result. Warm tables remain intact.

`BoundedFinite.finite/of_domain` compose these word checks with the existing
finite native theorem. They construct their own physical Receipt, final
Idle, SemanticReady, structural Stored, result availability, result domain,
both original-operand height bounds, and empty free-name list. Initial Good,
SemanticReady, Stored, Idle, and resident domain operands remain explicit.
There is no future WordRanges input. This structural finite endpoint alone
does not assert an additional language law.

## New Scan and supplied-read verification

`ScanRanges` derives the ordinary Scan range checks from initial coherent,
available domain records. The fast Scan branch uses no seeded query.
Its adapters cover Scan-only local and actual edge-call checks. They do not
derive complete Class target/leaf capacity.

`OuterVerification` covers all eight supplied actual strict read families.
It derives Checks, full Post, structural bounds, and independent language
laws at the same returned caller. Completed earlier prefixes supply the next
initial context. No Checks or range plan is a public input. A supplied
completed strict read graph remains an input. This result verifies that
graph; it does not construct it or prove general termination.

## Next missing capacity proof

One query can construct results with new identities. A later Target or Leaf
can request those results. The initial original-operand key proof does not
bound them. Result domain and height do not bound identity supplies.

Next define numeric capacity at independently reached query entries. Follow
actual earlier prefixes. At each entry, derive current residency, domain,
readiness, and causal certificates before applying `Words`. Do not use a
completed current query to derive its own range premise. Then prove upper
bounds on actual node, edge, and equality reservation attempts. Count losing
and intervening reservations as well as published entries. Global Haskell
supplies require an explicit process-history or isolation assumption.

Read prefix-reservations-review.md and prefix-words-review.md in this
checkpoint's evidence directory. General recursive reduction, repeated-pass
convergence, frontend adapters, concrete runtime, and full pipeline remain
open. The full-library goal remains active.

## Validation and handoff

Pinned Lean 4.34.1 passes the full Audit: 2538 jobs and 59423 dependency
checks. All 76 declared public axiom/full-signature pairs pass. Imported
integration probes check raw prefixes, complete warm owners, arbitrary
returned identities, supplied-read prefixes, initial counter boundaries,
and two constructed queries at their same actual warm state. Only `propext`,
`Classical.choice`, and `Quot.sound` occur. The canonical build retains the
historical unused-input warning. Final imported probes contain no warning
or placeholder.

Evidence is in lean/restart-evidence/20261016-constrained-query-words/.
Preservation retains 6422 starting files and 2530 older non-Audit proof
sources, apart from the seven named restart authorities and additive Audit
imports. Thirty-seven frozen manifests check 295 module entries. Older
proofs, counterexamples, repairs, drafts, stashes, other worktrees, and the
optimized interned core remain.

The recursive field-pool repair `b9219b9e` is merged by PR #65 in current
main. The original Chain reproducer returns
`Left (FieldAtomOnDatatype "Next" 0)`. The repair rejects the invalid
derivation configuration. Standalone `holds` retains opaque pool evaluation.
Root FINDINGS.md records the failure, executable reproducer, affected paths,
commit, checks, and upstream status. Record every later Haskell repair there.
Reuse unchanged source validation: strict Nix all-component build, 798
examples plus golden, six-file Fourmolu, and four-package Cabal-gild and
metadata checks.
