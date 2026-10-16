# Current proof objective, caller resources, and remaining areas

Updated: 2026-10-16. Audited source main is `c0cc8a05`, merged at
`896b0a1c`. This checkpoint starts at published `e0476c52`.
Root FINDINGS keeps the Haskell repair handoff first.

## Top-level objective

Prove that the current Haskell library implements the intended constrained
tree languages and generators. Each public operation must satisfy its
stated contract on its stated domain. An operation that promises a finite
result must construct a terminating execution. Solver, callback, codec,
machine, and host assumptions must remain explicit.

For an automaton A and node-count size n, let S(A,n) be the set of distinct
accepted terms of that size. The exact query contract requires finite
evaluation, exactly S(A,n) without duplicates, its exact cardinality, the
specified enumeration order, public error behavior, and both rank/unrank
inverse laws. Rank follows the original sorted explicit graph rows.
Language preservation alone does not preserve rank order.

An exact transformation preserves the language. An over-approximation
includes the input language. Representative selection can remove terms.
Generator occurrences can repeat the same value. Sampling must implement
the stated distribution over the stated objects. Construction, readback,
transformations, queries, generators, and sampling must compose on their
actual returned values and states. There is no completed theorem for the
whole Haskell library.

## Current proof map

| Area | Proved boundary | Remaining area |
| --- | --- | --- |
| Exact size queries | `SourceSizedApiLaws.Exact` collects exact size classes, distinctness, counts, signed errors, ordered prefixes, and both rank inverses. `SourceSizedFiniteKeysPublic.native_sized_exact` derives these laws for successful modeled dispatch on validated original finite rows. | Complete current public adapters and concrete host correspondence under the explicit solver contracts. |
| Languages and transformations | Many semantic and source-model component laws distinguish exact transformations, over-approximations, and representative selection. | Compose all current public operations and their implementation adapters. |
| Constrained reduction | `SourceCurrentAllocatedFiniteOrdinaryOuterNumericRoot.finite` constructs a finite ordinary root, independent language law, physical invariants, and stable literal execution. Arbitrary guards, equality classes, and unequal path lengths are admitted. | Its reached numeric capacity plan is still a premise. Mu, references, and explicit unions are outside this finite ordinary domain. |
| Native intersection | Initial operand profiles give static constructor-request budgets. Actual checked traces derive their own result profile. Cold and serial finite endpoints construct receipts and capacity from initial headroom. | Compose this result with all generated callers and their other resource families. |
| Required and Projection | Actual constructor traces, output profiles, heights, counts, finite literal returns, and initial serial request budgets are proved. | Compose their results with the remaining Merge and Target stages. |
| Merge profiles | Column envelopes, selection/count facts, exact-owner cache certificates, and actual keep-first winner retention are proved. Existing finite Merge execution remains proved separately. | Prove profiles for the general recursive Merge producer. Then prove its constructor request bounds. |
| Generators and probability | Component laws cover rank multiplicity, ticket decoding, choices, products, conditioning, and distributions. | Connect current public frontends and concrete random execution to the stated objects and laws. |
| Concrete Haskell and full pipeline | Source models and focused executable comparisons cover many branches. | Complete containers, laziness, unfinished identities, memo publication, host interleavings, solver IO, callbacks, codecs, random draws, signed counters, and full composition. |

The strongest current result is a collection of checked component and
composition theorems. The Audit does not prove whole-library correspondence.
No useful completion percentage follows from module or theorem counts.

## New Required and Projection composition

The twelve new modules preserve all older proof source bytes.
Required retains the uniform descendant row and arity profile R,A, exact
forest length, and height bound. Projection has uniform row envelope
P = max(1,count) * max(1,R)^(depth+1), unchanged arity A, and no greater
height. Actual ordinary reads retain the heap. Actual makeNode and makeEdge
profiles include coherent constructor-cache hits.

Occurrences count all ordinary node and edge occurrences. Repeated
identities retain their multiplicity. For height H, the uniform limits are:

```
nodeCount(R,A,0) = 0
nodeCount(R,A,H+1) = 1 + R*A*nodeCount(R,A,H)
edgeCount(R,A,0) = 0
edgeCount(R,A,H+1) = R*(1 + A*edgeCount(R,A,H))
```

ConstructorWorkTrace retains each literal Work at its actual intermediate
heap. A constructor-cache hit counts as one request and zero new
reservations. Required requests at most the original node and edge
occurrences. Projection requests at most one plus the original node
occurrences and no edge constructors.

CallerResources constructs both finite results from initial semantic
readiness, availability, and resident profiles. SerialCallerResources
constructs Required followed by Projection. Before either stage, reserve:

```
nodes = 2*count*nodeCount(R,A,H) + 1
edges = count*edgeCount(R,A,H)
```

The proof derives the second stage's profile, height, length, and readiness
from the first actual return. Neither a completed stage nor a future profile
or request-count bound is an input. One imported kernel derives both final
packed-layout bounds from initial headroom. A further kernel combines the
generated profile P with ProfileBudget and derives remaining headroom for
a later native query. It does not construct that third query or supply its
native-machine adapter.

## Next proof and wider missing areas

1. Prove the general recursive Merge profile producer. Its local Body
   certificate must consume universal child certificates. Mutual induction
   on the actual Run and Call must derive the candidate certificate before
   finish. Finish must reread the current memo and certify its actual
   keep-first winner. The losing candidate can differ from that winner.
   Read `next-merge-producer-review.md` and `merge-profile-producer-next.md`
   in the evidence directory. No producer draft or Empty-only substitute
   endpoint exists.
2. Bound Merge constructors. Compose Operand, the rotated Target right fold,
   edits, class passes, local and parent calls, and the outer reduction.
   Derive the reached numeric plan from initial resources. Count all actual
   requests. Equality, domain, sidecar, and thunk resources need separate
   bounds. Constructor bounds do not prove instruction-step bounds.
3. Prove general progress for Mu, references, and explicit unions on a
   justified domain. Prove repeated-pass convergence separately. The public
   `reducePartially` operation performs one pass.
4. Complete current frontend correspondence. This includes typing inputs,
   binder bounds, type domains, drawn fields, derivation errors and their
   validation order, GHC pruning, generator ranks, and codecs. Existing
   component proofs do not cover every current public API.
5. Complete concrete Haskell and full-pipeline correspondence. Retain
   explicit assumptions for solver IO, callbacks, random draws, lazy forcing,
   unfinished records, memo publication, concurrent losing candidates, and
   signed host counters. Preserve the optimized interned core and the older
   constructor and equality proof targets.

## Haskell repair handoff

No Haskell file changes in this checkpoint. The recursive field-pool repair
`b9219b9e` is merged by PR #65 in main `c0cc8a05`. Current source rejects a
pool for a field of the datatype being derived. The unchanged Chain
reproducer returns `Left (FieldAtomOnDatatype "Next" 0)`. Standalone `holds`
still treats the pool as opaque. The repair rejects the invalid derivation
configuration. It does not recursively validate supplied pool descendants.

Root FINDINGS records the original failure, executable reproducer, affected
paths, commit, checks, and upstream status. It retains the old unfixed entry
as historical evidence. Add each later Haskell repair to that first section.
Reuse the unchanged strict Nix all-component build, 798 examples plus golden,
six-file Fourmolu, and four-package Cabal-gild and metadata checks.

## Validation and preservation

Pinned Lean 4.34.1 passes the full Audit: 2582 jobs and 60083 dependency
checks. All 86 declared public axiom/full-signature pairs pass. The final
kernel inventory has 27 integration pairs and three repeated public pairs.
Only propext, Classical.choice, and Quot.sound occur. Final imported probes
have no warnings or placeholders. The canonical build retains the older
unused-input warning. Failed drafts and diagnostic logs remain as evidence.

Preservation retains 6977 starting files and 2569 older non-Audit sources.
Forty-two frozen manifests check 339 module entries. Only the seven restart
authorities and three additive Audit imports can change among older files.
All Haskell files, repairs, counterexamples, drafts, stashes, other worktrees,
and the optimized interned core remain unchanged. Proof commits are
`221787aa`, `b2e23854`, `c9863c2d`, and `3d4ad799`. Evidence is in
`lean/restart-evidence/20261016-constrained-caller-profiles/`.
The full-library goal remains active.
