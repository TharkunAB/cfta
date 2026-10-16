# Current proof objective and Merge reservation progress

Updated: 2026-10-16. Audited main is `c0cc8a05`, merged at `896b0a1c`.
This checkpoint starts at published `490f7509` on `formalize`.
Root FINDINGS keeps the external Haskell repair handoff first.

## Top-level objective

Prove that the current Haskell library implements its intended constrained
tree languages and generators. Each public operation must satisfy its
contract on its stated domain. Finite operations must construct a terminating
execution. Solver, callback, codec, machine, and host assumptions stay explicit.
There is no completed theorem for the whole library.

For an automaton A and node-count size n, let S(A,n) be its distinct accepted
terms of that size. Exact queries must return exactly S(A,n), without
duplicates, in the specified order. Counts must equal its cardinality.
Rank and unrank must satisfy both inverse laws. Signed inputs and errors
must follow the public contract. Exact rank order uses the original sorted
explicit graph rows. Language equality alone does not determine that order.

Exact transformations preserve the language. Merge is an over-approximation
and can add terms. Representative selection can remove terms. Generator
occurrences can repeat a value. Sampling must follow the specified
distribution over the specified objects. These contracts remain separate.

## Current proof map

| Area | Current proved boundary | Main remaining obligation |
| --- | --- | --- |
| Exact size queries | `SourceSizedApiLaws.Exact` states finite classes, distinctness, membership, counts, signed rejection, size order, and both rank inverses. `SourceSizedFiniteKeysPublic.native_sized_exact` derives it for successful modeled dispatch on validated original rows. | Complete current public adapters and concrete Haskell correspondence under the explicit solver contracts. |
| Constrained reduction | `SourceCurrentAllocatedFiniteOrdinaryOuterNumericRoot.bounded_prepared_root` constructs preparation, source build, a stable literal pass, full invariants, and exact guarded-language equality. It permits arbitrary guards and equality classes. | Derive its reached numeric capacity plan from initial inputs and resources. The finite ordinary domain excludes Mu, references, and explicit unions. |
| Native intersection | Input profiles derive request bounds. Actual traces produce output profiles. Finite and serial endpoints construct their own receipts and final capacity. | Compose these results with every generated caller and the other resource families. |
| Required and Projection | Actual returns retain profiles, heights, lengths, constructor traces, and initial serial budgets. | Carry the bounds through the complete reduction pipeline. |
| Merge and Operand | General recursive Merge profiles and constructor budgets are proved. Operand constructs Projection followed by Merge at their actual shared intermediate heap. | Compose Target's rotated right fold and its native queries, then edits, class passes, local calls, parent calls, and the outer pass. |
| Generators and probability | Component laws cover multiplicity, tickets, choices, products, conditioning, and distributions. | Complete frontend, codec, rank-order, and concrete random-execution correspondence. |
| Concrete Haskell | Source models and executable comparisons cover many implementation branches. | Complete container, lazy forcing, pending memo, solver IO, callback, signed-counter, concurrency, and full-pipeline correspondence. |

The root theorem still takes numeric capacity at independently reached
parent entries as an input. It does not assume a completed enclosing call.
Static bounds on the initial build do not discharge that later-entry plan.
The next resource proof must derive that plan from initial data.
General recursive progress and repeated-pass convergence are separate.
The public partial reduction performs one pass.

## New Merge and Operand bounds

Six additive modules extend the prior profile proof. For row limit R, arity
A, and height H, their Merge constructor-request bounds are:

```
N(R,A,0) = 0
N(R,A,H+1) = 1 + R*A*(1 + N(R*R,A,H))
E(R,A,0) = 0
E(R,A,H+1) = R + R*A*E(R*R,A,H)
```

The squared row limit accounts for a generated column union. Local
certificates cover every body branch. Mutual induction follows the actual
Run and Call graph. Each miss counts its complete body before completion
retains the current first winner. A warm Merge hit has an empty Work trace.
No future body contract, returned profile, or supplied count is required.

MergeBudgetFinite constructs its own finite allocated and stable literal
return. Its cold endpoint derives empty-table invariants. Its full caller
retains the same semantic Post and language inclusion. Its capacity endpoint
derives final supply bounds from initial headroom.

For a forest of at most C values and path length at most D, set
P = max(1,C)*max(1,R)^(D+1). OperandResources constructs the full existing
receipt. Its Projection and Merge traces meet at the actual intermediate
heap. Its initial request bounds are:

```
nodes = 1 + C*OccurrenceBounds.nodeCount(R,A,H) + N(P,A,H)
edges = E(P,A,H)
```

The result includes the generated output profile and bounded height.
The conclusion supplies a WorkTrace witness for the actual returned heaps
and bounds their final supplies. It does not state a universal instruction
cost or runtime bound. Constructor-cache hits can use requests without new
reservations. Equality, domain, sidecar, thunk, signed host counter, and
concurrent candidate resources need separate proofs.

## Validation and Haskell status

The pinned Lean 4.34.1 Audit passes 2593 jobs and 60187 dependency checks.
All 45 declared public axiom/full-signature pairs pass. Eleven component
integration pairs pass. Only propext, Classical.choice, and Quot.sound occur.
The existing unused-input dependency warning remains. Independent review
found no material defect within the stated component boundary.
Evidence is in `lean/restart-evidence/20261016-constrained-merge-reservations/`.

No Haskell file changes in this checkpoint. Repair `b9219b9e` is merged by
PR #65 in main `c0cc8a05`. A pool for a field of the datatype being derived
now fails with `FieldAtomOnDatatype`. The original Chain reproducer returns
`Left (FieldAtomOnDatatype "Next" 0)`. Standalone `holds` retains its opaque
pool behavior. The repair rejects the invalid derivation configuration.
Root FINDINGS records its failure, reproducer, paths, commit, checks, and
upstream status for external work. Keep every later Haskell repair there.

Preservation retains all 7233 starting tracked files and 2586 older non-Audit
proof sources. Forty-four frozen manifests check 350 module entries.
All 234 starting Haskell files retain their bytes. Older repairs,
counterexamples, drafts, stashes, other worktrees, and the optimized interned
core remain. The full-library goal stays active.
