# Current library proof status and recursive allocation accounting

This checkpoint starts at published 8883b39a. Its proof commits are c4d0108b,
2771817b, and 9461e672. Source main remains c0cc8a05, merged locally at 896b0a1c.
The full library goal remains active.

## Top-level target

Prove the intended contracts of the complete library. Then prove that the
current public Haskell operations implement those contracts. For each public
operation P, the schematic target is:

`Valid(input) ∧ Supported_P(input, initialResources) ⇒ runHaskell(P, input) terminates with result ∧ Spec_P(input, result)`.

This is a family of target theorems. The complete implementation theorem
does not exist yet. Support must describe initial inputs and resources.
It must not assume future successful execution or the desired result.
Documented errors and validation order are observable results.

The contracts include exact distinct accepted terms per node-count size,
counts, enumeration order, both rank/unrank inverses, transformation language
relations, generation coverage, and sampling laws. Distinct terms, accepting
runs, and generated members remain separate. Exact transformations require
language equality. Over-approximations require inclusion. Representative
selection has its own restriction contract.

## Current proof map

| Area | Established result | Remaining boundary |
| --- | --- | --- |
| Exact Sized queries | Exact size classes, counts, original explicit row order, size-major enumeration, and both rank/unrank inverses. Validated graph keys supply a finite carrier. | Concrete host and solver adapters and complete public composition. |
| Interned construction | Finite modeled repaired closed construction with Mu and unions. Literal initial constructor syntax now bounds allocation for every outcome. | Haskell lazy publication, interning, and runtime correspondence. |
| Checked recursive intersection | Initial numeric bounds construct finite exact queries. Current inventories and captured origins retain joint laws for produced operands. | One initial resource budget for whole sequences that consume new results. |
| Original-source serial queries | One initial budget constructs any finite list of queries over a fixed original source. Warm native caches, equality operations, and global tables remain present. | New operands outside that source and total memory capacity. |
| Memo-aware Merge and selected Operand | Actual Merge derives universal cap certificates before publication. Initial selected domains construct finite Operands with unrelated open ordinary siblings. | Arbitrary constrained Mu bodies and runtime publication. |
| Mixed Edit and class pass | Actual editor reads and the tail-first class pass retain stores and derive finite syntax depth bounds. | General first target misses and editor/class completion from initial resources. |
| Ordinary constrained reduction | Initial profiles and constructor headroom derive a resource Plan. A complete modeled pass retains guarded language and stores. | This ordinary domain excludes Mu, references, and unions in every descendant. |
| Recursive allocation accounting | Full constructor, stored substitution, optional binder, and checked-prefix charges cover nested Mu and pending outcomes. Successful initial source reads have finite branching and size profiles. | Derive the accumulated charges from the original generated-query inputs. |
| Other components | Existing language, equality, arithmetic, union-find, memo, ranking, generation, sampling, and restricted driver proofs remain preserved. | General constrained descent, convergence, current adapters, and complete public pipelines. |

These results concern explicit modeled source workers and caches. They do
not establish full correspondence with compiled Haskell execution. A theorem
count or successful check does not give a completion percentage.

## Initial constructor and stored-body charges

InternedFreshOrdinaryAllocationBudget defines separate node and edge budgets
by recursion on the initial constructor syntax. The main build_bound theorem
covers every returned outcome. It requires no successful completion, heap
facts, availability, callback result, or replacement-size bound.

For a binder body, the conservative charges are:

`nodeBudget(binder body) = 3 * nodeBudget(body) + 4`

`edgeBudget(binder body) = 3 * edgeBudget(body)`.

The three body charges cover the depth probe, ordinary probe, and fresh body.
The extra node charges cover root normalization and the Mu reservation.
The proof retains cache-hit, reserved-owner, and pending branches. Ordered
children and raw rows retain their literal execution order.

InternedFreshOrdinaryStoredAllocationBudget applies the same bound to the
actual repaired stored execute and unfold functions. Its charges use the
initial encoded value or literal Mu body. Replacement values are opaque
inputs at variable positions. No PreparedWithoutMu premise restricts the
stored syntax. A single unfold bound does not prove a full recursive Head.

## Optional binders and checked prefixes

SourceCurrentAllocatedRecursiveOptionalBudget bounds the actual maybeMu
instruction. An unused pair has zero charge. A used pair pays the full
fresh optional-binder syntax charge, including nested Mu and unions.
Facts and availability justify the bridge to that constructor execution.
The resulting bound covers every outcome, including pending outcomes.
The checked-state result retains the same native tables, domains, and
equality operations. Only the constructor heap can change in this step.

SourceCurrentAllocatedRecursiveAllocationTrace gives every checked
instruction a node and edge charge. Work uses its actual literal cache
requests. Optional binders use the preceding full body budget. Other
instructions allocate no constructor identities. step_bound covers every
step outcome. prefix_bound retains validity and fields across every finite
physical prefix. charges_append adds charges at the exact common control
and returned state.

These prefix charges depend on the actual executed prefix. They are not an
initial admission condition for a whole generated query. The missing proof
must derive a bound on all reached body and Work charges from the original
inputs. Earlier result-size and store certificates must justify later
generated bodies. A future-prefix premise cannot replace this derivation.

## Initial source payload profiles

SourceRecursiveIntersectionSourceProfile reads all successful node and edge
payloads in their independent initial issued ranges. Sums of literal row,
union-member, and child counts give conservative branching limits. The
logical size sums include stored Mu bodies and probes. Size bounds use the
caller's SizeOf instances. They are not byte or runtime estimates.

Availability derives these profiles for actual resident values and edges.
An unrecorded reference has no complete stored-size bound from this profile.
An earlier successful read retains its literal payload and original bounds
through record growth and issued-key growth. An absent earlier identity
has no such readback guarantee. Initial payload bounds do not bound every
new payload that later execution can construct.

## Remaining work

1. Derive shared initial node, edge, and domain resources for serial queries
   that consume newly produced operands. Connect initial source profiles,
   result sizes, constructor charges, projection, Merge, and editor reads.
2. Construct general Target, Force misses, mixed Edit, and ClassPass from
   initial resources. Current depth and store results prove preservation;
   they do not establish general finite execution.
3. Produce the active and stored certificates required by general constrained
   outer descent. Retain the source gate that admits closed no-Mu endpoints
   independently of their own guard. Cover arbitrary constrained Mu bodies.
4. Prove repeated reduction convergence. Complete remaining recursive pruning
   and compiler callers. One complete pass is not a fixed point.
5. Complete current typing and refinement frontend adapters. Include drawn
   fields, symbolic measures, documented errors, validation order, and
   generator-specific rank order. Complete solver, runtime, IO, randomness,
   concrete capacity, and user-code adapters with explicit assumptions.
6. Compose complete public construction, transformation, graph conversion,
   exact query, generation, and sampling pipelines, including serial calls.

Preserve older constructor and equality work and the optimized interned core.
Do not repeat the completed source-rebase, origin, Merge, selected-Operand,
or mixed-editor cap proofs. Continue from the missing initial root budget.

## Validation and preservation

The pinned Lean 4.34.1 Audit passes 2854 jobs and 63392 dependency checks.
Only propext, Classical.choice, and Quot.sound occur. All five production
modules pass strict checks with zero-byte logs. All 70 imported axiom and
signature pairs pass in ten groups. Five component manifests verify 174
entries. Canonical replay retains only the older unused-input warning.

Concrete source-profile integration exposed a mismatch between the generic
and concrete SizeOf instances. The final size helpers accept caller
instances. All branching-only APIs retain their earlier assumptions. The
prior source, failed attempts, corrected source, and final checks remain
in the evidence directory. No older production proof was changed.

Preservation retains 12226 starting tracked files, 2848 older non-Audit
production proofs, all 239 Haskell files, and all 206 active-package files.
All 73 frozen production manifests verify their 611 entries. Stashes and
three other worktrees retain their initial state. Read checkpoint-validation
and preservation-final in restart-evidence/20261017-generated-resource-profiles.

## Haskell repair handoff

No Haskell source change or new Haskell defect occurs in this checkpoint.
Root FINDINGS keeps the external repair registry first. Recursive field-pool
repair b9219b9e is merged in c0cc8a05 and locally validated. The Chain example
returns `Left (FieldAtomOnDatatype "Next" 0)`. Derivation rejects the supplied
recursive pool. Standalone holds retains opaque-pool evaluation.

Reuse the unchanged strict Nix all-component build, 798 examples plus golden,
Fourmolu, and Cabal-gild evidence for this source. Record every later Haskell
repair in root FINDINGS with its failure, reproducer, affected paths, commit,
checks, and upstream status.
