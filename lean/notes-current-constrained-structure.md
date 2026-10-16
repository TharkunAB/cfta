# Current constrained finite ordinary native structure

## Full proof objective

The objective is end-to-end implementation correspondence for cfta.
The accepted terms of the live implementation must agree with the intended
language. Exact transformations must preserve that language. Over-approximations
and representative selection have their own contracts. Each size class must
contain exactly the accepted terms with that node count. Counts, ordered ranks,
both rank/unrank inverses, and probability laws are separate requirements.
The proof must also establish finite execution for the intended calls.
Frontend, runtime, and full-pipeline composition remain part of the objective.
There is no completed single theorem for that whole objective yet.

The explicit graph is the semantic boundary of exact listing, counting, and
ranking. The optimized interned core remains the construction and transformation
implementation. Read CONTEXT.md and docs/adr/0004-explicit-graph-boundary.md.
Keep older constructor and equality proofs, counterexamples, repairs, and drafts.

## New result

Source main is `c0cc8a05`, merged at `896b0a1c`. The starting published
checkpoint is `d7ce6713`. The proof adds eight modules without changing
any older non-Audit proof source.

| Module suffix | Result |
| --- | --- |
| Domain | Recursive ordinary domain, exact membership, constructor closure, and height bounds. |
| Stored | Conditional structural certificates for actual returned node and edge owners. |
| Code | Local continuation certificates for exact source requests and physical primitive inputs. |
| Node | Literal ordered row join and dispatcher certificates. |
| Edge | Literal checked accepted, rejected, and arity-mismatch certificates. |
| Frames | Physical finish splits and exact evaluating-owner retention. |
| Execution | Actual trace induction and public node/edge structural result endpoints. |
| Finite | Derived original syntax and closedness, then finite completion at the same returned state. |

All modules use the prefix `SourceCurrentAllocatedFiniteOrdinary`.
Commits are `106e4123`, `5d54241d`, `a4506576`, and `62f30089`.

The domain contains Empty and ordinary nodes. Every actual row child belongs
to the same domain. Guards and equality classes are unrestricted. It excludes
Mu, explicit union, and reference records. Raw metadata has no pure domain
restriction. Coherent available readback derives the cached closedness fact.

For empty-seen requests on this domain, Execution.node_trace and edge_trace
derive result domain membership and both inequalities:

```
height result <= height left
height result <= height right
```

Edge requests use edgeHeight. Each primitive result is the actual constructor
return at its reached heap. Ordered row pairs and zipped child occurrences
retain their original multiplicity. The sentinel has height zero. Its child
arity can differ from the original edge arity.

The main induction follows actual shorter physical traces. A nested body
derives its result certificate before its driver finish installs it. Physical
key readback identifies the whole captured request. The body retains the
same evaluating handle. Warm hits read certificates for their actual owners.
There is no historical eager-execution transfer or supplied parent result law.

Finite.finite constructs the completed physical receipt from initial Good,
SemanticReady, Stored, Idle, available domain operands, and reached WordRanges.
It derives original syntax and operand closedness. It returns Idle,
SemanticReady, Stored, result domain, both bounds, and result closedness at
the same actual state. It does not take a future graph or successful-run premise.

## Scope boundaries

The seen-pair list must be empty. An arbitrary nonempty list can select a
recursive placeholder before ordinary payload dispatch. This is part of the
existing recursive protocol. It is not a new Haskell defect. The public request
starts with emptyDomain, and this domain never enters a Mu binder.

Cold tables derive Stored. Arbitrary existing warm tables require initial
structural admission. Physical validity alone states no result height law.
Only certified source controls have the preservation theorem. Arbitrary Code
can finish a handle with a physically available result of the wrong height.

This result proves structural bounds and finite native intersection in its
stated domain. It does not by itself prove language equivalence, general
constrained reduction progress, GHC forcing, host-table publication, or a
frontend adapter. Existing language results remain separate components.

The preceding plain recursive worker and constructed/prepared root theorems
still apply in Region. They derive their own execution and full language law.
General constrained completion remains open. Next compose the new bounds
through actual target edits, shared edits, class folds, and local/parent
construction. Warm class slots and merge results need causal domain
certificates. Closed availability and language narrowing do not establish
finite ordinary structure. Read next-class-progress-review.md in the evidence
directory.
Mu constraint migration, unequal-length classes, and repeated-pass convergence
remain separate obligations. Current reducePartially performs one pass.
New drawn-field frontend states, validation order, and rank order still need
adapters. Concrete runtime and the whole exact query pipeline remain open.

## Validation and preservation

The pinned full Audit passes 2500 jobs and checks 59028 theorem dependencies.
Only propext, Classical.choice, and Quot.sound are permitted.
Public signature/axiom probes and integration kernels are recorded in
lean/restart-evidence/20261016-constrained-structure/.

The preservation check retains 5837 starting files and all 2491 older
non-Audit proof sources. Thirty-three frozen manifests check 257 entries.
All 234 starting Haskell files and 206 active-package files retain their bytes.
Historical repair text, stashes, and the three other worktrees remain.
No Haskell patch is added. Reuse the unchanged source's strict Nix build,
798 examples plus golden, Fourmolu, Cabal-gild, and package metadata checks.
Root FINDINGS.md keeps the external repair handoff first. The recursive
field-pool repair b9219b9e is already merged and locally validated there.
The full objective remains active.
