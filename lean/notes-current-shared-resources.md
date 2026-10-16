# Shared target and leaf resources from initial bounds

Updated: 2026-10-16 21:11 CEST. Audited main is `c0cc8a05`, merged at `896b0a1c`.
This checkpoint starts at published `0f1c72f7` on `formalize`.
Proof commits are `882c4eb8` and `dd1e246d`.

## Full objective and current boundary

Prove that the current Haskell library implements its intended constrained
tree languages and generators. Keep language, exact transformations,
exact size/count/order/rank, generator multiplicity, and probability
contracts separate. Construct finite executions on their stated domains.
Keep solver, callback, codec, machine, and host assumptions explicit.
There is no completed whole-library theorem. The goal stays active.

## Causal shared profiles

SharedProfiles.Stored retains native structural and output certificates,
universal Merge output profiles, and a profile and height for each present
class-local target slot. Fresh slots derive the last condition without a
result oracle. A miss must supply the certificate produced for its actual
Target return. Checked advancement retains immutable slots and Merge entries.
The existing domain-only Stored follows from this stronger invariant.

SharedProfileBounds derives exact source-order selected operand length
`record.paths.length - 1` from coherence and selected membership. It derives
uniform target row and constructor budgets from original record limits.
Domain-only slots and historical semantic receipts cannot supply these
numeric profiles without another proof.

## Constructed shared Force and Leaf

Let the captured forest have row and arity limits R,A, length bound C,
height bound H, maximum record path length D, and m distinct record paths.
Use the existing Target envelopes:

```text
T = TargetResources.outputRows R C D H (m - 1)
B = max A 1
ForceN = 0 on a present slot; TargetResources.nodeBudget R A C D H (m - 1) otherwise
ForceE = 0 on a present slot; TargetResources.edgeBudget R A C D H (m - 1) otherwise
```

SharedForceResources.complete constructs its own full existing Receipt.
A hit returns the same whole state and memos with an empty Work trace.
A miss constructs the full actual Target from captured bounds and initial
headroom. It stores that exact value, checked state, and returned Merge memo.
The return includes causal profiles, actual Work, request bounds, final
capacity, and both final supply bounds. No future range plan is an input.

For a current input profile r,a and height bound h, define:

```text
M = max T r
K = max B a
Q = NativeBudgetNumbers.nodeBudget M K (max H h)
LeafN = ForceN + Q
LeafE = ForceE + Q
output profile = (M*M, max K 1)
```

SharedLeafResources.complete first constructs Force. Its actual prefix
supply bounds and initial LeafN/LeafE headroom derive the next native entry.
It then constructs the exact query on the returned target and current input.
The full existing Leaf Receipt joins both stages. The output has the stated
profile and no greater height than the current input. Both Work traces join
at the actual intermediate heap. Captured and current inputs can differ.
The native query retains its incoming global memo bundle. The preceding
Force can change that bundle. The proof does not equate initial and final
memos or reset any warm table.

SharedInitialCapacity proves uniqueness of stable literal Force returns.
It identifies the returned value and the entire Shared state. Initial force
headroom derives the existing ForceCapacity and LeafCapacity for every raw
earlier Force return. LeafCapacity supplies capacity at query entry. It is
not a bound on total Leaf Work; the separate resource endpoint proves that.

## Literal values and the next caller

ValuePositions counts Empty as one value position. It retains repeated rows,
values, and identities. A profiled value of height at most H has at most
`1 + A * OccurrenceBounds.edgeCount R A H` positions. Multiply this bound
by C for a forest of at most C values. This is pure structural counting.
It does not yet prove the number of callbacks in an actual edit execution.

Read `restart-evidence/20261016-constrained-shared-resources/next-edit-resources.md`.
Next prove actual node/children/rows/list callback counts, then construct
edits with cumulative initial resources and output profiles. Continue through
classes and the tail-first pass, local calls, parents, and the outer root.
Its reached-parent numeric plan remains an input until this composition.
General Mu/reference/union progress, repeated passes, other resource
families, current frontends, concrete Haskell, and full pipelines remain open.

## Validation and preservation

The pinned Lean Audit passes 2605 jobs and 60357 dependency checks.
All 43 public axiom/full-signature pairs and 15 integration pairs pass.
Only propext, Classical.choice, and Quot.sound occur. Kernels construct
fresh misses and same-state hits, derive existing range and finite APIs
without supplied plans, and compose two actual Leaves from initial headroom.
Independent review found no material defect in these component contracts.
The older unused-input warning remains in the canonical dependency build.

Preservation retains 7423 starting tracked files, 2598 older non-Audit proof
sources, all 234 Haskell files, and 46 manifests with 362 frozen module entries.
Stashes, other worktrees, repairs, counterexamples, drafts, and the optimized
interned core remain. Evidence is in the corresponding restart directory.

No Haskell change or new verified defect. The field-pool repair `b9219b9e`
is already merged by PR #65. Root FINDINGS retains its external handoff first.
Reuse unchanged strict Nix checks, 798 examples plus golden, six-file
Fourmolu, and four-package Cabal-gild and metadata checks.
