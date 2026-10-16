# Static constructor budgets for one ordinary native query

Updated: 2026-10-16. Source main is c0cc8a05, merged at 896b0a1c.
This checkpoint starts at published fcb5fdeb. Proof commits are 6f53e07d
and 9f985068. Root FINDINGS.md keeps the Haskell repair handoff first.
No Haskell file changes.

## Full objective

Prove that the current Haskell library implements the intended constrained
tree languages and generators. Retain separate language, termination,
transformation, exact size, count, order, both rank inverses, probability,
frontend, runtime, and pipeline contracts. There is no whole-library theorem.
Keep the optimized interned core and all older constructor and equality work.

## Computed original input profiles

NativeProfile computes uniform row and arity limits by visiting the complete
original finite ordinary records. The profile includes every literal child
and row occurrence. It retains guards and cached metadata without added
restrictions. Membership and monotonicity derive the same envelope for all
original descendant operands. Literal row joins retain repeated positions.
Their length is at most the product of the two input row-list lengths.

The current domain contains Empty and ordinary nodes. It excludes Mu,
references, and explicit unions. This profile does not describe output rows.

## Whole expansion budget

For row limit R and arity limit A, NativeBudgetNumbers defines:

- N(0) = 1.
- N(h+1) = 1 + R * R * (1 + A * N(h)).
- E(h) = 1 + A * N(h).

A node request uses N at the maximum original operand height. An edge request
uses E at the maximum original edge height. NativeBudget.nodeBudget and
edgeBudget compute the profile and cost from the two original operands.
They inspect no query execution, future heap, or actual request list.

The bound includes a full recursive expansion of every repeated subproblem.
Memo hits can skip that work. This conservative bound needs no producer
uniqueness theorem. It does not count native instruction steps. A swap retains
the same cost. That is sufficient for the constructor request bound.

## Literal compiler and yielded prefixes

NativeBudgetCode gives Work, recursive requests, ordered walks, continuations,
and driver finishes a compositional budget. Work bounds hold on every heap.
Continuations admit arbitrary returned values with their fixed budget.
Unchecked read, environment entry, and optional binder code are excluded.

NativeBudgetCompile derives the certificate for the actual node dispatcher.
It follows the literal guard order. Empty-domain reset is false. The row
branch includes every joined pair and the final makeNode. Accepted checked
edges include all zipped children and makeEdge. Rejected and mismatched edges
include the literal sentinel makeEdge. Equality operations have their own
resource family and do not change these two constructor supplies.

NativeBudgetExecution follows each actual yielded instruction. Literal Work
consumes its observed node and edge request count. Hits use the continuation
budget. Starts identify the complete captured owner through fixed-source
Origins and checked key injectivity. Finish frames retain the continuation.
Each finite yielded prefix retains a remaining budget and the cumulative
request count is at most its initial budget.

The principal node and edge prefix theorems derive all code certificates
from initial Good, resident domain operands, and initial Capacity. They bound
the sum of actual node and edge requests and each actual supply increment.
Initial supply plus the computed budget fitting the respective key layout
then derives Capacity at every yielded prefix. No current completion,
future capacity, result invariant, or actual-request bound is supplied.

## Remaining caller resources

This closes the input-derived reservation bound for one sequential native
query. It does not derive the complete outer numeric plan. Later queries
can use newly generated operands. Their row and arity envelopes must be
proved at the same actual returned state, including warm result hits.
Domain and height certificates alone do not imply these envelopes.

The sentinel has one Empty child even when its original input has arity
zero. A shared node/edge output envelope must account for that child.
Read next-outer-budget-review.md in the evidence directory for the exact
returned-certificate and producer-lifecycle route. Then bound required-path
rebuilds, projections, merge bodies, raw edits, class folds, and outer calls.
Compose their cumulative budgets from the original source resource profile.

This sequential Work bound does not count unrelated host interleavings,
losing concurrent publication candidates, repeated lazy forcing, equality
interner identities, sidecar/domain/thunk supplies, or storage. Concrete
signed Haskell counters remain separate from modeled packed-key limits.
General recursive progress, repeated-pass convergence, current frontend
adapters, concrete runtime, and full-pipeline composition remain open.
The full-library goal remains active.

## Validation and preservation

Pinned Lean 4.34.1 passes the full Audit: 2562 jobs and 59773 dependency
checks. All 75 declared public axiom/full-signature pairs and 20 integration
pairs pass. Namespace-aware coverage includes nested Bound and ControlBound
names. Only propext, Classical.choice, and Quot.sound occur. Final probes
have no warnings or placeholders. Canonical logs retain the older unused
input warning. Evidence is in
lean/restart-evidence/20261016-constrained-native-budget/.

Preservation retains 6768 starting files and 2555 older non-Audit proof
sources. Forty frozen manifests check 319 module entries. Only seven restart
authorities and additive Audit imports change. Historical repairs, drafts,
counterexamples, stashes, other worktrees, and the optimized core remain.

No Haskell behavior changes. Reuse strict Nix validation, 798 examples plus
golden, six-file Fourmolu, and four-package Cabal-gild and metadata checks.
Repair b9219b9e is already merged by PR #65. Add every later Haskell repair
first in root FINDINGS with failure, reproducer, paths, commit, checks, and
upstream status.
