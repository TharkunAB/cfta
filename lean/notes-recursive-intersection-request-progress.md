# Recursive request bounds and native demand progress

Proof checkpoint: `2a9cea9c`. Upstream: `f59c198d`, 2026-10-14.
Request-decrease checkpoint: `e1ae3098`.
Read [exact original inputs](notes-recursive-intersection-input-exact.md) first.

## Extensional domains and exact execution

`IntersectDomainEquivalence.DomainEquivalent` retains lookup equality and
cutoff membership. Lookup equality also determines free-map emptiness.
No separate reset-test assumption is supplied. Extending both domains with
the same entries retains equivalence. `domain_equivalent_workers` proves
exact node and edge execution equality at every finite bound, including
all results and failures.

`SourceRecursiveIntersectionDomainEquivalence` connects actual sorted source
domains to semantic overwrite lists. `entered_key` derives the actual
allocated key from valid domain-cache allocation. `entered_domain_equivalent`
uses actual operand codecs, identities, and bindings. The result retains
all semantic observations after canonical allocation.

## Least successful request bound

`IntersectRequiredFuel.Completes` states that one semantic request has a
finite successful execution. `requiredFuel` selects its least successful
natural bound. The proof uses natural-number induction and classical choice.
It adds no library dependency or project axiom. It is a proof measure, not
a replacement source execution or search procedure.

`requiredFuel_success`, `requiredFuel_le`, and `requiredFuel_positive` derive
actual success, minimality, and positivity. The measure depends on the exact
request and domain observations. It does not depend on enclosing closed roots.
`requiredFuel_domain` proves equality under extensional domain equivalence.

`IntersectImmediateCalls.branchCalls` retains the exact recursive requests
of every source branch. It includes reset, ordered swap, original Mu bodies,
ordered union members, original reference lookup, and equal-symbol row joins.
`Immediate` includes ordered paired edge children. `immediate_success` derives
successful child execution at the preceding parent bound.
`immediate_requiredFuel` then derives a strict decrease for every immediate
request. No successful child execution is supplied as a premise.

`SourceRecursiveIntersectionRequestProgress.physical_child_requiredFuel`
uses actual physical branch selection and derives codecs and cached
closedness from original available records. `entered_requiredFuel` derives
the canonical child completion certificate and its unchanged least bound.
`initial_complete` starts with actual closed original physical records.
It derives the initial certificate from the proved finite semantic schedule.

## Running-cell origin and completed frames

`FlatMemoThunkRunningBefore` derives that publication and completion cannot
create a running cell. An actual busy demand identifies the original running
cell. An absent demand identifies an absent cell. Demand can create a running
phase only at its own selected handle. Completion leaves no running cell at
the handle it completes.

`SourceRecursiveIntersectionNativeRunningBefore.Evaluation.running_before`
proves that each running cell after a completed source body was already
running before it. The earlier forward-retention theorem remains. Together
they give exact running-cell retention for completed source code.
`done_running_before` starts with an actual completed native execution.
It does not require a supplied nested evaluation tree.

`node_body_finish_before` and `edge_body_finish_before` prove that an actual
completed body and its original completion frame leave only the running
cells present before its demand. Nested requests cannot leave new running
cells behind on successful completion.

## Active bounds and actual native observations

`SourceRecursiveIntersectionNativeActiveBounds.nodeSemantic` and `edgeSemantic`
read the semantic request from exact captured physical fields.
`ActiveAbove` states that every running cell has a finite least semantic
bound at or above the current source-body bound.

`active_initial` derives this invariant for empty memo state at every bound.
Actual publication and physical/domain effects retain it. A weaker current
bound retains it. Actual demand adds only the selected request's certified
bound. An original completed body and finish restore the caller's stronger
bound. The later all-branch invariant and native bound induction compose
these lemmas. See [finite native observations](notes-recursive-intersection-native-finite.md).

`SourceRecursiveIntersectionNativeDemandProgress.node_absent_impossible` and
`edge_absent_impossible` exclude absent observations after actual publication
from structurally valid memo state. No semantic completion premise is needed.
`node_busy_impossible` and `edge_busy_impossible` exclude busy observations
for checked requests strictly below all enclosing active bounds. Actual
lookup, demand, complete source records, and checked machine keys derive exact
captured request identity. Active bounds and the strict request decrease
remain explicit premises. No general native completion theorem is claimed.

## Current continuation and next proof target

The compiled body-limit invariant and its native strong bound induction are
now proved at `2129c3ed`. Read
[finite native observations](notes-recursive-intersection-native-finite.md).
`cold_node_terminal` gives a finite return or exact pending constructor from
actual closed original roots under checked words. No source failure, absent
handle, busy cell, or yielded outcome satisfies that result.

Next exclude pending optional binders at their actual source caches and
bodies. Derive coverage and `PreparedWithoutMu`, or the larger nested
constructor invariant. Closed roots alone do not give preparation.
Derive successful first-run completion, output preparation, and actual
product-row membership/rejection. Do not supply a completed trace or a
no-pending callback contract as a replacement source proof.

## Validation at this checkpoint

The request-progress audit passes 1,268 jobs and 41,469 dependency checks:
`/tmp/mcfta-request-progress-20261014-audit.log`.
After the running-origin and active-bound proofs, the pinned Lean 4.34.1
aggregate build passes 1,272 jobs and 41,502 dependency checks:
`/tmp/mcfta-native-active-20261014-audit.log`.
Only `propext`, `Classical.choice`, and `Quot.sound` are used.
No Haskell source changed. Prior Nix and formatter checks remain the source
validation checkpoint. All 1,515 original manifest files remain. Only the
five previously intended audit and coverage files differ. The marked drafts
and retained counterexample have their original bytes. All work remains local.
