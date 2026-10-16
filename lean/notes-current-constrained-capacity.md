# Numeric query-entry capacity and constructor reservation counts

Updated: 2026-10-16. Audited source main is `c0cc8a05`, merged at
`896b0a1c`. This checkpoint starts at published `a86c09dd`.
Root FINDINGS.md keeps the external Haskell repair handoff first.
No Haskell file changes.

## Full objective

Prove correspondence between the intended constrained tree languages and
generators and the current Haskell implementation. Retain separate language,
termination, transformations, exact size classes, counts, enumeration order,
both rank inverses, probability, frontend, runtime, and pipeline contracts.
There is no completed whole-library theorem. Read
notes-current-constrained-query-words.md for the current proof map.

The finite ordinary domain admits arbitrary guards, equality classes, and
unequal path lengths. It excludes Mu, references, and explicit unions.
The older plain Region is a separate proof domain. Preserve the optimized
interned core and all older constructor and equality proofs.

## Numeric plans at actual entries

`Capacity` contains only two inequalities on the current node and edge
supplies. At width `bits+2`, they are `nodes.next <= 2^bits` and
`edges.next <= 2^(bits+2)`. Initial physical validity, resident operands,
and finite ordinary domains derive the recursive original-key bounds and
all actual native word checks. Capacity contains no readiness, execution,
completion, or semantic result condition.
These are modeled packed-key bounds. They do not establish a concrete
signed Haskell allocation-counter bound.

`TargetCapacity` follows the actual first-seeded right fold. Its head
operand runs before its recursive tail. The current query starts at that
tail's exact return. Induction on the shorter path list derives the tail
ranges before verifying the earlier completed tail. This supplies current
readiness, domains, and structural certificates before the current query.
The public finite endpoint constructs its own Target, reads, full receipt,
native and merge certificates, and output domain.

`SharedCapacity` selects a target plan only for an absent slot. A leaf
requires numeric capacity at the exact earlier force return. The force
receipt derives the current target domain and transports input residency.
Present slots retain the actual existing state and target. Native tables,
equality operations, the merge memo, and other slots remain warm.

`EditCapacity` follows selected children, all rows, and literal constructor
rebuilds. Initial domains exclude the recursive-head branch. The first
selected edit's ranges are derived before constructing that prefix.
Stable worker uniqueness aligns an arbitrary earlier raw prefix with the
constructed prefix at the same result and whole shared state. The prefix
reads then derive the suffix's readiness, globals, and structural tables.
No completed enclosing edit is needed to obtain its own ranges.

`ClassCapacity` uses the literal compiled edits and captured entry forest.
Only local target slots start empty. `PassCapacity` processes the actual
tail classes before the head. Shorter-tail induction derives its own ranges
before verifying the earlier tail return. Repeated classes and paths retain
their source order.

`StageCapacity` contains only the pass plan selected after an earlier
actual Scan, positional Retained proof, and literal required-worker return.
The finite ordinary Scan derives its own range checks and unchanged state.
Required execution derives its current domain, availability, readiness,
inventory, and global validity before the pass begins.

`LocalCapacity` enters that stage only after the actual live precheck.
The original field and inherited equality readiness derive the normalized
records and their trie facts. The precheck retains the same native machine.
`ParentCapacity` selects only a live original field. Raw rejection has no
local capacity obligation. `CallCapacity` selects the actual captured
evaluating owner before its parent body starts. Initial caller facts derive
that owner's domain and readiness. The finite endpoint constructs the full
outer edge call, strict reads, Checks, Post, structural bound, language law,
and stable literal worker return from numeric entry plans.

## Reservation arithmetic

`Reservations.observe` follows literal Work requests and their actual
initial cache lookups. Exact counter equations count misses. Request counts
give upper bounds. A hit uses no new identity. One evaluated-record
makeNode action reserves at most one node identity. makeEdge reserves at
most one edge identity. These actions do not consume the other supply.

`AtomicTrace` follows actual reserve and install actions. Installation does
not refund a reservation. A losing candidate still consumes its reservation
and remains in the issued history. Two candidates for one key can therefore
consume two identities while publishing one canonical entry.

`QueryReservations` follows raw actual yielded native prefixes. It observes
the literal Work request list at each instruction. Body equality operations,
memo lookup, demand, and finish consume no node or edge identity immediately.
The ordinary code certificate excludes optional binder construction.
Exact prefix equations and request-count upper bounds require no completed
physical receipt or successful query.

The resulting `capacity_after` theorem still takes a bound on the actual
prefix request count. That count is not a difference of final and initial
counters. It is also not yet a static total-work bound derived from the
initial input. Equality-interner capacity is separate from these two counters.

## Static initial construction bounds

`ConstructionReservations` counts ordinary source node and row occurrences,
including all repeated nested child syntax. Empty and variable syntax cost
zero. On the finite ordinary source domain, `complete` constructs the actual
successful build from any initial heap and environment. Both returned
counters are at most the initial counter plus the corresponding syntax
count. This arithmetic completion needs no initial record-validity or
result-domain assumption. Legitimate resident environments add the result
domain, heap Facts, and availability at that same return.

The closed endpoint constructs its own root from Empty. Its absolute supply
bounds depend only on input syntax. A duplicate row can reserve fewer
identities than its occurrence count. `InitialCapacity.constructed/prepared`
combine those bounds with actual field preparation and full initial caller
admission. They derive initial Capacity when the static syntax counts fit.
They construct their own source return, Context, structural certificates,
actual empty inherited identity, availability, and domain. This is an
initial-resource bound for construction. Later reduction entries remain
subject to their own numeric plans.

## Remaining whole-root obligation

The older constructed finite ordinary root still takes
`OuterEntries.Plan`. That plan quantifies all independently reached raw
parent entries. Numeric capacity alone does not derive the Context,
residency, domain, and causal tables at every such entry. The new outer
edge endpoint derives its own current owner facts from an admitted caller;
it does not establish that global reachable-entry admission theorem.

Next prove admission through the actual Reach relation and earlier raw
prefixes. Derive or construct and align those earlier reads before using
their result invariants. Then lift the numeric parent plan to the full root.
Do not supply future readiness or a completed enclosing root as the missing
admission premise. Bound generated Target, merge, leaf, and constructor
actions from initial resources to discharge the numeric plans themselves.

Haskell supplies can be shared across types and callers. A host mkNode can
force deferred child computations. The primitive Work bound covers the
constructor's own evaluated-record action. Count those additional host
actions or retain an explicit process-history assumption. General
Mu/reference/union progress, repeated-pass convergence, current frontend
adapters, concrete runtime, and full-pipeline composition remain open.

Read next-capacity-lifting-review.md and outer-capacity-next-review.md in
lean/restart-evidence/20261016-constrained-query-capacity/.
The full-library goal remains active.

## Haskell handoff

This checkpoint adds no Haskell behavior change. The recursive field-pool
repair `b9219b9e` is already merged by PR #65 and validated. Root FINDINGS.md
records its failure, executable reproducer, affected paths, commit, checks,
and upstream status. Record every later Haskell repair there before the
historical reports. Reuse unchanged source validation: strict Nix build,
798 examples plus golden, six-file Fourmolu, and four-package Cabal-gild and
metadata checks.

## Validation and preservation

Pinned Lean 4.34.1 passes the full Audit: 2551 jobs and 59587 dependency
checks. All 88 declared public axiom/full-signature pairs pass. The coverage
includes indented mutual declarations and noncomputable definitions.
Thirty-nine imported integration pairs check actual prior prefixes, warm
slot reuse, complete captured owners, losing atomic candidates, static
construction budgets, source-derived initial keys, and prepared admission.
The initial-query kernel composes static source counts with a complete
exact native query at the same admitted initial state. Only `propext`,
`Classical.choice`, and `Quot.sound` occur. Final selected probe logs contain
no warning or placeholder. Canonical logs retain the historical unused-input
dependency warning.

Preservation retains 6528 starting files and 2537 older non-Audit proof
sources, apart from the seven named restart authorities and additive Audit
imports. Thirty-eight frozen manifests check 308 module entries. Older
counterexamples, repairs, drafts, stashes, other worktrees, and the optimized
interned core remain. Evidence is in
lean/restart-evidence/20261016-constrained-query-capacity/.
