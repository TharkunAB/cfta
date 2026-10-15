# Seeded refused-class queries and their input domain

Source main remains `525d722e`. The query-demand proof is `e36ecf90`.
The seeded query and domain-boundary proof is `38569b85`. Both are pushed.
The [completed task-table proof](notes-source-emptiness-task-soundness.md)
supplies the finite emptiness result. This work connects that result to the
caller's distinct seeded intersection and weakens its closedness premise.
General caller correspondence remains open.

## Query demand

`SourceEmptinessDecision.Decision` keeps the source query branches separate.
An empty query returns true without exploration or fixed-point work. A
missing key returns false after exploration without fixed-point work. A
present key reads the completed equality-stop result. Each branch retains
the actual native input and returned state. A fresh local task scope retains
the surrounding native caches.

`empty_no_work` proves the immediate result and unchanged native state.
`explored` derives a finite decision for a closed nonempty query once its
actual exploration completes. `effects` retains readiness, physical history,
and normalized fields. `sound` excludes every accepted term when the decision
is true. These statements do not prove exploration completion or exact GHC
evaluation of the row spine.

## Selected projection domain

`SourceEmptinessProjectionLocal` retains the earlier improvement that only
the selected top child must be closed. Its finite projection theorem and all
other proofs remain. A stronger domain is needed when that selected child
has an unrelated open sibling deeper inside it.

`SourceEqualityProjectionPathDomain` follows each signed index through
ordinary nodes. Each selected leaf must be closed. Unvisited ordinary
siblings may remain open at several depths. Every selected row branch has
the same requirement. Root union still requires every operand closed.
Mu and union heads retain the existing whole-value closedness boundary.

Mutual induction on actual projection and row graphs derives heap effects,
closed resident results, accepted-subtree inclusion, and physical annotation
preservation. The domain contains no final-output language assertion. It has
no heap parameter. Actual operand wrappers retain the native domain cache
and both native memo tables.

`SourceEmptinessClassFoldLocal` passes this domain through both foldr1 and
seeded schedules. It derives closed available results and common accepted
subtree inclusion at their actual returned states. It also derives normalized
query fields through the actual projections and native requests. The original
forests and all earlier values remain resident through physical history.

## Refuted classes

`SourceRefusedClassQuery.class_witness` uses the actual seeded result. An
accepted original forest and a satisfied active class supply a common
strictly smaller subtree accepted by that result. The caller rotates its
first projection to the seed position of the right fold. This is distinct
from the row analysis foldr1 schedule.

`refutes` combines that witness with a completed task-table decision at the
actual returned native state. `refutes_decision` includes the query's demand
shortcuts. A true query decision refutes satisfaction of the original class
by every accepted forest in the stated projection domain. Initial native
readiness, available original values, normalized fields, and the syntactic
path domain remain explicit. No sound-oracle premise is supplied.

## Checked caller boundaries

`SourceRefusedClassDomainBoundary` uses actual constructor computations in an
open environment. Both initial fixtures have an active class, a true primary
gate, a false secondary gate, and closed visited endpoints. The first has an
unrelated open top child. The second has an open selected top child because
its unvisited sibling holds the free reference. The stronger ordinary-path
domain admits both actual fixtures. Thus neither whole-forest closedness nor
selected-top-child closedness is a valid consequence of the secondary gate.

A third actual fixture enters an open unconstrained Mu, selects its closed
first child, and ignores a recursive sibling and an external-reference
sibling. A second original endpoint contains a constrained Mu. The primary
class gate returns true. The secondary gate returns false. Both gate receipts
retain their exact returned heap after unfolding. The current conservative
path domain fails at the open Mu head. `open_mu_boundary` proves this failure.
Thus the new domain also cannot be inferred from a false secondary gate.
The sequential secondary call starts from the actual primary result heap.
It returns false and preserves that exact heap, including its cached records.

These are proof-domain counterexamples. They are not counterexamples to
emptiness soundness. They assert no whole-source ready cache or completed
native caller execution for the open constructor environment.

## Remaining proof work

General gate-to-domain correspondence and open recursive-head exposure remain
open. The third fixture gives a concrete next case. Derive an open-head
projection leaf from actual unfolding, actual
nodeEdges, and ordinary reconstruction. Preserve available records, semantic
heaps, normalized fields, and the exact returned constructor cache. Existing
open stored-unfolding language and completion theorems can supply component
facts. Do not assume an open recursive input is closed.

Then compose the ordered primary partition, secondary scan, query, selected
fallback, and caller. Retain both gate modes and all three memo families.
Model progressive lazy row demand and original child forcing. Transfer native
leaves to checked allocation. Derive machine ranges, identity adequacy, and
general native, exploration, and whole-caller completion.

Representative waiting counts, template exclusion, other APIs and runtime
bridges, recursive constructors and generators, decoders, and extraction
remain separate targets. Preserve the optimized interned core, older proofs,
all repros and drafts, and each distinct exact Sized contract.

## Validation and preservation

The full pinned Lean audit passes 2,027 jobs and 51,762 dependency checks.
Only propext, Classical.choice, and Quot.sound occur. No new warning occurs.
Log: `/tmp/mcfta-refused-query-status-audit-20261015.log`.
Prior Lean definitions remain byte-identical except two additive Audit
imports. All four Haskell package trees match `2652fc98`. Their unchanged
checks were not repeated.

Starting snapshot: `/tmp/mcfta-seeded-query-start-20261015-1837/`
(2,684 files). Closing snapshot:
`/tmp/mcfta-refused-query-checkpoint-20261015-1853/` (2,691 files).
Script: `/tmp/mcfta-preserve-refused-query-20261015.py`.
All prior repros, marked drafts, external drafts, stashes, and other worktrees
remain. The open Mu probe is retained as
`/tmp/mcfta-refused-open-mu-domain-probe-20261015.lean`.
