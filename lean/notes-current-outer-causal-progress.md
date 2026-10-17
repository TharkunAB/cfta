# Class dependencies, copied children, and persistent native writers

Starting checkpoint: dd193cce. Proof commit: d16b63a3.
Source main remains c0cc8a05, merged at 896b0a1c.
The whole-library goal remains active.

## Target and largest gap

For each public operation P, prove:

`Valid(input) ∧ Supported_P(input, initialResources) ⇒ runHaskell(P, input) terminates with result ∧ Spec_P(input, result)`.

Support must describe initial data and resource limits. It must not assume
successful completion. Specifications include errors and validation order.
The complete public Haskell theorem remains open.

The largest mathematical gap is general recursive outer progress and
repeated-pass convergence. Actual inherited normalization and descent now
have their required local invariants. Nonempty local constraints can copy
constrained subtrees deeper into a returned child. A global proof must
account for those source occurrences and exclude every active ancestor
key. Ordinary tree height and a maximum constrained-depth count fail.

## Exact class dependency through child descent

SourceCurrentEqualityDependencyDescent.retained starts with one well-formed
payload that is a fixed point of actual normalization. If a class survives
the selected child descent, each class on which it has a strict-prefix
dependency survives too. The theorem constructs the actual dependent child
record and proves membership in the actual sorted result list.

subsumes_iff proves exact dependency equivalence for two retained child
records. Congruence closure supplies one uniform nonempty suffix. Two
distinct retained source paths force the dependent trie to retain two
distinct paths. This derives retention; it does not assume it for that
dependent class.

The positive constructed test has its parent dependency witness outside
the selected child index. Saturation still forces the dependency inside
the selected child. A second test has consistent, well-formed records but
no normalization fixed point. Its retained children lose the dependency.
The fixed-point premise is necessary in this generality. The previous
actual prefix and normalization results supply that premise.

This order belongs to one payload. It does not order occurrences from
different source fields or rank the full outer execution.

## A copied constrained child can require fresh work

SourceCurrentOuterCopiedCold constructs B = pair(leaf,leaf) with its own
class [0]=[1]. It constructs plain productive tau = mu x.(leaf | pair(x,x)).
The root children are [tau,B], with class [0,0]=[1].

The literal parent worker copies B into the first returned wrapper. The
outer walk reaches that copy before it visits the original second sibling.
An exact Reached prefix goes from the root call at fuel 24 to the copied
call at fuel 18. At that caller, the copied key is absent. The root and
wrapper owners still evaluate at handles 0 and 1. Actual demand allocates
handle 2 and starts the copied request. Its inherited payload is empty.

The copied call completes. The full root call also completes. The final
cell at handle 2 contains the returned B, and another demand is an exact
warm hit. Thus the example rejects a universal ready-copy shortcut. It is
not a nontermination example.

The proof also excludes a RequiredRowOrigins.Origin from tau alone to the
copied B. Tau is plain; B retains a nonplain guard. The pending sibling
source dependency must remain in any global provenance argument.

## Native writer provenance across persistent queries

SourceCurrentNativeEdgeWriterHistory.History starts with empty native memo
tables. It extends through actual completed checked traces and the exact
advancePhysical operation. The latter retains the entire edge-cell
function. No desired guard law or prior Writer predicate is an input to
this history producer.

History.writers derives an actual earlier body and finish for each returned
edge cell. History.query extends the history with a completed node query.
History.request recovers the writer for a literal edge call. It handles
both a cold evaluation and a ready hit. Actual lookup and demand checks
identify the complete request with its captured owner.

History.rows connects each surviving compileRows output to indexed left
and right input rows and their actual earlier writer. It derives the exact
full guard conjunction and symbol. The existing Writer.live theorem also
provides the ordered child-call trace. The proof constructs the history
at each selected call from its actual completed walk prefix.

These are provenance results for past execution. They do not construct
future completion. advancePhysical supplies no heap-growth or Good fact.
The writer witness is indexed by request and result, not the current cell
handle. A global occurrence proof still needs to connect each writer's
heap with the actual enclosing history.

## Effective own equalities are not the complete guard origin

SourceCurrentNativeOwnOriginBoundary.accepted_join gives literal guards
whose actual conjunction passes the two-child structural check. The left
raw equality field contains [0]=[1], but its separate effective accessor
returns contradiction because its guard is Same [0] [0,0]. The right raw
field is empty and its guard is Not Top. Its effective accessor is empty.

The joined residual conjunction is outside positive extraction. Its
effective accessor retains the nonempty raw class [0]=[1]. Thus a live
nonempty joined own payload need not have a live nonempty operand own
payload. Track full raw fields and guard syntax when tracing origins.

This is an accepted-constructor boundary. It does not establish a complete
native execution or a Haskell defect. The full guard remains contradictory.
Haskell conjoinConstraints combines stored equality fields and full guards
separately, as the model does.

## Remaining work and Haskell handoff

Connect original field occurrences, class dependencies, actual native
products, and complete physical request keys. A decreasing historical
label alone cannot exclude a busy alias. Then complete nonempty live
child walks, ordered rows, ordinary node bodies, and the general mutual
outer pass. Repeated-pass convergence is a separate obligation.

Retained-Mu writer correspondence, smart cleanup, frontend and runtime
adapters, and complete public pipeline correspondence remain open.
Read notes-proof-status-20261017.md for the complete proof map.

No Haskell behavior patch or new production defect is added. Field-pool
repair b9219b9e remains merged and validated in source c0cc8a05. FINDINGS
keeps the external repair registry first. Each later repair must record its
failure, executable reproducer, paths, commit, checks, and upstream status.
All earlier proofs, counterexamples, repairs, drafts, evidence, stashes,
other worktrees, and optimized interned code remain preserved.

## Validation

All four final strict source logs are empty. All four canonical targets
pass. Full Audit passes 3137 jobs and 68963 dependency checks under verified
4 GiB maximum, 4 GiB high, zero swap, and 381 MiB peak memory. Twelve public
checks and four constructed checks pass in seven groups. They permit only
propext, Classical.choice, and Quot.sound. Three component manifests verify
245 entries. Evidence is in restart-evidence/20261017-outer-causal-progress/.

The first copied-case proof output failed in the pretty printer despite
successful kernel checking. The earlier output checker missed that message.
The new checker rejects it. The final public theorem refers to a private
witness. Byte comparison confirms the same public statement and the same
witness proof body. Strict, canonical, public, constructed, and full Audit
checks pass after this change. Failed and interrupted printer attempts
remain unselected and retain their bytes. No cause is inferred for the
interrupted attempts. The preceding checkpoint's fourteen selected output
groups have no printer-failure text.
