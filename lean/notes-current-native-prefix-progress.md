# Verified checked query prefix bounds: 2026-10-29 20:57 CET

Source 20a4595247b497b1242707325ddf03dc101a92d4 on formalize.
Read lean/notes-current-checked-prefix-progress.md first.
The full formalization goal remains ACTIVE. Main 7b8db072f is integrated.
Earlier document bodies follow unchanged as dated checkpoints.

IncomingQuery.native_prefix_bounded now derives one finite Mu-body degree
ceiling for every actual checked native fuel from original caller admission.
Its finite completion trace is derived, not supplied as a new premise.
No sharp formula or global bound across successive rebased queries is proved.

Main PR193 now has an additive tuple-budget model with finite exploration,
conservative overflow, zero-charge entries, a completed literal fixed-point
loop and sound public True verdict under explicit source-interface laws.
The old conjunction-count resource models remain historical targets.
Physical lazy exposure and allocation bounds for PR193 remain open.

Strict checks pass for all 5 new modules and Audit: 4650 build jobs and 82182
theorem dependencies. Public output preserves the exact old prefix and adds
15 theorems. Nix core passes 384 examples; final Fourmolu/cabal-gild pass.
The two Haskell Haddock fixes include the overflow lookahead tuple. Runtime
code is unchanged locally. FINDINGS records both for external pickup.

Whole-system rendered soundness remains conditional on semantic/resource
contracts, fixed PCS and wholeDischarged. Global original-input resources,
nonterminal chosen-value coverage, ordering and Haskell correspondence remain
open. The detailed note gives the exact evidence and next proof targets.

---
# Current proof state: all-outcome native intersection body bounds

Checkpoint: 2026-10-29 20:30 CET. The full goal remains ACTIVE.
Source: `3f15b7e8127019e02c9b66893225a842e9edb059` on formalize.
Main ef0a2f32 remains integrated. Read this note before older checkpoints.

## Full objective and strongest system claim

The objective is an end-to-end proof of the constrained language generator.
It includes sound outputs, coverage of intended finite values, sufficient
resources and recursive capacity from original inputs, specified order and
stop behavior, and correspondence with the public Haskell implementation.
Keep the optimized interned core. Retain older constructor and equality work
as secondary targets. Preserve repairs, counterexamples and marked drafts.

The strongest whole-system semantic claim remains conditional checked
rendered soundness under semantic/resource contracts, fixed PCS and
whole-state Discharged. Greater recursive capacity retains ordered output
prefixes under the required budgets. The terminal chosen-model callback
retains the same original assignment. DONE does not imply Discharged.
A configured stop can emit partial results. Whole-language completeness is
open. The new bound is a local resource result in this larger objective.

Existing finite-capacity resource bounds retain the same old bound, outcome,
resources, all-extra stability and admitted histories. Outputs and concrete
Cached payloads in stopped diagnostics retain original recursion keys at the
same raw slot. Nested failures and no-output runs are included. Membership
retention supplies no strict global unfolding rank.

## Exact new result

Native below means SourceRecursiveIntersectionNative.execute. It is the Lean
interpreter with typed node/edge memo tables and source code continuations.
It is distinct from SourceEqualityNativeDemand.execute and from Haskell.

Let L be the original source body-degree ceiling. Let R be the original
request's least successful semantic fuel. Native.node_prefix_lower proves:

```text
forall runtimeFuel,
  Lower current.machine.heap (L + R)
    (Native.execute runtimeFuel (.node request .pure) current).state.machine.heap
```

Native.edge_prefix_lower proves the corresponding actual edge-call result.
The result has no successful return or chosen endpoint premise. It includes
yielded residual code, done values, explicit failure and every blocked reason.
Pending optional-binder construction retains its actual changed heap.
The proof does not equate native yielded exhaustion with kernel failed
exhaustion. No stopped native-to-kernel replay theorem is asserted.

Lower quantifies each complete Mu record at its actual key. Such a record
is either the exact complete record in the incoming heap, including its
payload, or its body's open-binder degree is strictly below L + R.
The result covers complete probe records in every reached heap. It gives
no bound on incomplete reservations or the number of records.
The degree is open stored-plan binder depth. It differs from Value.depth,
term height, enumeration rank and a global unfolding rank.

The original-input gates are source Facts, source Bounded L, NodeScope or
EdgeScope, and semantic Completes for that original request. Current-state
gates are strong Thunks.Valid, NodeReady or EdgeReady, source Grows and issued
history, SemanticHeap, and the body/probe open-depth invariant. WordRanges
checks request words along actual finite Steps. It already covers reached
prefixes; it is not a DONE-only or arbitrary future-state condition.

Neither final prefix theorem assumes a current-heap ceiling, a future body
bound, a future value bound, a future prefix supplier, Idle, ActiveAbove, a
completed native run, or an arbitrary family of future word ranges.
All recursive child and compiled-body suppliers are discharged internally.

Native.closed_roots_prefix_lower derives L and original semantic completion
from original available closed roots. It selects one bound before all runtime
fuel and all later heaps. Old complete records in a later incoming heap can
remain above this bound; the Lower conclusion keeps the exact-old alternative.

Native.closed_roots_cold_prefix_bounded fixes the incoming constructor heap
to the source. The original finite source inventory then supplies Bounded
for every complete Mu body in every finite native outcome. Cold fixes only
the constructor heap. It requires no empty native memo tables. Its bound
is original inventory maximumDepth + 1 + original semantic requiredFuel.
This is an existence theorem. It is not an executable capacity algorithm.

## Proof structure and checked source map

NativeBindLower proves execute_bind_state_cases for the complete native state,
including both memos. Every bound-code endpoint is an actual inner endpoint,
or an actual continuation endpoint after a literal completed inner call.
No same-runtime inequality is assumed. execute_bind_lower composes the same
Lower bound through those exact endpoints, including incomplete outcomes.

NativePrimitiveLower covers pure, failure, native memo completion, ordinary
no-new-Mu work and optionalBinder. The optional-binder site includes pending
construction. Its local body-degree premise is derived in the Mu producer.
NativeReturnDegreeFacts packages actual completed-child validity, exact
Extension, availability, both heap invariants and the old closed degree bound.

NativeWalkLower derives each actual call's ranges with before_bind. A literal
completed child derives the actual tail ranges with after_body. Earlier
constructor effects remain when a later child stops. NativeUnionPrefixLower,
NativeRowsPrefixLower and NativeEdgePrefixLower discharge walk preservation
from actual child returns. Their exact makeUnion/makeNode/makeEdge jobs add
no complete Mu records. The original row and zip order is retained.

NativeMuPrefixLower derives the actual entered child's original scope and
strictly smaller semantic rank. The actual completed child's degree pays
for MaybeMu.lower's body-degree-plus-one bound. No original-input future
body inequality remains. Stopped children retain their own reached heaps.

NativeRequestPrefixLower covers direct selection, memo evaluation, ready,
busy and absent cases. It derives checked word/key facts at the actual node
or edge instruction. Actual started_source gives the same request, strong
current validity and unchanged source machine. It composes the compiled
body with literal finishNode/finishEdge instructions. These instructions
change memos and preserve the constructor heap. The existing Code.Safe and
Code.Below remain False on finish frames. No runtime definition is changed.

NativeNodePrefixLower covers every compiled physical node branch. It uses
original bindings at actual read instructions and exact source child bounds.
NativePrefixLower closes both request kinds by simultaneous strong induction
on original semantic requiredFuel. NativeClosedPrefixLower derives the two
closed-root statements. The final API has no local supplier premise.

All 12 module files and Audit have exact final strict SHA mappings in
final-check-map.json. Source-only candidate reports keep their historical
UNTESTED labels. Bind, walk, edge and request candidates were installed
unchanged and strictly checked. Their reports are distinct from Root checks.
The task scopes record zero, one and eight whole repository source reviews
for bind, walk/edge and request respectively. Other reads are retained cuts.
The later generator-query audit records three whole source acquisitions,
46 exact cuts/reads and 39 source identities. It makes no compilation claim.

## Biggest remaining gap

The actual IncomingNode.run calls SourceEqualityNativeDemand.execute at its
captured entry state. That engine has an edgeBody control before child code.
It performs field lookup, checked conjunction allocation, rejection or
sentinel handling, and retains operations caches on every outcome.
The plain native bound does not transfer to that engine by definition.

The distinction also affects memo validity. The checked physical cache needs
Available/EdgeResident at completed cells. Bare Thunks.Valid requires eager
Kernel Produced receipts. Checked closed receipts retain actual checked
NodeProduced provenance. They are not the eager receipts. A direct cast or
substitution would add an unproved assumption.

Inventory.query_complete rebases the source to each actual query-entry heap
and appends the queried operands. generated_complete reconstructs original
syntax in that rebased source. These local receipts do not make generated
operands Available in one fixed original source. Same-slot ancestry gives
recursion-key membership; it does not give physical operand scope or a
strict global measure. The source audit is a specification, not a checked
transfer theorem. Its report and exact proposed target are in the archive.

The next exact proposed caller statement is IncomingQuery.native_prefix_bounded.
It retains the actual entry Context, current Available and closed operands,
and original Fits and Room. It chooses one Bounded ceiling before every
nativeFuel and observes the literal Demand.execute outcome heap. It requires
no successful return or future bound. This is UNPROVED and UNTESTED.

Good derives entry Facts. Current Available plus closed derives Original,
initial_scope and initial_complete in this same entry source. Ready already
derives SemanticHeap and OpenHeap. Fits, Room and actual PendingRealized
supply checked initial ranges at incoming/dispatch calls. Physical operand
scope per query is therefore already derived. It is not a missing supplier.
Actual within-query scope lemmas also exist for reached node and edgeBody
controls. New checked memo cells still need degree facts derived from their
own actual executions. Warm entry cells use the literal entry inventory.
Target, seeded and shared target workers use the same checked backend.

Next prove this checked all-outcome bound. Then bound all rebased query-entry
ceilings by one measure from the generator startup data. Do not add a future
body/rank family as an original input premise.
Per-query body bounds still do not bound allocation cardinality, guard growth,
fresh handles, word ranges or pending keys. One global progress/resource
argument and original-input sufficient recursive capacity remain open.
Nonterminal chosen-value coverage, full policy/origin/public API admission
and physical optimized Haskell correspondence also remain open.
No completion percentage or whole-library termination claim is supported.

## Validation and retained failures

Twelve additive proof modules: 22 public theorems, 1238 lines and 90220 bytes.
No runtime definition or exported predicate is added. All 13 final sources,
including Audit, pass warningAsError and all linters. Audit checks 82156
theorem dependencies in 4645 jobs. Only propext, Classical.choice and
Quot.sound are permitted. No placeholder, native_decide or suppression is
added. Default Audit replays the known imported unused-variable warning;
its strict source check passes. The warning was not suppressed or repaired.

There are 34 completed compiler commands: 27 PASS and seven failures.
All jobs ran serially under measured 4 GiB max/high and zero swap with a
five-minute cap. All 303 command input snapshots match their hashes.
The seven failure directories and exact attempted sources remain. They cover
Mu rank/heap aliases, row namespace and compiler arguments, unsupported and
Boolean branch reduction, a repeated failed node dependency, and the Lean
strong recursion name/alternative. These are retained development attempts.
All final source versions strictly pass.

Public readback has 912 checks/axiom lists and 73 old definition bodies.
It has 3751130 bytes, SHA256
`a1585153cadb445cd442b184e83fd2e908bbfd96b88eeb1ebf8f6b56040309cb`.
The prior 3691779 bytes are an exact prefix. All 59351 new bytes were read
in contiguous ranges. Every public final prefix statement has its actual
original contracts and no hidden child/body supplier.

All 4632 old non-Audit Lean, 461 stronger-source and 829 Haskell/Cabal
identities match. Audit changes only by additive imports. Earlier sealed
evidence areas match their original payload hashes. All 27 older current
document bodies remain exact suffixes below a new dated header.
No Haskell source change or native Haskell job occurs in this increment.

## Haskell findings for external pickup

FINDINGS retains serialization repair
`c15021ce706ef560b6c0ab335ceed1a4b67ba4aa` on formalize. Main ef0a2f32 lacks it.
The exact checkedPathClass helper, both parser call sites, four strict-prefix
malformed fixtures and lawful codec are preserved. The helper rejects invalid
path classes before PathEClass can throw. The earlier native evidence proves
the four invalid inputs return Left and valid controls return graphs.
No new Haskell defect or repair is claimed here. The earlier main integration
passed 383 core, 56 serialization and 30 Sized/checkpoint examples. Those runs
were not repeated for these proof-only additions. Preserve the HugeLists
import fix, optimized interned operations, probe-freshness repair and exact
counterexample scopes. Old source claims remain dated checkpoints.

## Restart and publication

Proof commits are 19faf48feaeb4e99c2adc50f2ec0226e6f2b6440,
7b29b567ec7c8ce4869b84a60836dec195d4fd6b and
3f15b7e8127019e02c9b66893225a842e9edb059. All source proofs are committed. The full goal remains ACTIVE.
Regular pushes to git@github.com:TharkunAB/cfta.git refs/heads/formalize remain
authorized. Source and docs commits precede the unfiltered evidence archive.

Evidence is lean/restart-evidence/20261029-native-prefix-progress/. It includes
all command logs, failed attempts, exact inputs, final sources and public
readback, candidate reports, source-scope provenance, and the next source audit.
The standard-library verifier checks every archived regular file and can
reconstruct the complete sealed tree in a fresh destination. Keep old and
reconstructed areas immutable. Continue in a new writable area after sealing.
Read this note and the latest shared board status before difficult work.
Refresh upstream, preserve local work, and continue the actual checked-engine
prefix bound and generated-query lineage. Do not pause at this checkpoint.
