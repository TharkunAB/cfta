# Selected ordinary alternatives and pending references

## Current result

Selection: `9f3674ba1`.
Ordinary alternatives: `519d62a80`.
Main remains `153e1a211b56dd78bd22f6b427fb78e673041d55`.
The whole formalization goal stays ACTIVE.

Actual pure selection now derives incoming reference avoidance at its input
cache. Actual ordinary entry transports this fact and the initial global
pending-reference history. Every processed alternative then retains global
pending-reference history at its own returned cache and reached native heap.
The new selected completion theorem derives local pending inputs too.
It does not require the caller to supply Ready, InputsPending or IncomingAvoid.

The old completion theorems gain output implications. Their admission inputs
and numeric Ranges conditions do not change. No runtime worker body changes.
The only new definition is the logical predicate for per-receipt history.

## Selection at the same cache

`Selection.unblocked_incoming` lifts the existing per-bucket avoidance theorem
over every stored value. Exact canonical waiting counts and actual root paths
make an unblocked root distinct from every stored suspended reference class.
Eliminated and enumerated values contain no stored suspended references.

`Selection.incoming` uses actual native flags, Safe, root paths, exact waiting
counts and the actual pure selection equation. It derives IncomingAvoid at
that same input cache. It does not transport a stale selection across a write.
The existing ready and realized selection contracts stay unchanged.

## Each alternative retains its own history

`NativeBranchCompletion.Pending` checks PendingReferences at the cache of a
complete receipt, an arity rejection, or a valid raw-empty child rejection.
The unhandled constructor has no cache. Its predicate is True, but admitted
completion never includes it among processed receipts.

Branch completion now turns initial PendingReferences and IncomingAvoid into
Pending for every processed receipt. Captured completion supplies the
supported case. Arity rejection returns the input cache. Unsupported
preparation stops explicitly before a processed receipt is added.

Each alternative starts with the identical original enumeration cache.
Actual native caller and query effects advance between alternatives.
The history proof follows those same witnesses. It does not merge branch
caches or move an old receipt to the final native heap. Valid child rejection
retains pending history without an unconditional final Safe assertion.

## Actual entry and selected completion

`NativeOrdinary.complete` transports the two initial reference conditions
through actual entry's RenderStable receipt. It then uses branch completion
on the framed entry cache. It retains its old inputs and actual run equation.

`NativeOrdinary.selected_complete` derives Ready and IncomingAvoid from
selection. Initial global history and the actual stored pending-slot equation
derive InputsPending. The theorem calls ordinary completion once and returns
unconditional Pending for all processed receipts. It also retains the full
actual entry receipt, common sufficient finite bounds, index equality,
native Post, query equality and all existing admission certificates.

The decoded parent must be ordinary. Its bucket must have no terminal trie.
The supplied edge callback must select stored edges. It need not select every
stored edge. Supported annotations complete the ordered scan, including valid
rejections. This does not imply that the result contains an accepted term.
Numeric Ranges admission remains explicit. Initial-only admission stays open.

## Actual driver boundary

The selected theorem has no narrowing or callback between selection and entry.
The Haskell driver has both. Enumeration.hs:968 to 1004 selects a variable,
reads its value, runs narrow, may replace its pending node, and calls the
Right oracle before enumerateOutUVarWith at line 976. The ordered driver
also accepts an oracle result before a later activation refresh and raw step.

The next proof must retain history at these actual reached states.
Action.prepare_pending_complete already exposes native narrowing and the
actual changed-handle write. That write keeps the suspended bucket.
Use these receipts and native Keeps facts. Do not replace the native operation
with an identity callback assumption. A callback that permits representative
compression needs an actual preservation contract. The old ReadOnlyOracle
contract requires exact state equality and is stronger than that behavior.
Arbitrary EnumerateM callbacks do not automatically preserve the conditions.

This is an open correspondence boundary. No new Haskell defect or repair is
identified. Root FINDINGS retains all external Haskell repair information.

## Verification

All three changed modules pass Lean 4.34.1 with all linters and warnings as
errors on their first strict attempts. The installed selection and branch
build passes. The aggregate Audit passes with 3749 jobs and 76712 theorem
dependencies. The older unused inputs warning remains unchanged.

Installed public readback checks nine declarations. The full output has
319 lines and 22212 bytes. Its SHA-256 is
`0a19e888c16d48dd03b119c1474631778eb2d6bbfcd0dde4db6126118031778f`.
All reported axiom sets are subsets of propext, Classical.choice and Quot.sound.
No compiler attempt fails in this checkpoint. The evidence preparation first
compares a following variable declaration as part of an old definition.
That assertion fails after copying the evidence. The corrected declaration
boundary check passes. No proof source changes in response to this assertion.
All six checks run serially under 4 GiB heavy-management caps with no swap.
Actual compiler inputs, full raw logs, reports, cap records, final sources
and the proof patch remain in restart-evidence/20261025-selected-reference-receipts.
Haskell runtime, all old worker bodies, prior native reference producers,
SelectedEntry and H6 stay unchanged. No Haskell suite repeats.

## Strongest claim and remaining work

H6 remains the strongest end-to-end language theorem. Covered closed
construction, a valid initial cache and original allocation history, and
prescribed finite budgets and modeled node-call rounds derive sufficient
finite bounds and a mathematical width chosen after construction.
With empty inherited payload, the final available value has exactly the
original finite-tree language under the formal formula and entailment
interfaces. The theorem does not cover the whole typing or pruning driver.

The pruning result now connects actual same-cache pure selection to per-branch
pending-reference preservation through covered ordinary expansion.
These predicates inspect stored suspended references. They do not prove
fragment-hole history, fragment acyclicity or successful extraction.
Those proofs, narrowing and oracle preservation, terminal parents, parent
normalization, successful receipt semantics and whole-driver language
preservation remain open. Arbitrary Haskell demand, full raw-stream erasure,
concrete solvers and physical runtime correspondence also remain open.
No practical resource or convergence bound follows.
