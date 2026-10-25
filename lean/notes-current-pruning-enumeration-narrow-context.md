# Caller and indexed caches from one native narrowing result

## Current result

Caller and memo preservation: `d677fd77b`.
Combined narrowing producer and Audit import: `6e83025d8`.
Main remains `153e1a211b56dd78bd22f6b427fb78e673041d55`.
The whole formalization goal stays ACTIVE.

One actual native narrowing result now derives the full checked Caller Post,
valid saved global memos and indexed enumeration cache at the same result
heap. The initial inputs include the genuine full Caller Context, enumeration
invariants and an actual initial value-read receipt. The combined theorem does
not require a final Context, final cache invariant or successful narrowing run.
No old producer contract or runtime worker body changes.

## Actual exposure and filtered construction

NativeContext.narrowAt_post first consumes an actual completed narrowAt
equation. It extracts that equation's exact nodeEdges exposure and the exact
makeNode call on its filtered rows. It derives physical heap effects from the
actual exposure and filtered constructor. It retains the equality-operation
state, checked request tables, domain cache, result tables, fourth cache and
merge cache through the existing literal advance operation.

The physical effects derive all required validity and soundness facts at that
advanced Caller. The proof also derives probe validity from the actual read
and constructor. The initial inventory remains valid at the reached heap.
A heap Keeps receipt alone would not establish these facts.

exposure_memos uses the same exposure fuel, input value and initial heap.
It produces valid saved global memos at the exposed heap, unfolding-table
extension and unchanged query tables. Constructor growth retains their
validity at the filtered constructor's actual heap. The proof does not use
head_memos, because that operation rebuilds all exposed rows.

The returned Post retains native effects even for an Empty result. The
separate enumeration action then rejects Empty without a successful final
enumeration state. Effects reached before rejection remain in the Caller.

NativeContext.outer_post handles the source's Mu and type skips by deriving
the unchanged value and heap from the actual result equation. Reflexive Post
then retains the original memos. Every other value case uses narrowAt_post.
This helper proves preservation from a completed run. It does not prove
completion on its own.

## One completion producer and one set of witnesses

NarrowContext.complete calls NarrowCache.complete once. The initial full
Caller Context supplies native readiness. The initial actual value-read
receipt identifies an old stored pending slot. Initial PendingRealized
supplies that slot's available closed value. Its decoding equation identifies
it with the exact oldValue returned by NarrowCache.complete.

The proof passes that producer's exact native fuel, result and heap to
NativeContext.outer_post. It then returns the derived Post and memos beside
the original cache packet. It does not choose another result or heap.

Empty retains its actual rejecting action. An equal handle retains the
framed read cache. A changed handle retains its actual representative reread,
plain setValue endpoint and indexed native write with gained=scs and lost=scs.
Each nonempty result retains Ready, paths, realization, the new stored-slot
equation, exact waiting counts and all native expandable flags. Waiting-map
identity and conditional pending and incoming history remain attached to
that same final cache and native heap.

The native result and heap are stable at every larger native fuel. Saved
memos belong to the chosen concrete exposure fuel. The theorem does not prove
that saved memo tables are identical across all larger fuels.

## Verification and approaches retained

Both new proof modules and the changed Audit import pass Lean 4.34.1 with
all linters and warnings as errors. Eight strict attempts are retained.
Five fail. The first caller proof attempt needs the already rewritten
exposure goal and the correct orientation of Mu result equalities. The next
needs removal of an unused typeclass input and explicit skipped-call inputs.
The third needs the fallback value argument made explicit. The fourth needs
list membership and unused simp arguments corrected. The fifth passes.
The combined producer's first attempt needs the native State type qualified.
Its second attempt passes. The strict Audit import check passes too.

The installed caller helper build passes with 1260 jobs. The aggregate Audit
passes with 3754 jobs and 76724 theorem dependencies. Installed public readback
checks six declarations. Its full output has 306 lines and 23457 bytes.
Its SHA-256 is
`d065be2e61db76316390f1de14199e73dafbfc85e1a92e6e79a41c2077d8a600`.
Every axiom set is a subset of propext, Classical.choice and Quot.sound.
The older unused inputs warning remains unchanged. All eleven checks run
serially under 4 GiB heavy-management caps with no swap.

All attempted compiler inputs, full raw logs, reports, final sources, cap
records and the proof patch remain in
restart-evidence/20261025-native-narrow-context. Source review confirms the
shared fuel, result and heap and the absence of a final Context premise.
Audit adds one import. H6, old producers and runtime workers remain unchanged.
No Haskell runtime defect or repair is found. Root FINDINGS retains the
external Haskell handoff. No Haskell suite is repeated for these proof changes.

## Next work and strongest claim

The full checked Caller and memo Context boundary for modeled native narrowing
is now closed. Compose this producer with actual selection, recursion
bookkeeping, the concrete typing callback and ordinary entry. The current
producer requires an actual initial read. It has no intervening recursion
check or callback between that read and its action.

Retain the original selection receipt. Do not reuse its equation at the
narrowed cache, because the target's expandable flag can change. Transport
Ready and incoming avoidance through the actual prefix instead. The concrete
pre-expansion typing callback is pure. Rendered callbacks have a compression
frame, but Frame alone does not establish Safe. Ordered activation refreshes
and arbitrary callbacks still need contracts.

H6 remains the strongest end-to-end language theorem. Covered closed
construction, a valid initial cache, original allocation history and
prescribed finite budgets and modeled node-call rounds derive sufficient
finite bounds and a mathematical width chosen after construction. With empty
inherited payload, the final available value has exactly the original
finite-tree language under the formal formula and entailment interfaces.

The new narrowing result preserves structural and cache invariants. It does
not prove semantic correctness of arbitrary fits and admits predicates or
language preservation of pruning. Fragment-hole history, acyclicity,
successful extraction, terminal parents, parent normalization, whole-driver
language semantics, arbitrary Haskell demand, full raw-stream erasure,
concrete solvers and physical runtime correspondence remain open.
No practical resource or convergence bound follows.
