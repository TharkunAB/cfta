# Original selection through native narrowing and the Right callback

## Current result

Framed replacement: `fc1e38a19`.
Framed cache and Caller producers: `93d621a5c`.
Selected composition and Audit import: `5106259fa`.
Main remains `153e1a211b56dd78bd22f6b427fb78e673041d55`.
The whole formalization goal stays ACTIVE.

Original selection now derives the single pending value read, the native
recursion guard and, when not repeated, native narrowing and its full Caller
and indexed-cache result. A nonempty result then executes the concrete
pre-expansion typing callback at that exact cache and new handle.
No successful read, check, narrowing run, final Context or final cache
invariant is supplied. The repeated branch retains its exact parked receipt.

## Actual frames and genuine safety

The native false guard can compress representatives between the first read
and narrowing's representative reread. The older cache and Caller producers
used entry=readAfter. Inserting another value read would not follow the source.

Replacement.after_frame now accepts the actual Frame readAfter entry and
genuine Ready uv entry. The latter supplies entry safety, allocation and
rootness. An arbitrary Frame alone does not establish Safe. The actual
representative reread derives its reached safety and root=uv from entryReady.
The first-read frame, supplied entry frame and actual reread frame compose
for path, value, count, flag, realization and reference transport.

The actual plain write and indexed scs/scs write retain the same reread and
final-state witnesses. Canonical waiting-map identity remains proved.
The old after_read declaration keeps its exact type. Its wrapper supplies a
reflexive frame and derives entry readiness from the actual read.

NarrowCache.complete_after_frame calls Action.prepare_pending_complete once
with the actual entry. Empty rejects at entry. An equal handle returns
frame entry before. A changed handle retains Action's exact representative
reread, plain write and native indexed write. The new interface retains the
old initial invariants and actual initial read; its added premises concern
only the real intervening enumeration frame and readiness.

NarrowContext.complete_after_frame passes that cache producer's same native
fuel, result and heap to NativeContext.outer_post. Initial realization and
the original read derive old-value availability. Initial Caller Context
derives the reached full Post and saved memos. No final Context is assumed.
The old complete declarations in both modules keep their exact types.
They use reflexive frames and actual-read readiness in their wrappers.
No runtime worker changes.

Saved memos belong to the chosen native exposure fuel. Larger native fuels
retain the result and heap. Equality of saved memo tables across those fuels
is still open. The enumeration frame does not describe arbitrary intervening
Caller, metadata or memo changes.

## Original selection and one read

SelectedNarrow.complete calls Recursion.selected_complete once. It retains
the exact readAfter and checked cache. Its extra ready and incoming proofs
use the original selection equation at the original cache. It does not repeat
selection at the narrowed cache or execute a second initial value read.

The true branch forwards the actual parked endpoint, full lost-bucket count
update, disabled expandable flag and representative/write equations.
It does not call narrowing or an oracle on that branch.

The false branch composes the inverse first-read frame with the prefix's
full false-check frame. This gives Frame readAfter checked.core. The native
guard supplies genuine Ready at checked.core. The framed Caller producer
therefore starts its enumeration action at the actual checked endpoint.

The original decode equation identifies the narrowed input with the prefix's
old value. The proof retains the returned native fuel, result, heap, encoded
handle, advanced Caller, saved memos and final enumeration cache together.
Empty retains its reached Caller and rejecting action before the callback.
Equal and changed handles retain their original cache/write alternatives.

For nonempty output, recordTypes_inr proves the actual callback succeeds as
(false, metadata) at the returned cache for every callback fuel. It uses the
new narrowed handle. The callback changes no enumeration or metadata field.
Its Graph parameter needs no native-heap correspondence for this pure event.
No arbitrary oracle contract follows.

The reached cache retains Ready, paths, realization, exact canonical counts,
native flags and incoming avoidance derived from original selection.
Initial global pending-reference history remains a conditional output.
The proof does not perform ordinary-entry ancestry bookkeeping early.

## Verification and evidence

All four proof modules and the changed Audit import pass Lean 4.34.1 with
all linters and warnings as errors. All five strict checks pass on their
first attempts. Three installed helper builds pass. The aggregate Audit
passes with 3757 jobs and 76734 checked dependencies. Installed public
readback checks eight declarations, including the three original interfaces.
Its full output has 728 lines and 60618 bytes. Its SHA-256 is
`632cff9bff7e54640aee1f7433fbad19c89e2227ff76c4f45b76b130db0b50e0`.
Every axiom set is a subset of propext, Classical.choice and Quot.sound.
The older unused inputs warning remains unchanged. All ten checks run
serially under 4 GiB heavy-management caps with no swap.

Source review confirms genuine entry readiness, unchanged original declaration
types, one initial read, original selection, shared native and enumeration
witnesses, and the callback's exact new-handle event. The new interfaces
factor existing proofs. They add no runtime worker or producer admission
premise to the old public interfaces.

Full compiler inputs, raw logs, reports, original headers, final sources,
cap records and the proof patch remain in restart-evidence/20261025-framed-narrowing.
Audit adds one import. The native guard, Action producer, ordinary workers,
H6 and all Haskell runtime source remain unchanged. No Haskell defect or
repair is found. Root FINDINGS retains the external Haskell repair handoff.
No Haskell suite is repeated for these proof changes.

## Next work and strongest claim

Compose the nonempty narrowing result and pure Right event with actual
ordinary entry and expansion. An ordinary node result and a nonterminal
suspended bucket are still required. Edge selection must use the narrowed
stored rows. Apply NativeOrdinary.complete with the reached cache, Caller
and saved memos. Use post.context as its genuine initial Context.
The returned pending-history implication and stored slot derive InputsPending
through EnumerationReferences.pending_inputs. Incoming avoidance is already
unconditional at the narrowed cache. Compose the Caller receipts with
Post.trans. Do not rerun selected_complete at the narrowed cache.

Numeric Ranges must refer to that actual reached Caller/cache and query table.
Original-cache ranges do not transfer from heap Keeps or waiting-map identity.
Do not replace that remaining admission boundary with a successful trace
premise. Preserve Empty rejection, nonordinary parents and terminal buckets
as separate outcomes.

The repeated branch's scheduler restart, the later fragment callback, fragment
hole history, acyclicity, successful extraction and whole-driver language
semantics remain open. No loop progress, convergence or termination is proved.
Arbitrary fits and admits predicates receive no language-preservation law.

H6 remains the strongest end-to-end language theorem. Covered closed
construction, a valid initial cache, original allocation history and any
prescribed finite budget and modeled node-call rounds derive sufficient
finite bounds and one mathematical width chosen after construction. With
empty inherited payload, the final available value has exactly the original
finite-tree language under the formal formula and entailment interfaces.
Concrete solvers, physical containers and machine counters, arbitrary Haskell
demand, full raw-stream erasure and practical resource bounds remain outside
that claim.
