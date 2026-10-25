# Concrete callback and repeated-recursion restart

## Current result

Source commits: `3f02ddcef` and `6dff1a207`.
Recorded origin/main: `153e1a211b56dd78bd22f6b427fb78e673041d55`.
The whole formalization goal stays ACTIVE.

The selected ordinary proof now derives a concrete Left callback followed
by its source stop/selection restart. The same completion witness supplies
the stronger output. The original native selection also derives an actual
repeated-recursion restart with rebuilt waiting counts and candidate flags.
Neither result assumes a successful future continuation or a future cache.

H6 constructed_node_calls remains the strongest end-to-end language theorem.
Given a covered closed construction and valid original constraint allocation
history, any prescribed finite node-call budget and round count have derived
sufficient finite fuels and one mathematical width chosen after construction.
The modeled trace completes. Its final available value has exactly the
initial finite-tree language for every ambient environment and finite term,
under the formal Formulas and Entailment interfaces. The inherited constraint
payload is empty. This theorem does not cover the whole typing/pruning driver,
withoutRedundantEdges, arbitrary mixed calls or convergence.

## Stop and selection retain source order

Restart.decision tests an optional stop predicate before pure next selection.
It tests every remaining candidate, including blocked candidates. It stops
only if that list is nonempty and every candidate passes. An absent stop
rule always reaches selection. The result distinguishes early stop, done,
stuck and a selected expansion. Restart.run rejects only stuck selection.
Other results retain the exact supplied metadata and enumeration core.

decision_frame retains the decision under compression at the same metadata
and allocation counter. The frame retains indexes. The counter determines
the candidate list range. A metadata update can change the preference, so
the proof uses the returned metadata on both sides. It does not equate old
and updated metadata preferences. selected derives readiness, no incoming
references, and the closed available pending value for an actual expansion
decision from the original Safe and native CacheValid inputs.

## Concrete callback rejection or restart

AfterCallback.run executes recordTypes on the actual fragment, applies
require to the negated pruning flag, reads the actual resulting core and
calls Restart.run with the callback's returned metadata. It frames this
core with the indexed cache already preserved by the callback theorem.

run_success derives actual Success for a false pruning flag and a non-stuck
restart. The returned core is the same callback endpoint. run_pruned excludes
every successful continuation when a known callback result prunes. It uses
recordTypes_agrees to compare any other success of that same action.
run_stuck excludes every successful continuation when the known restart is
stuck. Agreement retains metadata and a frame between compressed endpoints;
decision_frame transports the stuck decision across those endpoints.

These are claims about successful results. They do not state that the raw
composite result is empty. A raw callback action can also contain fuel errors.
Follows records both implications for every stop rule and expansion order.
The original receipt supplies representative totality through its actual
Safe input. No new callback-success or future-success premise is added to
ReceiptCallback.completes. Its existing bounded callback is executed once.

Completes and completes retain their exact declaration types and inputs.
The completion predicate adds Follows at the same chosen fuel, result and
callback cache. The earlier safety, metadata, history and index clauses stay.
SelectedOrdinary.complete_with_history and its wrapper remain byte-for-byte
unchanged and inherit the stronger predicate through their existing call.
This is per-receipt availability, not execution of callbacks inside the
serial native alternative scan. Each source sibling uses the same incoming
metadata; its returned metadata feeds its own recursive continuation.

## Repeated recursion derives an indexed restart

ParkedRestart.selected_complete_with_order calls the original native selected
producer once. It retains all original read/check/write receipts and derives
the unchanged counter and dependency levels for the actual pending clear.
The actual clear preserves the representative forest and removes outgoing
bucket references. It does not add a dependency or advance the frontier.

adapt rebuilds the indexes using NativeIndex.write at the original cached
indexes. The gained bucket is empty. The lost bucket is the full original
scs, so every suspended waiting count is removed. The candidate flag is
recomputed for the cleared pending slot. The final mapping retains the
exact observed check core, rather than the synthetic indexed-write core.
Framing the check core with old indexes alone would leave stale counts.

adapt_after_write derives the adapter result from the actual clear write
and the indexed-write receipt. The clear retains the forest read by count;
the original waiting map and flags are the same. The final frame retains
the observed core. There is no list-write idempotence assumption.

run performs one getValue and one native checkRepeated. Read and check errors
remain explicit. A false guard returns the checked prefix with payload None;
it is a boundary awaiting narrowing. A true guard recovers the indexed cache
and restarts at unchanged metadata. Failed index recovery returns an explicit
representativeFuel error. The proof makes no general classification claim
for arbitrary candidates or insufficient fuel outside the admitted inputs.

selected_complete_with_restart starts from Safe, actual native CacheValid
and original pure selection. It derives the same selected producer witnesses,
retains final Safe and CacheValid at the same Caller, and transports global
pending history when supplied. On the repeated branch it derives a finite
countFuel from the producer's indexed-write receipt. Every larger index fuel
gives the same exact raw restart: empty for stuck, otherwise a singleton at
the actual parked core. The exact read and check fuels are those chosen by
the original producer. No future adapter result is an admission premise.
This branch performs no narrowing or oracle call.

## Verification

Lean 4.34.1 checks all five changed modules with all linters and warnings
as errors. Eight strict attempts retain three failed attempts. The first
restart proof left reflexive goals after unfolding. The first two callback
proof attempts used an unmatched framed rewrite, eliminated a binder too
early, or left ExceptT.run opaque. The final direct expansion and explicit
substitutions close these goals. All five final strict checks pass.

Four installed helper/consumer builds pass. The unchanged selected-ordinary
consumer rebuilds with the stronger completion output. Aggregate Audit passes
with 3770 jobs and checks 76876 theorem dependencies. Audit source adds one
import; its checker stays exact. The existing unused inputs warning remains.
The dependency total is an audit count, not a completion estimate.

Installed public readback checks 21 declaration types and axiom sets. It
prints the full installed Completes, Follows and restart decision definitions.
The full output has 1366 lines and 127080 bytes.
SHA-256: `7db8abd563e04cdc3b00c6e0b2b50cfb895982e97a946cf149d77cf4bafee345`.
There is no output ellipsis. All axiom sets are subsets of propext,
Classical.choice and Quot.sound. No new project axiom is added.
All 14 checks run serially under heavy-management 4 GiB caps.

Independent source review confirms the actual callback endpoint, all-success
rejection scope, full stop set, same returned metadata, original lost bucket,
actual indexed write, derived count fuel and observed checked core. It finds
no future-success admission or full-loop claim. The original recursion worker,
selected producer, native scan and H6 source stay unchanged. No Haskell or
package file changes, so the Haskell suites and format checks are not repeated.
No new Haskell repair is identified. FINDINGS retains the external repair table.

Evidence: lean/restart-evidence/20261026-native-callback-restart.
The manifest records exact payload bytes and SHA-256 for all raw logs,
strict source copies, failed attempts, public readback, final and original
source snapshots, proof diff, verification report and cap records.
Force-add exactly those payloads and verify staged and committed bytes.

## Next work

Compose a complete selected-step worker from the original selection. Its
repeated branch must use this derived indexed restart. Its false branch
must use the actual narrowing, Right callback and admitted native ordinary
producer at their reached Caller/cache/memos. Keep Empty, rejected, parked,
stopped and unsupported outcomes explicit. Do not treat a false check prefix
as a complete ordinary expansion.

Then compose each completed fragment callback with the recursive continuation
inside the actual depth-first alternative demand. Siblings restore the local
enumeration state and share evaluated native interner/memo effects. The
current serial alternative scan can force later alternatives before earlier
recursive continuations. Its per-receipt callback proofs do not establish
the source's complete effect interleaving or arbitrary Haskell forcing.

The ordinary producer still requires reached-state numeric Ranges. A complete
forecast must derive all native query capacity from initial inputs across
narrowing, selected children, alternatives and recursive continuation.
Additional fuel does not prove that machine-word capacity is sufficient.
Native Graph/heap classification, terminal/nonordinary outer fallback,
whole-driver pruning language laws, extraction, concrete solver behavior,
physical containers and complete Haskell finite-machine correspondence stay
open. H6 and component results must remain distinct from those obligations.
