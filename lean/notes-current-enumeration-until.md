# Shared enumeration and the eager completion bridge

Updated: 2026-10-24. Proof commit: `ecabbf38e669d96275ce991fa8a843bcec3b51ed`.
Start: `790c39ce21f0be612fafcb6a36eb972ac5bf03f9` on `formalize`.
Imported main: `6b62b4afefca80bb05f5a37546212a99980aa3df`.
The main refresh and its Haskell repair are already pushed at the start.

## Checked result

`EnumerationUntil` adds the complete bounded control flow on the existing
`EnumerationState` graph and state. It includes parameterized edge and slot
expansion, shallow child allocation, narrowing, repeated-recursion handling,
both oracle callbacks, stopping and partial rendering. Earlier definitions
and proofs are unchanged. Audit adds one import.

`EnumerationUntilBridge.no_stop_eager_successes` compares the shared driver's
no-stop, identity-narrowing, eager specialization with the earlier eager loop.
Both actions use the same finite bound and the same modeled scheduler.
For `ReadOnlyOracle`, the ordered successful rows agree. The equality retains
duplicates and the complete final state. It changes the old Unit result to
`none`. The statement needs no `Safe`, total-forest or completion premise.

`no_stop_eager_success_iff` gives exact successful-run correspondence at that
same final state. `no_stop_eager_outcome` adds `Safe before` and applies the
existing completion theorem. It derives `Safe after`, a nondecreasing slot
counter and `Finished graph after`. Finished means no candidate remains.
It does not discharge residual guards or establish concrete acceptance.

The eager slot and edge specializations equal their earlier complete actions.
`stop_all` proves that a positive bounded call returns the current state before
scheduling when the nonempty candidate list passes the stop rule. Candidates
include blocked slots. Fuel zero remains an explicit model error.

## Scope boundaries

`ReadOnlyOracle` requires each successful callback branch to leave the complete
machine state unchanged. It permits rejection, errors and caller-state changes.
Some public observing helpers can compress representative paths. Their more
general storage-preservation contract still needs a separate bridge.

The success theorem does not equate error rows or callback traces. The new
driver rejects a narrowed empty node before the pre-expansion callback. The
old loop called that callback first. An arbitrary modeled callback can replace
the empty slot and make the old loop succeed. A callback that produces only an
error is read-only under the successful-branch definition, but it still changes
the old error output. These are source-derived examples, not new native probes.

The public shallow API is separate from the eager specialization. A read-only
callback can reject only the complete fragment `f[a]`. Eager expansion reports
that fragment. Shallow expansion reports `f[hole]` and then `a`, so that callback
does not reject it. Thus a constantly false stop rule does not establish generic
equivalence between the public shallow and eager APIs. This example is also a
source derivation. No direct public native slot-setter witness is claimed.

Partial terms can contain holes with no accepted completion. This behavior is
intentional. The earlier native empty-root example remains the decisive probe.
The partial wrapper retains errors and state. It does not discharge obligations.

Haskell selects from cached expandable and waiting sets. This first additive
model uses the earlier slot scan, which can compress representative paths.
Existing index-selection theorems equate offered choices and canonical roots.
They do not equate complete representative forests. A source cache realization
and an observational state bridge remain open. The abstract recursive graph
view must also realize both Mu and InternedUnion outer expansion.

## Validation and preservation

Pinned Lean 4.34.1 accepted the complete combined source with all linters and
warnings as errors. Its successful final check has an empty diagnostic log.
Both installed modules build. Audit passed with 3659 jobs and 75635 theorem
dependency checks. It replayed one older unused-input warning. The new modules
have no warning. These totals are validation evidence, not a completion claim.

Root read all 21 complete compiled public signatures and 12 axiom reports.
An independent reviewer read the installed source and compiled signatures.
The public theorem dependencies use only propext, Classical.choice and
Quot.sound. Some theorems need a subset of these axioms.

The retained attempts include temporary-package path failures, proof reduction
errors and an unsupported display option in the first public readback. The
successful readback removes that display option. No failed attempt is reported
as a successful check. No Haskell source changed in this checkpoint.

Evidence is in `restart-evidence/20261024-enumeration-until`.
The baseline pins 126320 earlier tracked files and modes. The backup ref is
`codex/backup-enumerate-until-20261024-0055`. All earlier proofs, drafts,
counterexamples, repairs and sealed evidence remain. The same H23 scan-chain
counter-consumer proposal remains queued in the preceding refresh evidence.

## Next proof target

Establish an observational bridge for actual cached selection and observing
callbacks. Then prove shallow preparation preserves the intended complete
languages under explicit oracle and narrowing conditions. Retain speculative
partial outputs as a separate contract. The new program frontend also needs
typing, pruning, type-alternative correlation and runtime correspondence proofs.

H6 `constructed_node_calls` remains the strongest combined system theorem under
its stated premises. Full-pipeline composition, upper resources, practical
machine width, Haskell and solver correspondence, and convergence remain open.
The full goal remains active and incomplete.
