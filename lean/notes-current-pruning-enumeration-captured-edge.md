# Native captured-slot edge finalization

## Current result

Finalization safety: `3197aaaa47cf0080e9097da1191f36947bb2fd5b`.
Selected entry: `2bfd43cfe3e7001dbdec7adbae2c98b98a7d1ca7`.
Captured edge: `736d95555def03b909a25d5b1a756270f95055dd`.
Main remains `153e1a211b56dd78bd22f6b427fb78e673041d55`.
The whole formalization goal stays ACTIVE.

`SourcePruningEnumerationCapturedEdge.complete` derives sufficient finite
bounds for one supported selected ordinary edge and its final raw-slot write.
The actual stored pending handle must decode to the supplied ordinary parent.
The successful result records the residual, resets expansion ancestry and
stores the completed fragment at the original captured target. A valid child
rejection retains its exact observation and cache without finalization.
The theorem derives completion. It assumes no successful future trace.

## Selected entry

`SourcePruningEnumerationSelectedEntry.complete` starts with
`EnumerationDriver.Ready` at the actual entry state and an actual pending
slot equation. Native realization, root paths, exact waiting counts and
expandable flags supply the other entry invariants.

The proof uses the existing `Entry.complete` once. Its actual read and capture
receipts establish that the captured target equals the original selected
root. Both reads can compress paths. They preserve the target's value and
complete class. Ancestry setup retains `Ready`, counter, values and both
cached indexes. The exact original entry action produces the returned core.
Inherited bucket bounds follow from the actual stored pending value.
Every separately supplied `InputsPending` bucket transports through entry.

This is a separately composable entry theorem. `CapturedEdge.run` starts at
the captured edge input; it does not implicitly run `Entry.enter`.
`Selection.ready` can establish entry readiness from actual selection at the
same state. Native narrowing and the oracle occur between scheduler selection
and entry. Full scheduler composition must prove readiness through them.
Heap readiness in the older `Admission.complete` has a different meaning.
It does not supply selected-slot readiness.

## Captured-slot completion

The initial captured target is allocated and a root. Its actual pending
payload supplies bounds. `Ready.avoids` excludes the captured class from that
payload. The explicit `InputsPending` premise excludes every old enumerated
class from the payload. These are separate conditions. Existing selected-edge
completion derives the actual post-child caller, queries and cache.
It protects the captured root and its stored pending payload.

The proof reads that current payload at the same raw target. It calls the
existing `Finalize.complete` once. Native finalization removes the waiting
references of that current payload and writes the fragment at the captured
target. It does not perform another representative lookup or use a terminal
child's merge winner. Expansion ancestry becomes empty. Per-variable recursion
ancestry stays unchanged.

`Finalize.written_safe` derives safety for the ancestry reset and bounded
root replacement. `Finalize.complete` retains every old premise and output
and adds the implication from current safety and target rootness to final
safety. Its runtime definitions are unchanged.

`CapturedEdge.run` returns the existing selected-edge result inside `Option`.
A failed native finalization is explicit `none` outside admission.
The completion theorem derives an actual cache at sufficient bounds.
It retains caller `Post`, saved queries, monotone counter, roots, storage,
pending-value realization, exact waiting counts and native expandable flags.
Successful output retains `Safe`, a bounded fragment, the exact enumerated
target slot, empty expansion ancestry and target rootness.
The stopped-child law forwards every stopped receipt without a final write.
The admitted rejection branch has no unconditional `Safe` claim.

Finalization creates an enumerated slot. Therefore full `EnumeratedOrigin`
and unchanged-value protection cannot hold for that target. The new theorem
states both properties only away from the target. `InputsPending` for the
parent bucket still holds: the target case uses transported `Ready.avoids`;
the other cases use the selected-edge pending-input result.
This does not establish global `PendingReferences`, pending fragment holes,
fragment acyclicity or complete driver language semantics.
Conditional numeric admission and the original `InputsPending` premise remain.

## Alternatives and native state

Source inspection confirms the branch boundary. `Enumeration.hs:328` defines
pure CPS enumeration. Its `Alternative` instance at line 353 and `branches`
at line 372 give each alternative the same enumeration-state input.
Finalization at lines 900 to 902 runs separately for each successful branch.

That branch snapshot does not contain the native interners or memo tables.
`Interned/Type.hs:453` and line 510 define process-global caches and identity
supplies. `Interned/Cache.hs:169` mutates a shared interner through
`unsafeDupablePerformIO`. `Interned/Memo.hs:91` uses shared memo tables.
Unfolding, intersection and emptiness have global cache families too.
Rejected branches do not roll these native effects back.

Ordered native alternative composition must restore the original enumeration
cache and retain the effects of evaluated native calls. Independent runs
from the same complete caller/query state are isolated logical runs; they
do not reproduce the shared process-global history.
`allBranches` at line 377 exposes a lazy result list. Memo entries can retain
lazy results. A strict serial caller thread chooses a forcing discipline.
Agreement with arbitrary Haskell demand is a separate correspondence theorem.
No Haskell runtime defect or repair is established by this source inspection.

## Verification

All three final modules pass Lean 4.34.1 with all linters and warnings as
errors. Six strict attempts are retained. Finalization attempt 1 exposes
record and lambda syntax. Entry attempt 1 needs explicit cached-index
equalities. Captured-edge attempt 1 needs final-forest equality and runtime
match reduction. Attempt 2 passes for each module.
No linter or production proof-resource limit is disabled or increased.

Installed builds and all six public declaration readbacks pass.
The full public log has 240 lines, 17856 bytes and SHA-256
`a5a6ad7c9efd62ba0d6ac64dbe773505a9b2882df3a638a64e8f7e8e2d8018b6`.
All axiom sets are subsets of `propext`, `Classical.choice` and `Quot.sound`.
The aggregate Audit passes with 3743 jobs and 76656 theorem dependencies.
The older unused `inputs` warning remains unchanged.
Checks run serially under 4 GiB heavy-management caps with no swap.
Full attempted sources, raw logs, reports, final source snapshots, native
source references and peak records remain in
`restart-evidence/20261025-native-captured-edge`.
Source review finds no semantic blocker.

No Haskell source changes. The Haskell repair handoff remains first in root
FINDINGS. No runtime test is repeated for these proof-only changes.
The optimized interned core, existing native child workers, historical
repairs, counterexamples and older constructor/equality work remain unchanged.
H6's source remains unchanged.

## Next work and strongest claim

Compose the separately proved entry and captured-edge steps into the full
ordinary-parent wrapper. Restore branch-local enumeration inputs for each
ordered alternative. Account for shared native growth and query memo effects
from evaluated alternatives. Establish the required cache-invariant transport
against the grown heap. Make the forcing discipline explicit.
Derive the remaining global pending-reference and fragment-dependency history
facts. Then connect whole-driver language semantics and scheduler callbacks.

H6 remains the strongest end-to-end theorem. Covered closed construction,
valid initial constraint cache and original allocation history, any prescribed
finite budget and number of modeled node calls derive sufficient finite fuels
and one mathematical width chosen after construction. With empty inherited
payload, the final available value has exactly the original finite-tree
language for every ambient guard and term under the formal formula and
entailment interfaces.

Arbitrary mixed calls, initial-only numeric admission, withoutRedundantEdges,
whole typing/pruning, concrete solver correspondence, extraction, physical
maps and machine integers, practical resource bounds, convergence and full
Haskell correspondence remain outside that end-to-end claim.
