# Ordered pruning resume observations

Updated: 2026-10-24. Start: `74104221af2bdc2d0ccf454658170dd9a253545a`.
Proof: `6b168d41cc9a5e7c1a7f2eb0db6f0e395edebe32`.
Main: `0db62d26b87e8e55b6c2719f6312ece6f93ed31b`.
Merge: `504523e47a9b85c5dc5f24a396dbf12baf54f290`.

## Checked result

SourcePruningPartialMatch uses the existing Pattern, Term and PartialSymbol
representations. Its branch order follows Pruning.matchPartial. Hole and the
empty AnyPrefix accept every shape before the raw-hole and truncation cases.
Other patterns park on a raw hole leaf with the original ID. Exact patterns
check equal arity. Prefix patterns check sufficient arity and ignore trailing
children. Pending pieces retain child order and repeated entries.
Four branch lemmas expose both wildcard exceptions without extra premises.

SourcePruningResume models Pruning.resume. It reads every parked representative
in input order. It then sequences the pure optional results and concatenates
their pending lists. A rejected match is an Option value inside the state
action. It does not skip later representative reads. A failed bounded read
still fails through the existing action. The part compares the returned root
to the unchanged raw current. It calls the actual imported partial matcher.
There is no matcher callback or canonical-current premise.

resume_frame preserves the complete compression Frame after every successful
resume. The frame retains the allocation counter, stored values, obligations,
both ancestry fields, and every root representative with its stored size.
The parent paths can differ. Left forest totality is an explicit premise.
The frame derives totality for the related input and each intermediate state.

resume_agrees gives exact optional output equality and a complete final frame
for two successful executions on framed inputs. They use the same raw current,
partial term and pending list. Their successful bounds can differ.
resume_transport constructs a finite matching execution in the related input
from one actual successful execution. Right success is not a premise.
The proof constructs each actual intermediate state in source order. It raises
the head and tail actions to the sum of their finite bounds. Their exact
endpoints remain. resume_moreFuel retains the exact result and final state.

## Boundaries and next work

These are observation results. They do not prove that a rejected partial match
has no required completion or that every pruning template is safe. No Safe,
Finished or accepted-completion premise is added. The result includes successful
actions whose optional result is none. It does not equate bounded error rows,
callback traces or whole result streams. The Haskell source comparison is
reviewed correspondence, not verified extraction or a native runtime proof.

The next target is the actual templateOracle callback. Compose its partial
render, ordered resume traversal and ordered new-match production. Then cover
typedTypes and its unexpanded-node reads. Preserve template and program order,
raw IDs, duplicate entries and actual intermediate states. The separate
selected-current protection invariant still needs its cached-driver composition.
Complete canonical mutation histories and the cached-driver bridge remain open.

H6 SourceCurrentColdFiniteWarmCalls.constructed_node_calls remains the strongest
combined theorem. Covered closed construction and a valid allocation history
supply finite repeated node calls at a sufficient mathematical width and fuel,
with exact finite-tree language preservation under the formal guards.
It excludes withoutRedundantEdges and does not prove convergence. Full-pipeline
composition, complete resources, practical widths, Haskell and solver refinement,
phase-4 correctness and general convergence remain open. H23 is still queued.
The full formalization goal is active and incomplete.

## Upstream and validation

PR #169 is integrated. Read notes-current-upstream-lpo.md. Both recorded LPO
failure mechanisms have source repairs and focused native validation. General
order and pruning proofs remain separate. FINDINGS keeps the external repair
index first and records the merged status. All older reports remain historical.
No additional Haskell source patch or committed test is introduced locally.

Pinned Lean 4.34.1 checked both final sources with warnings as errors and all
linters. The resume passed its first strict check. The matcher needed only two
escaped prefix proof-case names. The executable definition did not change.
The original failed attempt, author preflight draft and exact patches remain.
The installed aggregate Audit passed: 3673 jobs and 75792 dependency checks.
It replayed one older unused-variable warning in
InternedFreshOrdinaryClosedCompletion.lean:24. No new-source warning occurs.
All 11 public signatures and eight axiom reports were read in full. Their
axioms are limited to propext and Quot.sound. No project axiom or proof-limit
override is added. Independent source and public reviews are retained.

Evidence is in restart-evidence/20261024-pruning-resume. It retains the original
baseline, exact upstream changes, checks, failed harness attempts, cap receipts,
source reviews, public output and the preceding checkpoint publication receipts.
The verifier checks exact preservation of every baseline file. It permits only
the recorded upstream changes, document updates and one Audit import.
This record precedes the evidence commit and authorized push to formalize.
