# Current proof state: original-input native return degree

Checkpoint: 2026-10-29 19:29 CET. The full goal remains ACTIVE.
Proof commit: `f735675369ceed4a8244d54c24d1599b1359f69d`.
Combined source: `2cdd5080bfb066e975856ada4f7a3c819a6f8567`.
Main `ef0a2f32ed2e658603de395253cee89f5747f2e2` is integrated.
Read this note before the older dated checkpoints.

## Objective and strongest claim

The objective is an end-to-end proof of the constrained language generator.
It includes sound outputs, coverage of intended finite values, sufficient
resources and recursive depth from the original input, specified order and
stop behavior, and correspondence with the public Haskell implementation.
The optimized interned core remains primary. Older constructor and equality
results remain secondary targets.

The strongest whole-system semantic claim remains conditional checked
rendered soundness under the semantic and resource contracts, a fixed path
constraint set, and whole-state Discharged. Greater recursive capacity retains
ordered output prefixes with the required work budgets. The terminal chosen
model callback retains the same original assignment. DONE does not imply
Discharged. A configured stop can emit partial results.

The earlier finite-recursion theorem retains the same old work bound,
outcome, resources, all-extra stability and admitted histories. Every emitted
output and concrete Cached payload in returned stop diagnostics retains the
original recursion keys at the same raw slot. This includes nested failures
and runs with no output. It establishes membership, not a strict global rank.

The new result bounds actual successful intersection returns. For original
source requests, it derives an open-binder degree bound from the original
source ceiling and the request's least successful semantic fuel. It covers
actual kernel node and row returns, actual checked native node and row
returns, and actual completed node and row memo hits. It preserves the exact
returned value and both reached heap invariants. The native statements retain
the existing word-range or checked-key conditions.

The useful new case is an open intermediate return in a nonempty recursive
domain. Closed root outputs already have degree zero by the separate
closedness theorem. The closed-root corollaries package the original-input
witnesses; they do not bound every cached body or prove return existence.

## Exact bound and closed induction

`InternedMuDepthAvailableBounds.value_le` bounds an Available source value by
the source's Mu-body ceiling. `initial_value_le` derives the ceiling from the
finite original node inventory. No future heap ceiling is assumed.

`SourceRecursiveIntersectionMaybeMu.result_le` bounds the actual optional
binder result by body degree plus one. `lower` covers every constructor
outcome and all new cached bodies, including probes. `bounded_outcome` retains
a current ceiling when the actual body fits it. These are local constructor
statements. Their body condition is not a final enumeration input gate.

`SourceRecursiveIntersectionKernel.node_result_degree` proves:

```text
actual successful original request return degree
  <= original source ceiling + original semantic requiredFuel(request)
```

Its premises retain original NodeScope and semantic Completes, current valid
facts and ready operands, original-source growth and issued history, current
SemanticHeap and body/probe open-depth equality, and the literal return.
It assumes no current-heap ceiling and no future returned-value bound.

Natural induction on actual kernel runtime fuel closes every node branch.
Ordered child and row walks pass the actual reached heap to the next call.
The semantic child has strictly smaller required fuel. That decrease pays for
the optional binder's extra degree. Canonical constructor hits use exact
physical readback. Reference cases read the original bound Mu payload.
The final theorem discharges every internal nodeIH supplier.

`Kernel.row_result_degree` closes the row helper with that node theorem.
`Kernel.closed_roots_degree` derives the source ceiling and semantic completion
for closed original roots. One bound precedes every runtime-fuel observation.
It applies to later valid heaps that retain those original operands.

`Native.node_ready_degree` and `edge_ready_degree` use the existing exact memo
replay. They add no cached-value degree provenance. `node_return_degree` and
`edge_return_degree` use existing checked native-to-kernel correspondence.
`Native.closed_roots_return_degree` derives one original-input bound for all
checked successful native returns. It supplies no native return existence.

The degree is open stored-plan binder depth. It is separate from cached
Value.depth, term height, enumeration rank, and a global unfolding rank.

## Additive sources and verification

Eleven additive modules contain 18 public theorems in 1,055 lines/71,543 bytes.
No new predicate or runtime definition is added. The modules are:

1. InternedMuDepthAvailableBounds
2. SourceRecursiveIntersectionMaybeMuDepth
3. SourceRecursiveIntersectionKernelEdgeDegree
4. SourceRecursiveIntersectionKernelEdgeWalkDegree
5. SourceRecursiveIntersectionKernelMuDegree
6. SourceRecursiveIntersectionKernelRowsDegree
7. SourceRecursiveIntersectionKernelUnionDegree
8. SourceRecursiveIntersectionKernelReturnDegree
9. SourceRecursiveIntersectionKernelClosedDegree
10. SourceRecursiveIntersectionNativeReadyDegree
11. SourceRecursiveIntersectionNativeReturnDegree

All 12 final sources, including Audit, pass warningAsError and all linters.
Audit checks 82,076 theorem dependencies in 4,624 jobs. The old imported
unused-variable warning remains visible in the default Audit build.
No suppression, custom axiom, placeholder or native_decide is added.

The main public readback has 874 theorem checks and axiom lists and 73 old
definition bodies. It contains 3,654,083 bytes. SHA256:
`26b091b5136f428fb0fbc42b505733178b69c18ab26c438d36b2b3391e87e832`.
The old 3,609,022 bytes are an exact prefix. All 45,061 new bytes were read.

There were 38 completed new Lean commands: 28 PASS and ten retained failed
drafts. One diagnostic evaluator reached its five-minute cap. It yielded no
completed numeric observation. It establishes neither a counterexample nor
divergence. Earlier UNTESTED source proposals remain historical evidence.
The inherited prior-public-readback report is excluded from new command totals.
Nine native commands completed: eight PASS and one GMP linker failure.

Compiler and native checks run serially with measured max/high memory of
4 GiB and zero swap. Each has a five-minute cap. Per-command input snapshots
and raw logs remain. Early batch peak records went to the shared default
file; its retained tail is separate from the task-specific peak file.
The timed-out evaluator has an outer exit record, not a completed inner report.
The runner now writes raw output as the child runs.

All 4,612 old non-Audit Lean identities and 461 stronger source identities
remain. Only additive imports change Audit. All old document bodies remain
exact suffixes. All earlier evidence stays unchanged.
The return-rank audit's correction records 12 whole-source reviews against an
eight-file budget. Its original eight-file claim is superseded. Other source
copies and exact reviewed cuts remain separate evidence.

## Upstream integration and Haskell findings

Main first advanced to e2185ede. Commit 37f0ba817 replaces the unavailable
QuickSpec.Internal.Utils.usort import in specftacular/examples/HugeLists.hs
with a local Int sort that removes duplicates. Merge d53d37df retains it.
The benchmark target and the actual example are separate files. Both were
checked. The first benchmark build failed on missing GMP; the host-linker
retry passed. The linker change is local to PATH inside nix-shell.

After the elapsed time, main advanced to ef0a2f32. Merge 2cdd5080 retains the
new source documents, language updates and merges, canonicalFTA, listing and
sampling checkpoints, and support for symbols at several arities.
Three conflicts were resolved: the serialization imports, its constraint
documentation, and the core changelog. Both sides' behavior and repair notes
remain. The optimized interned operations and local probe-freshness repair
remain. No old Lean source changes with this merge.

The merge changes 23 previously recorded Haskell/Cabal identities and adds
eight, for 829 recorded identities. The exact upstream and resolved inputs
remain. The strict-prefix parser helper retains its exact prior body.
Both parser branches still use it. Core tests pass 383 examples, serialization
passes 56 examples, and the Sized/checkpoint subset passes 30 examples.
Fourmolu and cabal-gild checks pass. These checks are implementation evidence.

FINDINGS retains serialization repair
`c15021ce706ef560b6c0ab335ceed1a4b67ba4aa` for external pickup.
Main ef0a2f32 still lacks checkedPathClass. The lawful codec and exact malformed
inputs remain in the older findings. This merge keeps the repair with the
new document and checkpoint parsers. FINDINGS also records the upstream
HugeLists fix and the current integration checks.

## Biggest remaining gaps and next proof

The main proof gap is an original-input bound through all generated work.
The new return theorem does not bound every new Mu body in every intermediate
or pending heap. Repeated per-query bounds in growing heaps do not provide a
fixed global enumeration rank. Identity cardinality, guard growth and word
range checks still need original-input derivations or another progress proof.

Next, prove Lower for every actual kernel outcome, including failure and
pending construction. Use runtime-fuel induction, the checked return theorem
for actual successful body calls, and MaybeMu.lower for all constructor
outcomes. Ordered walks must retain all earlier effects before a later failure.
Then connect that bound to actual native prefixes and generated-query lineage.
Do not replace these obligations with a future-result supplier.

Nonterminal chosen-value coverage and sufficient recursive capacity remain
open. Policy, origin, complete public API contracts and Haskell correspondence
remain open. The new source-edit, merge, canonical export and checkpoint APIs
also need explicit formal contracts. PRNG replay tests do not prove probabilistic
correctness or implementation correspondence. No completion percentage is
supported by the present evidence.

Preserve the exact earlier counterexample scopes. The 22-step open-body witness
shows an unprepared body. A returned .mu26 tag does not prove payload equality,
degree-ceiling failure, divergence, or a prepared whole-Packet counterexample.

## Restart

Read NEXT-PROMPT.md, HANDOFF.md, FINDINGS.md, then this note.
Refresh upstream with ff-only pull; use the command-local SSH 443 override.
Preserve local proofs, repairs, counterexamples and marked drafts.
Use a new writable evidence directory after this checkpoint is sealed.
The complete archive is lean/restart-evidence/20261029-native-degree-progress/.
Its manifest and standard-library verifier bind every retained payload.
Board 733 has exact author, content, metadata, type and thread readback.
Regular pushes to formalize remain explicitly authorized. Keep the full goal
ACTIVE. Continue with all-outcome allocation bounds and the global obligations.
