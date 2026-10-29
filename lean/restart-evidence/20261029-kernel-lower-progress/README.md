# All-outcome kernel body bounds: complete restart evidence

Source `c63fd18298a6060b39076eea484dc5db26f8a997`. Documentation `c3b713f9ad0892eaef3c562224a1ebca0a6356d2`.
The full formalization objective remains ACTIVE on formalize.
Every sealed regular file is archived without a filter.
The manifest binds all 501 paths, byte counts and hashes.
Raw bytes: 45,019,448.
Compressed bytes: 8,821,526.
SHA256: `07c79e3a87daa725e57776e9495e3c4682a01efbc5e8b286b8499f2c913e583b`.

Verify or reconstruct from the repository root:

```sh
python3 lean/restart-evidence/20261029-kernel-lower-progress/verify.py lean/restart-evidence/20261029-kernel-lower-progress --extract /tmp/mcfta-kernel-lower-progress-restored
```

Use a fresh destination. Omit --extract to verify only. The standard-library
verifier rejects duplicate, missing, extra, unsafe and non-regular members.
It executes no Lean or Haskell code. Keep reconstructed evidence immutable.
Continue in a new writable area. The original source area is sealed read-only.
Historical UNTESTED labels and failed drafts remain. Final strict mappings
identify the exact 10 checked sources. All 160 command input snapshots match.
The note below specifies the result, conditions, failures and remaining gaps.

---

# Current proof state: all-outcome kernel body bounds

Checkpoint: 2026-10-29 19:53 CET. The full goal remains ACTIVE.
Source: `c63fd18298a6060b39076eea484dc5db26f8a997` on formalize.
Main ef0a2f32 remains integrated. Read this note before older checkpoints.

## Full objective and strongest system claim

The objective is an end-to-end proof of the constrained language generator.
It includes sound outputs, coverage of intended finite values, sufficient
resources and recursive capacity from original inputs, specified order and
stop behavior, and correspondence with the public Haskell implementation.
Keep the optimized interned core. Retain older constructor and equality work
as secondary targets. Preserve repairs, counterexamples and marked drafts.

The strongest whole-system semantic claim remains conditional checked
rendered soundness under its semantic and resource contracts, fixed PCS and
whole-state Discharged. Greater recursive capacity retains ordered output
prefixes with the required budgets. The terminal chosen-model callback keeps
the same original assignment. DONE does not imply Discharged. A configured
stop can emit partial results. Whole-language completeness remains open.

Existing finite-capacity resource bounds retain the same old bound, outcome,
resources, all-extra stability and admitted histories. Every output and
concrete Cached payload in returned stop diagnostics retains original
recursion keys at the same raw slot. This includes nested failures and runs
with no output. It gives key membership, not a strict global rank.

## New exact result

The previous result bounded actual successful intersection values. The new
result bounds complete Mu bodies throughout every finite kernel outcome.
This includes exhausted, failed and pending-construction outcomes.

Let L be the original source ceiling. Let R be the original request's least
successful semantic fuel. Kernel.node_lower proves:

```text
Lower current.heap (L + R) (Kernel.execute runtimeFuel request current).state.heap
```

Lower quantifies every complete Mu record at its exact key. Such a record is
either the exact record in the input heap, including its complete payload,
or its body has open-binder degree strictly below L + R.
It covers all complete records in the reached heap, including probe records.
It supplies no bound on the number of records or on incomplete reservations.
The degree is open stored-plan binder depth. It is separate from cached
Value.depth, term height, enumeration rank and a global unfolding rank.

The statement retains original NodeScope and semantic Completes, original
Facts and Bounded source L, current Valid and NodeReady, source growth and
issued history, current SemanticHeap and body/probe open-depth equality.
It assumes no current-heap ceiling, future body bound or successful return.
Natural induction on actual runtime fuel closes every recursive hypothesis.

Lower.mono and Lower.trans retain exact old-record alternatives. Generic
result_bind_lower and walk_lower retain earlier effects when a later call
fails. Successful children derive the next heap invariants from the already
closed degree theorem and actual checked execution. Each original semantic
child has smaller required fuel. In the Mu branch, this decrease pays for
MaybeMu.lower's actual body-degree-plus-one bound. That constructor theorem
includes probes and pending construction. No future-result supplier remains
in node_lower or row_lower.

Kernel.closed_roots_lower derives one bound before all runtime-fuel and later
heap observations. Kernel.closed_roots_cold_bounded starts the constructor
heap at the original source. It derives the original finite source ceiling
and proves Bounded for every complete Mu body in every finite outcome.
No bound on future cached bodies is an original input premise.

Native.node_return_lower and edge_return_lower transfer this result to the
exact heaps of actual checked native returns. They use existing successful
native-to-kernel replay and retain WordRanges. Native.closed_roots_return_lower
derives one original-input bound for every checked closed-root return.
Native.closed_roots_cold_return_bounded bounds every complete Mu body in
such a returned heap when the constructor heap starts at the source.
These native statements require an actual DONE equation. They do not cover
arbitrary yielded or blocked native prefixes. Native denotes the Lean model
of the implementation. Full Haskell correspondence remains a separate goal.

## Sources and verification

Nine additive modules contain 16 public theorems, 836 lines/58,130 bytes:

1. InternedStoredPlanBinderDepthLowerAlgebra
2. SourceRecursiveIntersectionKernelLowerSequencing
3. SourceRecursiveIntersectionKernelMuLower
4. SourceRecursiveIntersectionKernelUnionLower
5. SourceRecursiveIntersectionKernelEdgeLower
6. SourceRecursiveIntersectionKernelRowsLower
7. SourceRecursiveIntersectionKernelReturnLower
8. SourceRecursiveIntersectionKernelClosedLower
9. SourceRecursiveIntersectionNativeReturnLower

No new runtime definition or exported predicate is added. All ten final
sources, including Audit, pass warningAsError and all linters. Audit checks
82,108 theorem dependencies in 4,633 jobs. The old imported unused-variable
warning remains visible in the default build. No suppression, custom axiom,
placeholder or native_decide is added.

There are 23 completed compiler commands: 21 PASS and two failed drafts.
The edge mismatch draft used a reflexivity proof with an insufficient
simplification. Its replacement reads the unchanged node-record projection.
The first closed-root draft used the wrong namespace for maximumDepth.
Both failed sources and raw logs remain. All 160 exact command input snapshots
match. Jobs run serially with measured 4 GiB max/high and zero swap and a
five-minute cap. No diagnostic timeout or Haskell/native suite runs here.

Public readback has 890 theorem checks/axiom lists and 73 old definition
bodies, 3,691,779 bytes. SHA256:
`b23355ece0ebb608477299ec28002fe31ca33d7f0dd01b952ab355f4fc39d6c0`.
The prior 3,654,083 bytes remain an exact prefix. All 37,696 new bytes were
read. All 4,623 old non-Audit Lean, 461 stronger source and 829 Haskell/Cabal
identities remain. Only additive imports change Audit. All earlier document
bodies remain exact suffixes. Earlier frozen evidence remains unchanged.

The union and row source-only reports retain their original UNTESTED status.
Their exact submitted versions subsequently passed root's strict checks.
Their source scopes are separate from whole input hashes. The union task
records two whole source acquisitions; the row task records five. Both are
within the task limit of eight. Other reads remain exact cuts.
The native-prefix audit records eight individual whole-file requests,
including two corrective rereads. Seven distinct sources were acquired in
full, including one assembled from cuts. Its exploratory truncations are
disclosed. Corrected complete reviews and all exact source cuts remain.

## Biggest gap and next proof

The next gap is allocation bounds through all stopped native prefixes.
Evaluation and the existing native_node_correct bridge describe completed
returns. A yielded or blocked native run needs a concrete prefix invariant
that retains actual continuations and constructor/memo states.
Native fuel exhaustion yields residual code. Kernel fuel exhaustion returns
failed exhausted. These are different observations.
The source audit identifies a specific obstacle: current Safe and Below
reject finishNode and finishEdge, although a memo miss creates those frames.
They cannot serve unchanged as invariants of all residual native code.
The native-prefix-audit report is source analysis, not a checked theorem.

Next, derive a prefix Lower observation for the actual initial request and
its compiled body. Decompose actual bind prefixes. Derive completed child
value bounds from the closed return theorems. Use MaybeMu.lower at actual
optional-binder effects. Account for absent/busy memo stops, finish frames,
exhaustion and blocked construction. Preserve the exact reached heap.
Do not introduce an assumed family of future body/value bounds.

Later generated queries can have operands outside original NodeScope.
Their lineage and an accumulated original-source invariant remain open.
A separate per-query bound does not give one fixed global enumeration rank.
Body degree alone does not bound allocation cardinality, guard growth,
fresh handles or word ranges. Sufficient recursive capacity and nonterminal
chosen-value coverage remain open. Complete policy/origin/public API
contracts and Haskell correspondence remain open. The new document edits,
language merges, canonical export and checkpoints need formal contracts.
No completion percentage follows from the present evidence.

## Haskell findings and restart

This increment changes no Haskell source and establishes no new Haskell bug.
FINDINGS retains serialization repair
`c15021ce706ef560b6c0ab335ceed1a4b67ba4aa`, its exact helper and two call sites,
four malformed fixtures and lawful-codec reproduction for external pickup.
Main ef0a2f32 still lacks checkedPathClass. The prior integration passes
383 core, 56 serialization and 30 Sized/checkpoint examples. The upstream
HugeLists import fix, both example checks and formatting evidence remain.
Those checks are historical implementation evidence, not correspondence.

Read NEXT-PROMPT.md, HANDOFF.md, FINDINGS.md and this note. Refresh upstream
with an ff-only pull and the command-local SSH 443 override when needed.
Preserve all earlier repairs, counterexamples and their exact scopes.
The 22-step open-body witness remains unprepared. A returned .mu26 tag proves
neither payload equality, degree-ceiling failure nor divergence.

Complete evidence is in lean/restart-evidence/20261029-kernel-lower-progress/.
The manifest and standard-library verifier bind every retained payload.
Board 734 has exact author, content, metadata, type and thread readback.
Use a fresh writable directory after sealing. Push formalize regularly under
the existing authorization. Keep the full formalization goal ACTIVE.
