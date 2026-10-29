# Current proof state: diagnostic ancestry

Checkpoint: 2026-10-29 02:30 CET. The full goal remains ACTIVE.
Source `49169700142d3f587e64ffe4398616e4aba33e90` is pushed to `formalize`.
Read this note before the older dated checkpoints.

## Top-level objective and current claim

The objective is an end-to-end proof of the constrained language generator.
The proof must establish sound outputs and coverage of intended finite values.
It must derive sufficient resources and recursive depth from the original input.
It must preserve the specified order and stop behavior.
It must connect the formal operations to the public Haskell implementation.
The optimized interned core remains the primary target.
The older constructor and equality results remain secondary targets.

The strongest semantic claim remains conditional checked rendered soundness.
It uses the stated semantic and resource contracts, a fixed path constraint set,
and whole-state Discharged. Greater recursive capacity retains the ordered
output prefix when the required work budgets are supplied. The terminal
chosen-model callback result retains the same original assignment.
DONE does not imply Discharged. A configured stop can emit partial results.
The public Haskell system does not yet have an unconditional end-to-end proof.

This checkpoint strengthens the structural theorem for finite recursive runs.
For each finite recursive capacity, the original resource contracts give a
sufficient work bound and an actual outcome that is stable at every larger
work budget. The SAME old bound and outcome retain all old resource fields
and every admitted output history. Every emitted output retains every
original recursion key at the SAME RAW SLOT. The new theorem also establishes
that property for the concrete enumeration-cache payloads in returned stop
diagnostics. It includes nested continuation failures and runs with no output.
It adds no original input gate and no future-retention supplier.

This is recursion-key membership. It does not establish order, multiplicity,
strict decrease of a global rank, transfer between different representatives,
or a sufficient recursive capacity. A fixed slot and fixed handle give the
earlier unused-budget nonincrease result. They do not give a moving-root rank.
Sibling alternatives reset their captured enumeration cache. Their native
caller and memo state advance. Do not chain sibling output caches as inputs.

## Concrete diagnostic property

The namespace is `SourcePruningEnumerationPreparedRecursive` unless stated.
All five new definitions have concrete Prop bodies.

- `ReceiptAncestry` checks complete, rejected and stopped-with-cache receipts.
  An unhandled receipt or a missing cache contributes True.
- `PrefixAncestry` checks parked and narrowed selected results. It also checks
  each retained ordinary-branch receipt and its current stopped receipt.
- `FailureAncestry` checks exhausted and selected snapshots. For alternatives,
  it checks processed receipts, the current receipt and each nested failure.
- `OutcomeDiagnosticAncestry` applies that property to a stopped HookResult.
  A complete outcome carries no stop diagnostic and contributes True.
- `CompleteWithDiagnosticAncestry` adds this diagnostic property to the old
  finite-recursion resource contract. Its `complete` theorem projects the old
  contract without changing its original arguments.

The separate output theorem covers outputs of complete and stopped outcomes.
The diagnostic definitions do not claim ancestry for raw Core observations in
callback/preparation errors. Those values are not Cached enumeration payloads.
The theorem does not claim retention for every discarded internal cache.
Storage, child and head observer theorems remain separate local results.

## Closed producer proof

The proof derives receipt ancestry from actual captured and opaque run
equalities. The receipt helper has a local retained-receipt argument. Its
parents discharge that argument from those actual observations.
The final theorem has no corresponding extra premise.

The parked helper derives prefix-history equality from the original Packet's
Total field and actual prefix validity. Callback framing uses its own completed
Packet. The head, ordered sibling scan, finish, ordinary preparation and opaque
dispatch helpers preserve the original resource tuples. The sibling proof
retains every actual processed receipt and every actual current stop payload.
It does not replace a preceding rejected alternative with the chosen later one.

The selected-step proof composes actual prefix and preparation transitions.
The run proof closes the successor case. Natural-number induction closes the
strengthened recursive contract for every finite capacity. No recursive
diagnostic oracle remains as a final input.

`run_finite_complete_resources_with_all_cache_ancestry` combines this closed
diagnostic result with the previous output-history/ancestry theorem. It compares
the two actual runs at the sum of their work bounds. Their outcomes are equal.
The theorem then retains the OLD resource theorem's bound and outcome. It does
not enlarge that bound or add a new original gate.

The 14 additive modules are:

1. `SourcePruningEnumerationDiagnosticAncestry`
2. `SourcePruningEnumerationPreparedDiagnosticContract`
3. `SourcePruningEnumerationPreparedDiagnosticParkedResources`
4. `SourcePruningEnumerationPreparedDiagnosticCallbackResources`
5. `SourcePruningEnumerationPreparedDiagnosticReceiptResources`
6. `SourcePruningEnumerationPreparedDiagnosticHeadResources`
7. `SourcePruningEnumerationPreparedDiagnosticSiblingResources`
8. `SourcePruningEnumerationPreparedDiagnosticSiblingFinishResources`
9. `SourcePruningEnumerationPreparedDiagnosticOrdinaryResources`
10. `SourcePruningEnumerationPreparedDiagnosticOpaqueResources`
11. `SourcePruningEnumerationPreparedDiagnosticExpansionResources`
12. `SourcePruningEnumerationPreparedDiagnosticRunResources`
13. `SourcePruningEnumerationPreparedDiagnosticFiniteResources`
14. `SourcePruningEnumerationPreparedAllCacheAncestry`

They contain 23 public theorems and five definitions in 2,225 lines/153,422 bytes.
No private proof helper was authored. Lean generates a recursive body for
`FailureAncestry`; its complete printed body was checked separately.
Only additive imports change the old Audit source. Every earlier Audit byte
remains an exact suffix. No old runtime function or old proof body changes.

## Verification and retained attempts

All 15 final source files, including Audit, pass warningAsError and all linters.
Audit checks 82,040 theorem dependencies in 4,613 jobs. Its default build still
shows the old unused-variable warning from InternedFreshOrdinaryClosedCompletion.
No linter suppression was added. No custom axiom, placeholder or native_decide
was added.

There were 37 actual compiler commands: 33 PASS and four failed drafts.
The failed versions are two base monotonicity proofs, the first sibling proof
and the first final outcome transport. All failed inputs and logs remain.
The base fix splits the actual nested stop constructors before constructing
the conjunction. The sibling fix uses explicit proof-term parentheses and
splits the actual stop constructor. The final fix rewrites the proved outcome
equality directly. No diagnostic definition or runtime behavior was weakened.

Every compiler command ran serially at measured memory.max=memory.high=4 GiB
and memory.swap.max=0, with a five-minute cap. All 368 per-command input
snapshots match their recorded hashes. The final strict source mapping contains
exactly the 14 new modules and Audit.

The main public readback contains 856 theorem checks and axiom lists, plus
73 definition bodies, in 3,609,022 bytes. SHA256:
`90f6ea43f27a796e9ecbd3d679a01a41e1e6b17f57f61698352d2e471ef59405`.
The old 3,473,780 bytes are an exact prefix. All 135,242 new bytes were read in
eight retained parts. The generated `FailureAncestry._f` body adds one separate
2,392-byte readback. It is not included in the main 73-body count.

All 4,598 old non-Audit Lean sources, 447 earlier stronger sources and 821
integrated Haskell/Cabal identities retain their hashes. The 24 earlier current
documents retain their complete bodies as exact suffixes below a new header.

Source-only evidence retains the reviewed ranges. Eleven base source snapshots
include one whole-source read and ten partial source reads. Nine sibling source
snapshots retain the four old producer reads and the listed supporting ranges.
The callback evidence verifies three complete header transformations. It retains
seven source records and 17 files. The next-rank audit retains seven whole Lean
reads, nine literal cuts, one whole prior report, 16 existing signatures and
21 files. A historical first-version ancestry input remains identified as such.
Complete source copies are not claims that every copied line was reviewed.

Board sequence 725 records this proof result. Its author, content, metadata,
type and thread match the saved request exactly. The full goal is ACTIVE.

## Biggest gaps and next proof target

The main gap remains an original-input bound for actual generated native work.
The source-only next-rank audit narrows that obligation. Its proposal is
UNPROVED. It is not an installed Lean statement or a new assumed contract.

`SourceRecursiveIntersectionRequestProgress.initial_complete` already derives
semantic completion for the cited original closed-root requests. It uses the
original Facts, Original, Available and closed-root gates. No semantic completion
oracle is needed for that particular result. `CompileMuBounds` also proves
strictly smaller semantic request fuel for actual original-scope Mu children.

Those facts do not bound the syntax degree of a generated native return.
`CodeBounds.Below` accepts arbitrary available returned values in continuations.
Its optionalBinder case retains a request bound without an output-degree fact.
The pending binder uses the ACTUAL returned body, not an original operand body.
Available proves residency/provenance. It does not identify that generated body
with a subtree of the original syntax.

The next target is a joint proof for actual request returns, ordered child
returns, optionalBinder construction and memo publication/readback. Derive a
body bound from the SAME original source and its already derived request fuel.
Do not assume the desired bound on each future callback body. The retained
proposal starts with empty native memos. Warm-memo provenance and later queries
on generated operands require further work. A per-query bound recomputed from
a growing heap is not a fixed original rank for the whole enumeration.

The same startup-only Mu ceiling remains unproved. No admitted counterexample
to that ceiling was established. The earlier 22-step OpenBodyBoundary witness
refutes universal first-order preparation under its exact gates. It proves only
returned=some(.mu26) for its bounded native reference observation. It proves no
literal payload/cache equality, divergence or failure of the proposed degree
bound. It supplies no prepared whole-Packet counterexample.

A degree bound also does not count canonical handles or generated guards.
Different keys at the same degree can contain different generated probes.
Prove the required key/guard closure or use a different well-founded rank.
Earlier startup-only identity and decreasing cached-depth counterexamples remain
valid for their exact, different claims. Preserve those counterexamples.

Nonterminal chosen-model emission and sufficient recursive capacity remain
open. Current assignment origins give a non-strict term-height bound. Empty
equality classes can reuse the current term. A chosen later constructor cannot
justify ignoring earlier ordered callbacks and rejected alternatives. The proof
must cover those actual operations before it can derive a whole-run bound.

Complete policy/origin contracts, the public API and physical Haskell
correspondence remain open. These are central end-to-end proof obligations.
The ancestry result closes a structural prerequisite. It is not a percentage
estimate for completion of the full formalization.

## Haskell repair for external pickup

No Haskell source changes, new Haskell defect or Haskell check occurred here.
FINDINGS retains repair `c15021ce706ef560b6c0ab335ceed1a4b67ba4aa`.
Main `63aae675c5c6b8312bc5872fff065a7de3629aef` still lacks that repair.
It is on formalize and remains available for external pickup.

The lawful codec `StateCodec id Right :: StateCodec Text` accepted graph text
whose class contains a path and its strict extension. The parser then threw in
toPathTrie. The minimal input is
`graph 1; start S; state S { a where equal([], [0]); }`.
The shared checkedPathClass now deduplicates paths and rejects adjacent sorted
strict-prefix pairs before the partial PathEClass constructor. Both parser
branches use it. Four malformed root/nested equal/class variants return Left.
Four valid controls remain Right. Prior validation passed all 19 serialization
examples with -Werror and the recorded formatter, lint and package checks.
Those checks were not repeated without a Haskell change.

## Restart and immutable evidence

New writable evidence: `/tmp/mcfta-diagnostic-ancestry-progress-20261029/`.
The repository archive is
`lean/restart-evidence/20261029-diagnostic-ancestry-progress/`.
It retains source snapshots, failed drafts/logs, exact public readback,
review scopes, resource measurements, current documents and board readback.
The archive verifier checks every payload hash before reconstruction.

Preserve this source area after sealing. Preserve every earlier evidence,
packaging and restored area. Use NEW writable paths for further work.
The previous checkpoint is `20261029-recursive-ancestry-progress` at
`c2e0865123bd0feab997142046e626457bc43f74`.

Refresh upstream before new repository work. Preserve all local proofs and
counterexamples. Main was unchanged at the current refresh and is an ancestor.
Normal pushes to git@github.com:TharkunAB/cfta.git refs/heads/formalize remain
explicitly authorized. Keep source commits small and push checked progress.
Use serial measured heavy-management caps. Do not change queue concurrency.
Continue the whole objective without asking whether to continue.
