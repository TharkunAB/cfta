# Actual prepared ancestry and graph text parser repair

Checked at 2026-10-29 01:15 CET. Source `5eb88a239b05ee6ede5acb296b64ee0fe8616f02` is pushed on formalize.
The complete formalization objective remains ACTIVE and incomplete.

## Top-level objective

Show that the optimized implementation enumerates exactly the intended
constrained and refined tree language. Every emitted complete term must belong
to that language. For each intended finite term, derive sufficient bounds that
make the actual search emit it. Preserve the specified order, resource and stop
behavior. Connect the public API and concrete Haskell representation to the
model. An infinite language does not require one finite exhaustive run.

The optimized interned core remains primary. Preserve the earlier constructor
and equality proofs as secondary targets. Derive required bounds and admission
from the original input and branch model.

## Current strongest statement

The optimized interned Lean model has conditional checked rendered soundness
under its semantic/resource contracts, fixed-PCS and whole-Discharged. Greater
recursive depth retains the ordered output prefix. Its finite prepared worker
retains resources, histories, proper/canonical storage, arity and projection
under the original gates. Earlier work constructs the actual terminal callback
emission with the same original assignment. DONE does not imply Discharged.
Configured stop can emit a partial result.

This checkpoint adds actual per-slot recursion-key retention through the local
prepared pipeline. It adds no whole recursive coverage or sufficient recursive
depth theorem. Native generated-query closure and physical Haskell equivalence
remain open. The new text serialization API is evaluated and integrated, but
its grammar and round-trip laws are not proved in Lean.

## Exact new relation and budget scope

`SourcePruningEnumerationAncestryExtension.Extends before after` states that
every recursion key in `before.recursionAncestry slot` also occurs in
`after.recursionAncestry slot`, for every Nat slot. It includes old keys at the
next fresh counter. It does not require valid, allocated or canonical slots.
It does not preserve list order, multiplicity or literal list equality.

The base lemmas give reflexivity, transitivity, complete compression framing,
actual allocation and actual assimilation. Allocation unions the fresh slot's
old keys with the expansion keys. Assimilation retains old target keys and
does not remove the old source history.

`Extends.unused_le` derives nonincrease of the unused original shape count at
one FIXED native handle and one SAME RAW SLOT. It supplies no strict decrease,
native-handle cardinality bound or representative change. Earlier Entry budget
work separately proves strict consumption at the checked handle and inheritance
by a directly allocated child. A child's own encoded handle can differ.

If a later argument follows a different live representative, use the actual
source-to-target transfer from `CachedAssimilation.finish_ancestry` plus the
real representative/handle facts. Per-slot extension alone is insufficient.
Each sibling starts from its captured enumeration cache. Native callers and
full Memos advance. Do not compare a previous sibling's output cache with the
next sibling's reset input as one globally monotone branch.

## Actual local pipeline now checked

Eleven additive modules contain 33 public theorems, one Prop predicate and six
private proof helpers. They total 1,295 lines and 70,783 bytes. They change no
enumerator or native function definition.

1. `SourcePruningEnumerationAncestryExtension` defines membership retention and
   proves the six base/budget lemmas.
2. `SourcePruningEnumerationAncestryExtensionStorage` observes actual indexed
   writes, allocation, old-slot replacement and ordinary child preparation.
3. `SourcePruningEnumerationAncestryExtensionOwn` observes own-class allocation,
   each returned shallow child row, attached caches, finalization and residual
   recording. Finalization derives expansionAncestry=[].
4. `SourcePruningEnumerationCachedAdapterAncestryExtension` observes actual raw
   dispatcher singletons and optional recovered caches separately. Adaptation
   returns the original core or the actual raw singleton core. Neither is
   silently equated with a different raw/cache endpoint.
5. `SourcePruningEnumerationTerminalPrefixAncestryExtension` observes the real
   representative scan and unions. They change only the forest.
6. `SourcePruningEnumerationFoldAncestryExtension` follows the actual ordered
   dispatcher fold and attached cached-fold endpoints, including rejection.
7. `SourcePruningEnumerationIncomingAncestryExtension` observes actual paired
   assimilation writes, incoming read cores, successful singletons and recovered
   incoming caches. The adapter and raw branches stay explicit.
8. `SourcePruningEnumerationTerminalAncestryExtension` composes the real prefix,
   cached fold, raw singleton identification and incoming adapter. No recovered
   cache means the actual uncached path; it does not invent an attached cache.
9. `SourcePruningEnumerationChildAncestryExtension` covers Empty rejection,
   shallow preparation and the actual terminal path.
10. `SourcePruningEnumerationTraversalAncestryExtension` composes the actual
    completed child trace. A stopped trace uses its real completed prefix and
    the attached cache from the stopping child.
11. `SourcePruningEnumerationPreparedHeadAncestryExtension` composes actual own
    preparation, children and residual recording. The captured complete case
    also observes finalization. Rejected/stopped attached caches retain exact
    input expansion ancestry. Completed captured caches clear it. The actual
    CompletedHeadReceipt supplies this result through `receipt.running 0`.

These local observers require their literal actual observations. They add no
carrier, model, finite-bound, semantic admission or future-retention premise.
The completed receipt corollary uses that actual receipt. It does not replace
the original producer's gates or prove global recursive success.

## Biggest gaps

The main global gap is a finite native generated boundary family, or another
well-founded rank derived from the original input. A fixed-handle shape budget
cannot bound the number of native handles. Queries can use generated operands.
Earlier source review identifies the generated callback body bound before
optionalBinder as a missing degree link. `build_new_lower` bounds a new Mu body
by the generated body. Current Bounded alone does not supply that generated
body's strict original ceiling. Even a degree ceiling still needs physical
probe-key/guard closure or a different justified rank.

Nonterminal chosen-model recursive emission remains open. The actual terminal
callback emission theorem is retained. Source-derived sufficient recursive
depth must also cover earlier allocating callbacks, rejected alternatives and
stopped diagnostics. Complete solver/policy/origin/public API admission and
the concrete optimized Haskell representation bridge remain separate work.

Existing counterexamples remain unchanged. SourceColdUnfoldNewMuBoundary
refutes startup-only Mu inventories and decreasing cached depth. The actual
22-step OpenBodyBoundary witness refutes universal PreparedWithoutMu. Its
native_returned theorem observes only returned=some(.mu26), not literal cache
or payload equality. Neither witness proves divergence or disproves the needed
original degree ceiling. Their historical missing /tmp logs remain marked as
missing; they are not represented as recovered evidence.

## Next local proof task

The frozen source-only `worker-next/REPORT.md` in this evidence area gives exact
proposed interfaces and a complete/stopped case map. These are planning
interfaces, not installed or checked declarations. It preserves 49 whole
source identities and distinct source-read cuts. A copied whole source is not
a claim that its whole proof was reviewed.

First prove valid-prefix recursionAncestry equality for every actual retained
prefix tag under original Total and literal PrefixValid. Full Frame is too
strong: a repeated check clears a bucket and narrowing can write a value.
The actual actions are reject, pure, or representative plus setValue. Reuse
the PrefixCanonicalHistory inversion; do not assume arbitrary action framing.

Next prove the actual SelectedOpaqueDispatch all-cache observer. Use the new
child observer and finalizer for complete, rejected and stopped Some caches.
Then reuse Entry.enter_history. Original Total gives exact per-slot equality
at actual Entry; Entry changes expansion ancestry. Compose the selected
preparation and actual ordinary/opaque receipt into
SelectedHistoryReceipt.ancestry_extension.

After these bridges, ResourceHistory.ancestry_extension can give output-only
retention. Its existing original-input producer already closes the finite
depth contract. It binds each callback to THAT head's own Packet/cache and
derives callback Frame from actual admission. Compose the real prefix, receipt,
callback Frame and tail history. No new model or future-output supplier is
needed for this proposed structural result.

Attached stopped caches require additional work. A HookResult.stopped has an
optional native endpoint, not one aggregate cached enumeration endpoint.
Define a Prop relation for Cached fields actually present in Failure/receipt
diagnostics. Include exhausted, selected, processed alternatives, current
receipts and nested continuation failures. Callback/preparation raw Core rows
are a different scope. Keep missing candidates and native endpoint None.

Strengthen the actual finite producer with output and diagnostic retention,
then close it by recursiveFuel induction. Each callback uses its own
receipt-derived input Packet. Each sibling uses the fixed captured cache while
the actual Caller/full Memos advance. Derive all local retention from the real
observers. The final theorem must have no hook-retention supplier premise.
The proposed producer is stable at sufficiently large work fuel for each
finite recursive capacity. Arbitrary smaller-work observations need a separate
reachability argument. This next theorem still would not prove a sufficient
recursive capacity for an intended result.

## Main integration and Haskell repair

Origin/main is 63aae675c5c6b8312bc5872fff065a7de3629aef, merged at
e216346905cfeb0b243799138b4c254a739de0aa. PR188 adds optional
cfta-serialization graph text support and CI wiring. Stored graph constraints,
cycle structure, repeated alternatives and child order remain explicit. Lawful
state codecs are required. Notes for absent items are discarded as documented.
Parsing does not itself prove a language or invoke the solver.

Root reproduced a real exception with the lawful text codec
`StateCodec id Right :: StateCodec Text`:

```text
graph 1; start S; state S { a where equal([], [0]); }
```

Both equal(...) and explicit constraint(CLASSES,true) constructed PathEClass
before checking intra-class strict prefixes. Its strict trie throws toPathTrie.
Four root/nested inputs threw. Four valid controls returned graphs. The
existing suite passed before the additional malformed-input coverage.

Repair c15021ce706ef560b6c0ab335ceed1a4b67ba4aa is pushed on formalize.
The checked helper deduplicates paths and examines adjacent ascending paths for
a strict prefix before trie construction. Both spellings use it. Empty,
singleton and valid stored classes stay exact. Four cases extend the existing
malformed-input list. The format README states the representation restriction.
No core equality semantics change was made.

After repair: four Left results, four valid Right results and no exception in
the focused probe. The existing suite passes 19 examples, zero failures with
-Werror. Fourmolu, Cabal-gild, HLint3.10 and Cabal metadata checks pass. The
integrated baseline has 821 Haskell/Cabal identities: 819 stay unchanged and
two repaired Haskell files differ. All 817 inherited manifest identities remain
unchanged. FINDINGS.md records the exact cause, input, command and pickup.
Main does not contain this repair at the recorded head.

The first Nix attempt failed to link host libgmp. Prepending /usr/bin to PATH
restored the host linker while keeping Nix Z3 later in PATH. Its failure log
is preserved separately from the parser exception and all successful checks.
The focused probe catches exceptions and exits zero; assess its eight labeled
results rather than its exit status alone. The archived original/final source
copies and exact raw outputs make the distinction reviewable.

## Exact verification and failed attempts

All eleven new modules plus Audit pass strict warning-as-error/all-linter checks.
Audit builds 4,595 jobs and checks 81,958 theorem dependencies. The compiler
matrix has 28 commands: 25 PASS and three preserved failed drafts. All final
inputs pass. Five native commands have four PASS and one initial environment
FAIL. The eight-case pre-fix probe deliberately reports the reproduced defect.
One strict-wrapper path argument error ran no compiler. One evidence verifier
assumed optional byte lengths were present in the inherited Lean hash inventory;
its failed script and observed traceback are retained. The repaired verifier
checks every supplied byte length and every source hash.

The three Lean repairs change no premise: use an inferred reflexive state after
equality substitution, infer the actual incoming read core before applying the
expected conclusion, and split the actual stopped Option for match reduction.
All failed sources, raw logs and candidate versions remain. Root checked 318
exact command input snapshots. Each measured job used memory.max/high of
4,294,967,296 bytes and memory.swap.max zero. No cap increase, custom axiom,
native_decide, placeholder or linter suppression was added. The default build
replays one existing unused-input warning in unchanged
InternedFreshOrdinaryClosedCompletion; strict final sources are clear.

Installed public readback has 827 theorem checks/axiom lists and 68 complete
definition bodies. It is 3,454,104 bytes, SHA256
0192c4d3d92d5ec0096c40a14a0af058abebd6b5918265a8e0a78c7f1b6a8f70.
The prior 3,408,116 bytes are an exact prefix. All 45,988 new bytes were read
in four contiguous ranges without an omitted suffix. Permitted axioms remain
propext, Classical.choice and Quot.sound. All 4,583 prior non-Audit Lean and
432 stronger-source hashes remain. Audit retains its entire old body after
eleven imports. All 22 earlier document bodies remain exact suffixes.

Nine source-scope manifests verify 266 identity records at 226 retained paths.
Source scopes retain original author UNTESTED labels. Root's exact checked
final source hashes identify the compiled repairs. The storage manifest field
parent_reported_main names the integration commit, not origin/main; the
separate scope clarification and Git records give both exact identities.

## Publication and restart

Three proof commits end at `5eb88a239b05ee6ede5acb296b64ee0fe8616f02`. Source, tracking and remote formalize
heads match on git@github.com:TharkunAB/cfta.git refs/heads/formalize. The exact
main head is an ancestor. Normal formalize pushes remain explicitly authorized.
The shared msg-board notes are parser repair sequence717 and proof sequence
718, with exact author/content/metadata readback. Use the
msg-board skill for further project knowledge sharing.

Complete unfiltered evidence is in
lean/restart-evidence/20261029-prepared-ancestry-progress/. Its standard-library
verifier checks and reconstructs every sealed regular file from
/tmp/mcfta-prepared-ancestry-progress-20261029/. This includes failed drafts,
all raw logs, input snapshots, original/final Haskell sources, public readback,
source scopes, the worker-next planning report, measurements, prior/final
documents, Git records and exact board requests/readbacks. Use a fresh extract
destination. Keep frozen/restored areas immutable.

Read this note and the front matter of NEXT-PROMPT.md,HANDOFF.md and FINDINGS.md.
Continue in a NEW writable directory. Refresh upstream while preserving proofs,
counterexamples, repairs, marked drafts and older archives. Keep compiler/native
jobs serial at the measured 4 GiB cap. Reuse passing checks unless inputs change.
Do not pause or mark the goal complete at this checkpoint. The full objective
remains ACTIVE and incomplete. Continue without asking whether to continue.
