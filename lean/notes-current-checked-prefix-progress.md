# Checked query prefix bounds and current tuple-budget emptiness

Verified checkpoint: 2026-10-29 20:57 CET. Branch: formalize.
The full formalization goal remains ACTIVE and unbounded.
Source: 20a4595247b497b1242707325ddf03dc101a92d4.
Checked query proof: b3fbf0855207047b67b5bbd0390727f469bd0a6e.
Main 7b8db072fbde44f20ce9a803736de5624050f038 is integrated at
ec6d21f68ee7e7ff702a4c8edbff413d802766d7.
The previous published checkpoint was 9da1fef0499e9b97bc06df6146c18bbc8412fd4e.

## Full objective and strongest claim

Prove sound outputs, intended finite-value coverage, resources from the original
input, sufficient recursive capacity, exact order and stop behavior, and
correspondence with Haskell. Keep the optimized interned core. Preserve the
older constructor and equality targets, repairs, counterexamples and drafts.
A local passing theorem does not complete this objective.

The whole-system semantic claim remains conditional checked rendered
soundness under the semantic and resource contracts, a fixed PCS, and
wholeDischarged. Greater recursive capacity preserves the existing ordered
prefix under its stated contracts. The terminal chosen-value callback retains
the same original assignment. DONE is distinct from Discharged. Configured
stops can return partial results. Membership does not establish strict global
size order or rank/unrank inverse laws.

The strongest new local claim concerns the actual checked native interpreter.
For each admitted closed query, one finite bound covers every complete Mu
body's stored-plan binder degree at every runtime-fuel observation. The bound
is selected before the universal fuel quantifier. It includes the query-entry
heap and every later returned heap. It does not bound handle count or memory.

## Actual checked query theorem

SourcePruningEnumerationIncomingQuery.native_prefix_bounded is in
MicroCFTA/SourcePruningEnumerationCheckedQueryPrefixBounded.lean.
Its inputs are the original Profile, Context, current operand Available and
closedness, Fits, and Room. The conclusion is an existential Bounded ceiling
for SourceEqualityNativeDemand.execute on the literal requestNode emptyDomain
left right at beforeCaller.checked, for every nativeFuel.
There is no public DONE premise, supplied trace, later heap bound, or future
body-degree supplier. The theorem derives the finite physical query trace
through the existing TargetQuery.finite producer. Its original numeric and
semantic admissions remain explicit.

Trace.prefix_bounded proves the local intermediate result. Each physical
step derives the next PhysicalCache.Valid and RequiredCache.Ready. Trace
induction takes the maximum of the current heap's finite inventory ceiling
and the tail ceiling. A completed pure control has the same state for every
larger fuel. No conversion from weak physical caches to eager thunk validity
is used. The exact checked states remain in the trace.

This resolves the previous proposed per-query interface. The older source-only
recommendation for a duplicate checked semantic-rank induction remains as a
dated report. That route is unnecessary for this existential result. It can
still be useful for an explicit sharp formula. The new ceiling depends on the
derived completion trace. It is not proved equal to L + semantic requiredFuel,
a Profile formula, or a cheaply computed forecast.

Each next query enters at its actual current heap. Inventories can rebase to
that heap. The new theorem does not give one ceiling fixed at generator
startup across all later queries. An admitted completed query cannot also
have a stable error or blocked observation from the same entry. No theorem
for malformed starts outside the admissions is added.

The previous sharp all-outcome bounds for SourceRecursiveIntersectionNative
remain unchanged. Their L + semantic requiredFuel result concerns the bare
interpreter and has its own source, scope, range and semantic premises.
Do not identify that interpreter with SourceEqualityNativeDemand.

## Main PR 193 and current emptiness model

PR 193 counts raw edge tuples instead of admitted conjunctions. Its default
budget is 10000. Empty, exhausted, open and repeated inputs precede sampling.
The sample is take (remainingBudget + 1) of edgeTuples. The count includes
contradictory tuples. Overflow inserts no entry and drains the queue at budget
zero. A fitting sample is complete and subtracts its full count. A zero-tuple
product inserts an entry with no rows and consumes no tuple budget.

Four additive modules model this behavior:
SourceCurrentConjunctionTupleBudget,
SourceCurrentConjunctionTupleBudgetSoundness,
SourceCurrentConjunctionTupleBudgetCompletion, and
SourceCurrentConjunctionTupleBudgetDecision.
They retain the existing source tuple order, equality combination, path
requirements and finite-table semantics. A fitting sample equals the full
tuple list. Overflow stays outside the table and remains possible.

run_complete derives a finite Run for every finite input table and queue.
Strong induction on the remaining budget handles positive charges and
overflow. List induction handles skipped heads and zero charges. A zero
charge gives no rows, so it generates no new pending requirements.
complete also derives the literal equality-stop grow result within the
actual final table length plus one comparisons. Run.answer_sound links the
completed canonical result to the public closed guard and possibility test.
A True verdict excludes every accepted finite term under the explicit empty,
exposure, path-projection and key-faithfulness laws. False proves nothing.

No final-table soundness oracle or Run-existence oracle is added. These are
finite extensional source-algorithm results. They do not prove that the Lean
evaluator avoids a full Cartesian product, derive a lazy Haskell execution
trace, or supply the new physical cold-exposure allocation schedule.

The older Worklist, Worker, Decision and WorklistResources definitions count
conjunctions and remain historical targets. Their old public definitions and
proofs are unchanged. Zero-charge entries prevent direct reuse of the old
total-table-length accounting argument. No physical-validity counterexample
to every possible sharper bound is claimed. The old budget + 1 grow proof
must be replaced or re-established for the new table family. The new proof
uses final.length + 1. It does not give that length from original resources.

## Haskell changes and external pickup

The upstream runtime fix and its constrained recursive regression are in
517448a42, merged by main 7b8db072f. The integrated source preserves both.
The local Haskell change repairs two Haddock statements in Enumeration.hs.
The main paragraph states the maximum raw reads as emptinessBudget + 1.
The budget comment states that one extra tuple detects overflow.
These are documentation changes. The entire file equals the tested upstream
file after exactly those two comment replacements. FINDINGS records both
for external pickup. No functional Haskell defect was established here.
The earlier parser repair c15021ce706ef560b6c0ab335ceed1a4b67ba4aa and all
probe-freshness repairs remain in the earlier findings and evidence.

## Verification and preservation

All five new modules and the exact final Audit source pass strict Lean with
warningAsError and linter.all. No axiom, sorry, admit, native_decide, or linter
suppression was added. Aggregate Audit passes 4650 jobs and checks 82182
theorem axiom dependencies. The unchanged older unused-variable warning can
appear during Lake replay. The six final strict sources have no warnings.

The public readback contains 927 checks and axiom lists, plus 77 printed
definition or inductive declarations. Its 3774276 bytes have SHA256
1f85e9559c9bc36e4cfda64f65a650c525f77656096e001d34ff4e4b7aa14307.
The previous 3751130 bytes are an exact prefix. All 23146 new bytes were
reviewed without truncation. All 15 new theorem axiom lists contain only
standard Lean axioms. The 73 older definition bodies remain in the prefix.

The Nix core suite passes 384 examples with seed 492294335, including the new
constrained recursive regression. GHC is 9.14.1 with -O0. Final changed-file
Fourmolu and cfta.cabal gild checks pass. The gild --input deprecation remains
an observation. No new local Haskell test was added. The native raw output
and integrated inputs are retained. The raw native log was read selectively;
no whole-log read is claimed. No broader test rerun was needed.

All 4644 previous non-Audit Lean files and 461 protected source identities
remain unchanged. Of 829 Haskell/Cabal identities, 827 are unchanged. The only
changes are the two upstream paths, with the two local comment replacements
in Enumeration.hs. The compiler and native checks use a serial 4 GiB memory.max/high cap,
zero swap, and a five-minute limit. There are 23 recorded checked commands:
15 pass and 8 retain failed attempts. All 107 command input snapshots match
their retained copies. The failures concern candidate names, documentation,
and import placement. Exact final strict mappings supersede failed drafts.

## Evidence and restart

The complete writable source area for this checkpoint is
/tmp/mcfta-checked-prefix-progress-20261029. It will be sealed read-only and
archived without filtering at
lean/restart-evidence/20261029-checked-prefix-progress.
The previous native-prefix areas and reconstructions remain immutable.
The source-only reports retain their original UNTESTED labels. The final
check map identifies the exact checked sources. Two source reviews retain
literal cut and whole-source provenance. One expected current-input hash
change in the tuple review is the documented Haskell comment repair.
Exploratory combined output was sometimes truncated. Required contracts,
final reports and the new public readback were read again without truncation.
No whole-source claim is based on a truncated read.

Read this note, then the top of FINDINGS, HANDOFF and NEXT-PROMPT. Check live
branch, worktree, remote and upstream before edits. Pull before new work.
Keep frozen areas immutable and continue in a fresh writable evidence area.
Use heavy-management for serial Lean and Nix jobs. Do not repeat passing
checks without a new source change or unresolved concern. Push only formalize
to git@github.com:TharkunAB/cfta.git under the standing explicit authorization.
SSH 443 with HostName ssh.github.com and HostKeyAlias github.com works when
port 22 stalls. Confirm the remote head and clean worktree after publication.

## Biggest gaps and next work

First derive one original-input resource and recursive-degree bound across
the generator's successive admitted queries. The checked per-query theorem
now exists, but rebasing its source does not make its ceiling uniform.
Connect that result to the admitted finite model and size resources.

For PR 193, add bounded tuple observation to the actual cold physical
exposure/row pipeline. Preserve the reached heap and skip tuple equality and
projection work on overflow. Account for zero-charge admissions and the
pending requirements generated by positive charges before reusing worker
allocation or grow bounds. The old eager full-row worker is insufficient.

Full nonterminal chosen-value coverage, strict global size order, rank/unrank
inverses, public API and policy/origin bridges, and Haskell execution
correspondence remain open. There is no reliable completion percentage.
Continue the full goal. Do not pause or mark it complete at this checkpoint.
