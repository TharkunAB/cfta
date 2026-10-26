from pathlib import Path
import json
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-incoming-language-20261026')
commits=json.loads((area/'source-commits.json').read_text());checked=json.loads((area/'verified-checks.json').read_text())
block=f'''## Actual incoming-node branches now have exact assignment meaning

Native handle and pending-write semantics: `{commits[0]['commit'][:9]}`.
Actual incoming producer and branch language: `{commits[1]['commit'][:9]}`.
The goal stays ACTIVE. H6 remains the strongest end-to-end language theorem.
Main `6c080537a` remains imported. All earlier Haskell repairs remain merged.

The original incoming-node admission now derives exact complete-assignment
meaning at the actual returned native heap. A returned branch accepts an
assignment exactly when the original state, incoming node and incoming
suspended constraints accept it. All old suspended constraints, aliases and
residual guards retain their meaning. Empty rejection has no accepted
assignment. Its logical write receipt remains separate from runtime raw [].

Both wrappers retain the ENTIRE earlier producer result and call their
producer once. No final satisfaction, desired language equality, fake Graph
interpretation or new input premise is admitted. Native growth is compared
only for handles actually read from realized old slots. The enumeration
guard type remains independent from the native constraint type.

All four new modules and Audit pass strict checks. Aggregate Audit passes
{checked['aggregate_jobs']} jobs and checks {checked['audited_theorems']} theorem dependencies. Installed readback covers
{checked['public_declarations']} declarations and one full definition. Only permitted axioms occur.
H6, all earlier Lean sources except Audit imports, runtime and Haskell remain
unchanged. Every finite recursive capacity still has original resource bounds.

Whole-enumerator language soundness and completeness remain open. Next lift
these semantics through the actual cached adapter and pending assimilation.
Assimilation must derive assignment equality from actual union paths before
it removes the source restriction. Selector coverage, partial stop outputs,
unsupported fallback, concrete solver and Haskell correspondence remain open.
Details: `lean/notes-current-pruning-incoming-language.md`. FINDINGS has Haskell status.

'''
findings='''### Incoming-node assignment language and Haskell status

The actual native incoming producer now has exact assignment semantics for
its logical write and returned branch list. An Empty replacement has no
satisfying assignment at the written slot. Native effects
remain at their actual reached endpoint. The runtime code is unchanged.

No Haskell source changed. No new Haskell defect or repair was established.
External action: no additional patch. Retain all six earlier merged repairs,
the merged Sized documentation repair in PR #178 and all historical repros.
Keep the pending parallel-decision suffix-exception and cancellation findings.
The formal native worker still chooses serial forcing. Arbitrary Haskell
lazy demand and shared global caches remain correspondence obligations.
The formal assimilation step still needs an assignment-equality argument
from actual union paths. This is a proof obligation, not a reported defect.
Details: `lean/notes-current-pruning-incoming-language.md`.

'''
note=f'''# Exact assignment language of actual incoming-node branches

Published base: {(area/'base.txt').read_text().strip()}.
Imported main: {(area/'main.txt').read_text().strip()}.
Native language and pending-write commit: {commits[0]['commit']}.
Actual incoming producer and branches commit: {commits[1]['commit']}.
The full formalization goal stays ACTIVE and incomplete. Keep the optimized
interned core. Preserve all earlier proofs, counterexamples, repairs and
marked drafts. Earlier constructor and equality work remain secondary targets.
The preceding checkpoint is `lean/notes-current-pruning-finite-depth.md`.

## Strongest current statements

H6 remains `SourceCurrentColdFiniteWarmCalls.constructed_node_calls`.
Covered closed construction and valid constraint-allocation history derive
sufficient fuels and one mathematical width for any prescribed finite number
of modeled node-processing rounds and any budget. With empty inherited
payload, the final available node accepts exactly the original finite-tree
language for every ambient context and term under formal Formula and
Entailment. Its source remains byte-identical at SHA256
`e4665b0bb522ec88f1925fe6bc360b76e9e4bdfbe6192210ac708a3097a20cc5`.

`SourcePruningEnumerationRecursive.run_finite_complete_resources` still
provides sufficient original resources for every chosen finite recursive
capacity. The actual result is stable at all larger work fuels. Complete
and explicit stopped outcomes retain their own native caller, full memos,
cache, metadata packet and resource bounds. This theorem does not assert
that every result completes enumeration or has whole-enumerator language.

The new local language theorem is
`SourcePruningEnumerationIncomingNode.run_complete_branches`.
Under EXACTLY the original run_complete inputs, it constructs the SAME
finite execution bounds, read and write witnesses, caller, memos, inventory,
replacement and handle. All previous producer conclusions remain unchanged.
For every ambient native environment, arbitrary residual enumeration-guard
meaning and total term assignment, a returned successful branch satisfies
that assignment if and only if the original state satisfies it, the incoming
node accepts assignment(uv), and all incoming suspended constraints hold.

The interpretation reads lookupNode at each actual native heap. It uses
InternedGuardedLanguage.meaning of the full stored value. It does not assume
an unrelated Graph agrees with changing interned records. SourceEqualityRequiredCache.Keeps only
retains successful old lookups. It does not equate handle meaning globally
for handles that were absent before growth. PendingRealized supplies exactly
the stored pending handles needed for assignment transport.

The local theorem quantifies complete assignments. It is not an end-to-end
whole-enumerator or Haskell theorem. It makes no claim about unbounded
termination, recursive-capacity adequacy, practical memory or time, physical
containers, machine integers, concrete solver correctness, arbitrary lazy
demand, extraction, withoutRedundantEdges or complete typing/pruning language.

## Proof structure

SourcePruningEnumerationNativeLanguage.handles defines a handle language by
an actual lookup and independent guarded meaning of the decoded value.
handles_lookup fixes the value. handles_keeps requires an old successful
lookup. slot_keeps and heap_keeps restrict native-growth transport to stored
realized pending slots. satisfies_keeps retains their complete assignments.
frame_sameClass derives equivalence of actual union-find classes from finite
root paths. satisfies_frame retains assignments for any fixed node and
residual languages. satisfies_keeps_frame combines both transports.
No Safe premise is invented from a frame.

SourcePruningEnumerationPendingWriteLanguage.pending_write is graph-free.
An exact stored-slot receipt supplies the array bound. Exact forest, values
and residual-obligation equations plus a local replacement-handle language
relation derive complete assignment equivalence. It retains old suspended
constraints and adds each incoming constraint. It does not require a future
successful operation or a satisfying final assignment as an input.

SourcePruningEnumerationIncomingNode.run_complete_semantics calls the old
actual run_complete once. The same read witness and root uniqueness derive
the actual stored pending value. The no-old-handle route uses replacement
identity. The old-handle route uses its native conjunction-language receipt
and actual lookup preservation. The exact write receipt supplies the state
fields. Native-growth and frame transport return to the original state.

run_complete_branches calls run_complete_semantics once and retains its
ENTIRE conclusion as a prefix. It connects logical-write satisfaction to
the returned raw branch list. A stored decoded Empty value denotes False,
so raw [] removes no satisfying assignment. Nonempty replacement returns
the exact singleton state already supplied by the producer.
The runtime outer continuation is still the read state. The logical write
is not invented as a rejected runtime continuation. Native effects and full
memo histories stay at the actual returned caller, including rejection.

## Verification and retained attempts

All four new modules and Audit pass warningAsError and linter.all.
Aggregate Audit: {checked['aggregate_jobs']} jobs; {checked['audited_theorems']} theorem dependencies.
Installed public readback: {checked['public_declarations']} declarations and one full definition;
{checked['public_lines']} lines and {checked['public_bytes']} bytes; SHA256
`{checked['public_sha256']}`.
Only propext, Classical.choice and Quot.sound are permitted. Public signatures
contain no ellipsis or placeholder. H6 and all earlier Lean sources except
Audit imports are byte-identical. No runtime function or Haskell source changes.
All checks in this checkpoint run serially under an effective 4 GiB memory
maximum and high limit, with zero swap. Raw cap reports and peaks remain.

The first pending-write strict check failed in two self-slot simplifier
steps. Using the actual setSlot reduction fixes both. The first incoming
strict check failed on one unused simp argument. Removing that argument
fixes it. No public theorem header changes in either repair. Failed source
snapshots and complete raw logs remain in evidence. The first branch strict check required an explicit reduction of Empty
meaning to False. Adding that reduction fixes it. Its snapshot and raw log
remain. The last logical forall is grouped in parentheses before the outer
branch equivalence is appended. Its binders and body are unchanged.
The existing InternedFreshOrdinaryClosedCompletion dependency warning remains
separate from the clean strict checks of all changed sources and Audit.
No heartbeat increase, new axiom or runtime alteration was used.

Evidence: `lean/restart-evidence/20261026-incoming-language`.
Original proposals remain marked drafts. Use sources/ and final-strict.json
for final checked bytes. Raw logs are compressed losslessly as raw.log.gz.
Original temporary files remain intact. Preserve raw proof-change.patch.
Exclude only its exact path from staged whitespace checks.

## Next semantic obligation

First use the exact same after.core receipt in
SourcePruningEnumerationIncomingCacheAdapter.complete to transport incoming
assignment meaning through the cached adapter. Do not replace actual native
heap interpretation with arbitrary Graph.IntersectionCorrect.

Next cover SourcePruningEnumerationDispatch.dispatch_complete and
SourcePruningEnumerationAssimilation.pending_assimilation_complete.
The optional merge can write two slots and eliminate the source slot, or
reject Empty before those writes. Deleting the old source restriction
requires assignment(source)=assignment(target). The dispatcher slot receipts
alone do not imply that equality. Derive it from the actual TerminalPrefix
union paths and the satisfying assignment's union-find equations. Then use
the native conjunction-language receipt and Keeps at each actual endpoint.
Do not admit the desired final Satisfies relation as an original premise.
Use this result for terminal children and captured edges. Lift backward
assignment semantics to each recursive output at its OWN cache and heap.

Current Packet has representation, safety, pending, stratification and
metadata bounds. It has no assignment-preservation invariant. Current
selector membership and length laws allow edgesOf=[]; they cannot imply
language completeness. An arbitrary stop can emit partial metadata.
Selected terminal or nonordinary fallback stays explicitly unsupported.
More fuel or depth does not remove that route. Stratified alone also lacks
the neutral-pending premise needed for complete assignments. State selector
coverage, supported semantic domain, output and progress conditions before
claiming exact full language or recursive-capacity adequacy.

## Haskell external status

No Haskell source changed. No new runtime defect or repair was established.
FINDINGS records this status. Retain all six earlier merged repairs, the
merged Sized documentation repair in PR #178 and all historical repros.
Keep pending parallel-decision suffix-exception and cancellation findings.
The formal worker chooses serial forcing. Arbitrary lazy demand and shared
global Haskell caches remain correspondence obligations. The semantic gaps
above do not establish a Haskell defect or require an external patch.
'''
docs=['NEXT-PROMPT.md','HANDOFF.md','FINDINGS.md','lean/README.md','lean/SYSTEM.md','lean/COVERAGE.md','lean/API-COVERAGE.md','lean/notes-current-system-claim.md','lean/notes-proof-status-20261017.md']
marker='## Every finite recursive capacity now has original resource bounds'
for rel in docs:
 p=root/rel;s=p.read_text();assert s.count(marker)==1 and block.splitlines()[0] not in s,rel
 p.write_text(s.replace(marker,block+marker,1))
p=root/'FINDINGS.md';s=p.read_text();marker='### Finite recursive resources and Haskell status';assert s.count(marker)==1
p.write_text(s.replace(marker,findings+marker,1))
rel='lean/notes-current-pruning-incoming-language.md';assert not (root/rel).exists();(root/rel).write_text(note)
(area/'handoff-content.json').write_text(json.dumps(dict(block=block,findings=findings,note=note,docs=docs,note_path=rel),indent=2)+'\n')
print('Updated incoming-node proof status, Haskell handoff and exact next semantic obligation.')
