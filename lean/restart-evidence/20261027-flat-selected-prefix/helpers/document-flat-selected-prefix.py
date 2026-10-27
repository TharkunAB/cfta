from pathlib import Path
import hashlib
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-flat-selected-prefix-20261027')
head = (area / 'source-head.txt').read_text().strip()
base = (area / 'published-base.txt').read_text().strip()
public = json.loads((area / 'installed-public/report.json').read_text())
prefix = '''
## Actual flat selected prefixes now derive completion and full native effects

Source checkpoint: SOURCE_HEAD.
Eight new modules and sixteen public theorems cover the complete selected
prefix through Right recording. The original recursive Packet supplies its
entire sufficient-bound prefix guarantee once. A related initial flat cache
then gives actual flat prefix correspondence at every adequate larger bound.
The appended guarantee uses the actual flat restart expansion decision.
Parked, Empty and nonempty narrowing retain their actual observed states.
Every narrowed result retains full native Post and final global Memos.
Every returned candidate has related earlier Packet and native-correct indexes
at the same reached Caller. Empty keeps native effects without a candidate.
No future flat observation or final flat invariant is an input.

The prefix does not execute ordinary siblings or the recursive worker.
The original conditional ordinary capability remains in the earlier packet.
H6 and captured rendering stay unchanged. Whole output soundness, coverage,
pruning-policy soundness and admission histories remain open.
Audit passes 4020 jobs and 78555 theorem dependency checks. All eight modules
and Audit pass strict checks. No Haskell source changed. FINDINGS retains
all Haskell repair handoffs and the extraction-progress limit.

Next transport actual captured child and recursive consumers through the same
native histories. Derive Canonical, semantic Ranges and allocation bounds.
Details: `lean/notes-current-flat-selected-prefix.md`.

'''.replace('SOURCE_HEAD', head)
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/API-COVERAGE.md',
    'lean/COVERAGE.md', 'lean/README.md', 'lean/SYSTEM.md',
    'lean/notes-current-system-claim.md', 'lean/notes-proof-status-20261017.md']
records = []
for name in documents:
    path = root / name
    old = path.read_bytes()
    baseline = subprocess.check_output(['git', 'show', base + ':' + name], cwd=root)
    assert old == baseline
    target = area / 'prior-documents' / name
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(old)
    first, rest = old.split(b'\n', 1)
    assert b'Actual flat selected prefixes now derive completion' not in old
    data = first + b'\n' + prefix.encode() + rest
    path.write_bytes(data)
    records.append({'path': name, 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest(),
        'offset': len(first) + 1, 'inserted_bytes': len(prefix.encode())})

note = '''# Actual flat selected-prefix completion

Source checkpoint: SOURCE_HEAD.
Published base: PUBLISHED_BASE.
Imported main: 82258094c2c32bb93e517427bc649a5c7077adac.
The initial formalize pull and main fetch succeeded. Main did not change.
The full formalization goal stays ACTIVE and incomplete. Keep the optimized
interned core and all previous proofs, repairs, counterexamples and marked drafts.
The previous checkpoint is notes-current-flat-pruning-callback.md.

## Target and strongest global claims

The target is a source-connected correctness argument for the whole system.
It must preserve the original finite-tree language and justify enumeration
outputs and coverage under the stated solver and pruning contracts.
The present completion result covers one selected prefix of that enumeration.

SourceCurrentColdFiniteWarmCalls.constructed_node_calls stays unchanged.
Covered closed construction and valid original guard-allocation history supply
any chosen finite budget and round count at derived mathematical width and fuels.
Those actual formal node calls complete. The final node remains available.
Its finite-tree language equals the original language in every ambient environment.
The inherited payload is empty. The theorem does not certify whole Haskell APIs.

SourcePruningEnumerationCapturedEdge.diagonal_render_sound_current also stays
unchanged. Actual stable captured-edge completion, its current admission gates,
structural discharge, successful rendering and checked residuals derive original
edge and parent acceptance and every original suspended constraint. It constructs
a satisfying assignment. It does not prove that discharge or rendering exists.

## Actual operations and primitive proofs

SourceFlatPruningRecursion.checkRepeated decodes the same native handle.
It reads the actual representative only at a recursive boundary.
It tests the original handle and bucket key in that root's ancestry.
A repeated key clears the bucket at that root. Index repair remains separate.
The related/stable lemmas compare all raw rows at completed or sufficient old
lookup bounds. The replay lemma uses actual successful old reads. It requires
no unused lookup on a nonboundary branch.

SourceFlatPruningAction.prepare executes the same native narrowing once.
It preserves faults, native values and the reached native heap.
Empty returns a rejecting core action before any enumeration write.
The same handle returns pure unit. A changed handle writes at the actual root.
PreparedRelated compares native state and all captured rows at the supplied cores.
Its stable representative bound covers every native fuel at those fixed cores.
SourceFlatPruningAction.prepare_replays obtains used lookup receipts from
the actual old preparation and action. It exports literal Empty rejection.
The Empty case is not inferred from a vacuous successful-action relation.

SourceFlatPruningCompletedIndex.count_eq follows each actually completed old
root observation. It preserves order, duplicates and signed waiting-count bumps.
write_related uses those completed lost and gained folds at the same native heap.
It needs no extra lookup fuel, Safe or desired final index invariant.
It does not assert that an arbitrary supplied write completes or is valid.

SourceFlatPruningIndexAdapters.parked uses the actual checked forest.
It removes the original bucket occurrences and maps back the actual checked core.
Changed narrowing removes and adds the full bucket at the actual observed forest.
Unchanged narrowing frames that observed core with the original indexes.
The completed adapters preserve actual successful old options at the same fuel.
The core lemmas keep observed cores separate from synthetic index-write cores.
In particular, do not apply write_correct at an already cleared slot while
treating its stored bucket as the original bucket. The returned earlier
CacheValid and actual Related endpoint supply correctness here.

## The complete selected prefix

SourceFlatPruningSelectedPrefix.run executes entry read, recursion check,
native preparation, captured action, cache attachment and Right recording.
It retains every reached raw observation and optional cache separately.
It advances Caller to prepared.state on failure and success. Queries remain
the original saved query table. Empty retains native effects and some empty
action rows, with no candidate or Right event.
Missing decode, action, encoding or cache remains an explicit branch.
Right recording runs at the attached core. An accepted singleton frames the
actual returned callback core. Other callback raw remains recorded.
The result type has no ordinary-continuation field.

run_related_of_valid uses PrefixValid for the ACTUAL earlier diagonal run.
It replays the actual singleton entry read and recursion check.
For nonempty narrowing, its private observation lemma inverts that actual run
to recover the action singleton and completed adapter. Result annotations alone
do not substitute for these execution equations.
It then replays the action and completed adapter at their actual reached cores.
The pre-expansion Right callback is pure for every template catalog.
Parked restart preserves the actual metadata, decision and related cores.
The relation retains native preparation, literal Caller and Queries, ordered
optional rows and related candidates. It requires earlier ordinary = none.
The virtual finish in PrefixValid retains an older conditional ordinary
capability. This new prefix does not execute that finish or an ordinary scan.

## Completion from original admission

packet_prefix_complete calls the original Recursive.packet_prefix_complete once.
Its inputs are the original recursive Packet and a flat cache related to that
same initial cache. Packet contains full native Context and global Memos,
Safe storage, pending references, native cache validity, dependency order and
allocated pending metadata IDs. Packet does not contain Canonical.
The result retains the ENTIRE original universal adequate-bound PrefixValid
family under its original earlier restart gate.

An added family uses the ACTUAL FLAT restart expansion decision.
decision_related transfers it to that same earlier gate and selected variable.
At every adequate larger bound, the actual flat prefix relates to the actual
earlier diagonal prefix. Native narrowing and callback fuel stay at that bound.
Direct-parent reads remove representative and count lookup fuel only.
No future flat observation, flat final invariant, new capacity gate or successful
ordinary continuation is an input.

A returned parked candidate retains the related earlier Packet at the original
Caller and full original Memos. Every narrowed result retains an actual Post
and its full final global Memos, whose query field equals the saved Queries.
This includes Empty and absent candidates. A returned narrowing candidate
additionally retains the related earlier Packet at that SAME reached Caller
and SAME final Memos. Every returned candidate has native-correct indexes at
that actual Caller heap. The proof uses earlier CacheValid storage alignment,
roots and both indexes. It does not infer Safe from Related alone.

## Verification and preservation

Eight new modules contain 1170 lines and sixteen public theorems.
Audit adds only eight imports. All previous proof source remains unchanged.
Each new module and Audit passes -DwarningAsError=true -Dlinter.all=true.
The aggregate audit passes 4020 jobs and 78555 theorem dependency checks.
Only propext, Classical.choice and Quot.sound are permitted.
The aggregate build replays the existing unused inputs warning in
InternedFreshOrdinaryClosedCompletion. Changed-source strict checks are clean.

Installed readback covers all sixteen new theorem signatures, unchanged H6 and
captured rendering, five complete runtime definitions and three complete
relation definitions. It has PUBLIC_BYTES bytes, SHA256 PUBLIC_SHA.
All eighteen theorem readbacks use only permitted axioms. No printed body is
truncated. Checks run serially with 4 GiB memory.max/high, zero swap and a
five-minute limit. The evidence retains failed attempts and their exact source
versions. Historical draft snapshots remain distinct from final checked source.

No Haskell source changed. No new Haskell runtime defect or repair was found.
FINDINGS retains all existing external repair handoffs and the known extraction
progress limit. No native suite was repeated because its source did not change.

## Remaining work

Transport actual captured child, sibling and recursive resume consumers through
these same native histories. Thread captured parent metadata and actual Caller,
full Memos and cache endpoints. Derive initial Canonical, semantic numeric Ranges
and allocation bounds from the original construction and receipt histories.
Prove whole-worker output classification and soundness. Prove pruning-policy
soundness separately from representation correspondence. Establish coverage and
forward completeness. A scheduler done result alone does not give structural
discharge or an available render carrier.

Mixed typing/pruning APIs, concrete solver and physical-container correspondence,
machine overflow, practical resource bounds and unbounded convergence remain open.
No arbitrary low-old-fuel error correspondence is claimed. No one literal flat
endpoint for all fuel values is required. Invalid raw target behavior of physical
IntMap insertion remains outside the list-based stored-core contract.

Evidence: lean/restart-evidence/20261027-flat-selected-prefix.
'''.replace('SOURCE_HEAD', head).replace('PUBLISHED_BASE', base).replace('PUBLIC_BYTES', str(public['bytes'])).replace('PUBLIC_SHA', public['sha256'])
name = 'lean/notes-current-flat-selected-prefix.md'
assert not (root / name).exists()
(root / name).write_text(note)
records.append({'path': name, 'bytes': len(note.encode()), 'sha256': hashlib.sha256(note.encode()).hexdigest()})
(area / 'document-paths.json').write_text(json.dumps(documents + [name], indent=2) + '\n')
(area / 'document-validation.json').write_text(json.dumps(records, indent=2) + '\n')
print(json.dumps({'documents': len(records), 'note_bytes': len(note.encode()), 'source_head': head}))
