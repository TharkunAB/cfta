import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-native-callback-restart-20261026')
evidence = root / 'lean/restart-evidence/20261026-native-callback-restart'
base = (area / 'base.txt').read_text().strip()
sha = lambda data: hashlib.sha256(data).hexdigest()
old = lambda rel: subprocess.check_output(['git', 'show', base + ':' + rel], cwd=root)
checks = {p.parent.name: json.loads(p.read_text()) for p in sorted(area.glob('*/report.json'))}
assert len(checks) == 14
assert {name for name, report in checks.items() if report['exit_code']} == {
    'strict-restart-1', 'strict-after-callback-1', 'strict-after-callback-2'}
finals = {
    'SourcePruningEnumerationRestart': 'strict-restart-2',
    'SourcePruningEnumerationAfterCallback': 'strict-after-callback-3',
    'SourcePruningEnumerationReceiptCallback': 'strict-callback-restart-1',
    'SourcePruningEnumerationParkedRestart': 'strict-parked-restart-1',
    'Audit': 'strict-audit-1',
}
sources = ['lean/MicroCFTA/' + module + '.lean' for module in finals]
for module, name in finals.items():
    source = root / 'lean/MicroCFTA' / (module + '.lean')
    assert source.read_bytes() == (area / name / 'MicroCFTA' / source.name).read_bytes()
    assert sha(source.read_bytes()) == checks[name]['source_sha256']
    if module != 'Audit':
        assert not re.search(rb'\b(sorry|admit|axiom)\b', source.read_bytes())
for name, report in checks.items():
    raw = (area / name / 'raw.log').read_bytes()
    assert len(raw) == report['bytes'] and sha(raw) == report['sha256']
public_bytes = (area / 'public-final/raw.log').read_bytes()
public = public_bytes.decode()
assert public.count('depends on axioms:') == 21 and '⋯' not in public and '...' not in public
for axioms in re.findall(r'depends on axioms:\s*\[([^]]*)\]', public):
    assert set(re.findall(r'[A-Za-z_.]+', axioms)) <= {'propext', 'Classical.choice', 'Quot.sound'}
for declaration in ['SourcePruningEnumerationReceiptCallback.Completes',
                    'SourcePruningEnumerationAfterCallback.Follows',
                    'SourcePruningEnumerationRestart.decision']:
    assert 'def MicroCFTA.' + declaration in public
assert 'Checked axiom dependencies of 76876 MicroCFTA theorems.' in (area / 'aggregate-audit/raw.log').read_text()
relative = 'lean/MicroCFTA/SourcePruningEnumerationReceiptCallback.lean'
previous, current = old(relative).decode(), (root / relative).read_text()
headers = {}
for marker, end in [('def Completes ', '\n  | .complete'), ('theorem completes ', ' := by')]:
    a, b = previous.index(marker), current.index(marker)
    header = current[b:current.index(end, b)]
    assert previous[a:previous.index(end, a)] == header
    headers[marker.strip()] = sha(header.encode())
assert previous.count('recordTypes_inl_complete_bounded graph') == current.count('recordTypes_inl_complete_bounded graph') == 1
marker = '      obtain ⟨fuel, result, final, success, stable, frame, finalOrder, types, holes, typing, finalBounded⟩ :='
a, b = previous.index(marker), current.index(marker)
assert previous[a:previous.index('      exact', a)] == current[b:current.index('      exact', b)]
audit = 'lean/MicroCFTA/Audit.lean'
assert (root / audit).read_text() == old(audit).decode().replace(
    'import MicroCFTA.SourcePruningEnumerationSelectedOrdinary\n',
    'import MicroCFTA.SourcePruningEnumerationSelectedOrdinary\nimport MicroCFTA.SourcePruningEnumerationParkedRestart\n', 1)
unchanged = ['lean/MicroCFTA/' + module + '.lean' for module in [
    'SourcePruningEnumerationSelectedOrdinary', 'SourcePruningEnumerationSelectedNarrow',
    'SourcePruningEnumerationRecursion', 'SourcePruningEnumerationNativeBranches',
    'SourcePruningEnumerationNativeBranchCompletion', 'SourcePruningEnumerationNativeOrdinary',
    'SourcePruningEnumerationCapturedEdge', 'SourcePruningCallbackCompletion',
    'SourcePruningRecordTypes', 'SourcePruningEnumerationNativeIndex', 'EnumerationCompressionFrame',
    'EnumerationPendingOrder', 'EnumerationPendingReplacement', 'EnumerationFragmentHistory',
    'EnumerationOrder', 'EnumerationPureSelection', 'EnumerationIndexSelection',
    'EnumerationDriver', 'SourceCurrentColdFiniteWarmCalls',
]]
unchanged += ['cfta/src/Data/CFTA/' + name for name in [
    'Enumeration.hs', 'Interned/Type.hs', 'Interned/Cache.hs', 'Interned/Memo.hs', 'Interned/Operations.hs',
]]
for rel in unchanged:
    assert old(rel) == (root / rel).read_bytes(), rel
subprocess.run(['git', 'diff', '--quiet', base, '--', '*.hs', '*.cabal'], cwd=root, check=True)
main = subprocess.check_output(['git', 'rev-parse', 'origin/main'], cwd=root).decode().strip()
assert main == '153e1a211b56dd78bd22f6b427fb78e673041d55'
source_commits = ['3f02ddcef', '6dff1a207']
for commit in source_commits:
    subprocess.run(['git', 'merge-base', '--is-ancestor', commit, 'HEAD'], cwd=root, check=True)
block = '''## Concrete callbacks and parked recursion reach source restart

Callback composition: `3f02ddcef`. Parked restart: `6dff1a207`.
The goal stays ACTIVE.

An accepted concrete Left callback now reaches the actual stop/selection
restart at its returned metadata and cache. A pruning result or stuck
restart excludes all successful continuations. This does not assert an
empty raw stream: callback fuel errors can remain. The existing selected
ordinary producer inherits this output with its exact source unchanged.

Original native selection also derives the repeated-recursion restart.
Its actual clear write removes the full old bucket from waiting counts,
disables the slot and retains the observed core. The producer derives
sufficient index fuel. No future cache or continuation success is assumed.
This branch retains metadata and dependency levels. It performs no narrowing
or oracle call. The false guard result still awaits narrowing composition.

Stop checks all remaining candidates, including blocked candidates, before
selection. All five changed modules pass strict checks. Installed public
readback and Audit pass; Audit checks 76876 dependencies. H6 remains the
strongest end-to-end language theorem. Haskell source stays unchanged.
Next: compose a complete selected step and its depth-first continuation
with shared native effects. Initial-only capacity, native Graph correspondence,
terminal/nonordinary fallback, extraction and whole-driver language semantics
remain open. Details: `lean/notes-current-pruning-enumeration-callback-restart.md`.

'''
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/COVERAGE.md', 'lean/API-COVERAGE.md',
             'lean/notes-current-system-claim.md', 'lean/notes-proof-status-20261017.md']
for rel in documents:
    path = root / rel
    text = path.read_text()
    marker = '## Concrete callbacks retain the native indexed cache'
    assert marker in text and block.splitlines()[0] not in text
    path.write_text(text.replace(marker, block + marker, 1))
path = root / 'FINDINGS.md'
text = path.read_text()
addition = '''### Callback and repeated-recursion restart boundary

The concrete callback model now composes its pruning Boolean with the source
stop/selection step. Rejection excludes successful continuations. It does
not erase raw callback fuel errors. Accepted callbacks use their own returned
metadata and actual cache. The selected ordinary producer inherits the proof.

The repeated-recursion model reads and checks once. Its true branch rebuilds
indexes from the full original suspended bucket and retains the checked core.
The original selected producer derives the needed index fuel and exact raw
restart result. This path uses unchanged metadata and no oracle or narrowing.
Outside the admitted state and sufficient fuel, adapter failure remains an
explicit error. There is no general error-classification claim for that case.

Enumeration.hs:963 checks the nonempty full candidate set before selection.
Lines 980 and 1004 restart after accepted Left callbacks and repeated guards.
The model retains this order. Exact depth-first native effect interleaving
and complete recursive-driver semantics remain open. No new Haskell defect
or repair is identified. External action: no new patch is proposed.
Keep the repair table and pending Sized documentation repair above.
Details: lean/notes-current-pruning-enumeration-callback-restart.md.

'''
marker = '### Concrete callbacks preserve native cache certificates'
assert marker in text and addition.splitlines()[0] not in text
path.write_text(text.replace(marker, addition + marker, 1))
assert path.read_text().index('## Haskell fix handoff') < path.read_text().index(block.splitlines()[0])
note = f'''# Concrete callback and repeated-recursion restart

## Current result

Source commits: `3f02ddcef` and `6dff1a207`.
Recorded origin/main: `{main}`.
The whole formalization goal stays ACTIVE.

The selected ordinary proof now derives a concrete Left callback followed
by its source stop/selection restart. The same completion witness supplies
the stronger output. The original native selection also derives an actual
repeated-recursion restart with rebuilt waiting counts and candidate flags.
Neither result assumes a successful future continuation or a future cache.

H6 constructed_node_calls remains the strongest end-to-end language theorem.
Given a covered closed construction and valid original constraint allocation
history, any prescribed finite node-call budget and round count have derived
sufficient finite fuels and one mathematical width chosen after construction.
The modeled trace completes. Its final available value has exactly the
initial finite-tree language for every ambient environment and finite term,
under the formal Formulas and Entailment interfaces. The inherited constraint
payload is empty. This theorem does not cover the whole typing/pruning driver,
withoutRedundantEdges, arbitrary mixed calls or convergence.

## Stop and selection retain source order

Restart.decision tests an optional stop predicate before pure next selection.
It tests every remaining candidate, including blocked candidates. It stops
only if that list is nonempty and every candidate passes. An absent stop
rule always reaches selection. The result distinguishes early stop, done,
stuck and a selected expansion. Restart.run rejects only stuck selection.
Other results retain the exact supplied metadata and enumeration core.

decision_frame retains the decision under compression at the same metadata
and allocation counter. The frame retains indexes. The counter determines
the candidate list range. A metadata update can change the preference, so
the proof uses the returned metadata on both sides. It does not equate old
and updated metadata preferences. selected derives readiness, no incoming
references, and the closed available pending value for an actual expansion
decision from the original Safe and native CacheValid inputs.

## Concrete callback rejection or restart

AfterCallback.run executes recordTypes on the actual fragment, applies
require to the negated pruning flag, reads the actual resulting core and
calls Restart.run with the callback's returned metadata. It frames this
core with the indexed cache already preserved by the callback theorem.

run_success derives actual Success for a false pruning flag and a non-stuck
restart. The returned core is the same callback endpoint. run_pruned excludes
every successful continuation when a known callback result prunes. It uses
recordTypes_agrees to compare any other success of that same action.
run_stuck excludes every successful continuation when the known restart is
stuck. Agreement retains metadata and a frame between compressed endpoints;
decision_frame transports the stuck decision across those endpoints.

These are claims about successful results. They do not state that the raw
composite result is empty. A raw callback action can also contain fuel errors.
Follows records both implications for every stop rule and expansion order.
The original receipt supplies representative totality through its actual
Safe input. No new callback-success or future-success premise is added to
ReceiptCallback.completes. Its existing bounded callback is executed once.

Completes and completes retain their exact declaration types and inputs.
The completion predicate adds Follows at the same chosen fuel, result and
callback cache. The earlier safety, metadata, history and index clauses stay.
SelectedOrdinary.complete_with_history and its wrapper remain byte-for-byte
unchanged and inherit the stronger predicate through their existing call.
This is per-receipt availability, not execution of callbacks inside the
serial native alternative scan. Each source sibling uses the same incoming
metadata; its returned metadata feeds its own recursive continuation.

## Repeated recursion derives an indexed restart

ParkedRestart.selected_complete_with_order calls the original native selected
producer once. It retains all original read/check/write receipts and derives
the unchanged counter and dependency levels for the actual pending clear.
The actual clear preserves the representative forest and removes outgoing
bucket references. It does not add a dependency or advance the frontier.

adapt rebuilds the indexes using NativeIndex.write at the original cached
indexes. The gained bucket is empty. The lost bucket is the full original
scs, so every suspended waiting count is removed. The candidate flag is
recomputed for the cleared pending slot. The final mapping retains the
exact observed check core, rather than the synthetic indexed-write core.
Framing the check core with old indexes alone would leave stale counts.

adapt_after_write derives the adapter result from the actual clear write
and the indexed-write receipt. The clear retains the forest read by count;
the original waiting map and flags are the same. The final frame retains
the observed core. There is no list-write idempotence assumption.

run performs one getValue and one native checkRepeated. Read and check errors
remain explicit. A false guard returns the checked prefix with payload None;
it is a boundary awaiting narrowing. A true guard recovers the indexed cache
and restarts at unchanged metadata. Failed index recovery returns an explicit
representativeFuel error. The proof makes no general classification claim
for arbitrary candidates or insufficient fuel outside the admitted inputs.

selected_complete_with_restart starts from Safe, actual native CacheValid
and original pure selection. It derives the same selected producer witnesses,
retains final Safe and CacheValid at the same Caller, and transports global
pending history when supplied. On the repeated branch it derives a finite
countFuel from the producer's indexed-write receipt. Every larger index fuel
gives the same exact raw restart: empty for stuck, otherwise a singleton at
the actual parked core. The exact read and check fuels are those chosen by
the original producer. No future adapter result is an admission premise.
This branch performs no narrowing or oracle call.

## Verification

Lean 4.34.1 checks all five changed modules with all linters and warnings
as errors. Eight strict attempts retain three failed attempts. The first
restart proof left reflexive goals after unfolding. The first two callback
proof attempts used an unmatched framed rewrite, eliminated a binder too
early, or left ExceptT.run opaque. The final direct expansion and explicit
substitutions close these goals. All five final strict checks pass.

Four installed helper/consumer builds pass. The unchanged selected-ordinary
consumer rebuilds with the stronger completion output. Aggregate Audit passes
with 3770 jobs and checks 76876 theorem dependencies. Audit source adds one
import; its checker stays exact. The existing unused inputs warning remains.
The dependency total is an audit count, not a completion estimate.

Installed public readback checks 21 declaration types and axiom sets. It
prints the full installed Completes, Follows and restart decision definitions.
The full output has {len(public.splitlines())} lines and {len(public_bytes)} bytes.
SHA-256: `{sha(public_bytes)}`.
There is no output ellipsis. All axiom sets are subsets of propext,
Classical.choice and Quot.sound. No new project axiom is added.
All 14 checks run serially under heavy-management 4 GiB caps.

Independent source review confirms the actual callback endpoint, all-success
rejection scope, full stop set, same returned metadata, original lost bucket,
actual indexed write, derived count fuel and observed checked core. It finds
no future-success admission or full-loop claim. The original recursion worker,
selected producer, native scan and H6 source stay unchanged. No Haskell or
package file changes, so the Haskell suites and format checks are not repeated.
No new Haskell repair is identified. FINDINGS retains the external repair table.

Evidence: lean/restart-evidence/20261026-native-callback-restart.
The manifest records exact payload bytes and SHA-256 for all raw logs,
strict source copies, failed attempts, public readback, final and original
source snapshots, proof diff, verification report and cap records.
Force-add exactly those payloads and verify staged and committed bytes.

## Next work

Compose a complete selected-step worker from the original selection. Its
repeated branch must use this derived indexed restart. Its false branch
must use the actual narrowing, Right callback and admitted native ordinary
producer at their reached Caller/cache/memos. Keep Empty, rejected, parked,
stopped and unsupported outcomes explicit. Do not treat a false check prefix
as a complete ordinary expansion.

Then compose each completed fragment callback with the recursive continuation
inside the actual depth-first alternative demand. Siblings restore the local
enumeration state and share evaluated native interner/memo effects. The
current serial alternative scan can force later alternatives before earlier
recursive continuations. Its per-receipt callback proofs do not establish
the source's complete effect interleaving or arbitrary Haskell forcing.

The ordinary producer still requires reached-state numeric Ranges. A complete
forecast must derive all native query capacity from initial inputs across
narrowing, selected children, alternatives and recursive continuation.
Additional fuel does not prove that machine-word capacity is sufficient.
Native Graph/heap classification, terminal/nonordinary outer fallback,
whole-driver pruning language laws, extraction, concrete solver behavior,
physical containers and complete Haskell finite-machine correspondence stay
open. H6 and component results must remain distinct from those obligations.
'''
(root / 'lean/notes-current-pruning-enumeration-callback-restart.md').write_text(note)
review = '''Independent source review: callback/receipt composition CLEAR; parked restart CLEAR.
Parked source SHA-256: bf5c16846f77bfa8d146f58ea8dafbde34ca1a1bef9dbfe453f344bebc0b94e0.
Confirmed: original indexes, full lost bucket, exact observed check core, same producer witness,
derived count bound, no future adapter/success premise, false prefix awaits narrowing,
admitted repeated-branch raw equality only, callback rejection excludes successes only.
No source edits or builds were part of this independent review.
'''
(area / 'independent-review.txt').write_text(review)
verification = dict(base=base, source_commits=source_commits, recorded_main=main, checks=checks,
                    final_strict_modules=finals, preserved_header_sha256=headers,
                    public_declarations=21, public_definitions_printed=3,
                    public_lines=len(public.splitlines()), public_bytes=len(public_bytes),
                    public_sha256=sha(public_bytes), audit_dependencies=76876,
                    final_source_sha256={rel: sha((root / rel).read_bytes()) for rel in sources},
                    unchanged_source_sha256={rel: sha((root / rel).read_bytes()) for rel in unchanged},
                    goal_status='active', existing_runtime_workers_and_haskell_unchanged=True,
                    new_executable_workers=['Restart.run', 'AfterCallback.run', 'ParkedRestart.adapt', 'ParkedRestart.run'])
(area / 'verification.json').write_text(json.dumps(verification, indent=2) + '\n')
(area / 'proof-change.patch').write_bytes(subprocess.check_output(['git', 'diff', base, 'HEAD', '--', *sources], cwd=root))
for rel in sources + unchanged:
    destination = area / 'sources' / rel
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(root / rel, destination)
assert not evidence.exists()
shutil.copytree(area, evidence)
manifest = {str(p.relative_to(evidence)): dict(bytes=p.stat().st_size, sha256=sha(p.read_bytes()))
            for p in sorted(evidence.rglob('*')) if p.is_file()}
(evidence / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps(dict(payloads=len(manifest), bytes=sum(item['bytes'] for item in manifest.values()),
                      manifest_sha256=sha((evidence / 'manifest.json').read_bytes()))))
