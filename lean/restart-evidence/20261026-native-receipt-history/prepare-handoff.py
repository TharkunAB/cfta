import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-native-receipt-history-20261026')
evidence = root / 'lean/restart-evidence/20261026-native-receipt-history'
base = (area / 'base.txt').read_text().strip()
sha = lambda data: hashlib.sha256(data).hexdigest()
old_source = lambda relative: subprocess.check_output(['git', 'show', base + ':' + relative], cwd=root).decode()
checks = {p.parent.name: json.loads(p.read_text()) for p in sorted(area.glob('*/report.json'))}
failed = {name for name, report in checks.items() if report['exit_code']}
assert len(checks) == 14
assert len([name for name in checks if name.startswith('strict-')]) == 9
assert failed == {'strict-branch-history-1'}
finals = {
    'EnumerationPendingOrder': 'strict-pending-order-1',
    'SourcePruningEnumerationRecursionOrder': 'strict-recursion-order-1',
    'SourcePruningEnumerationNativeBranchCompletion': 'strict-branch-history-3',
    'SourcePruningEnumerationNativeOrdinary': 'strict-ordinary-history-2',
    'SourcePruningEnumerationReceiptCallback': 'strict-receipt-callback-1',
    'SourcePruningEnumerationSelectedOrdinary': 'strict-selected-history-1',
}
sources = ['lean/MicroCFTA/' + module + '.lean' for module in finals]
for module, run in finals.items():
    current = (root / 'lean/MicroCFTA' / (module + '.lean')).read_bytes()
    assert current == (area / run / 'MicroCFTA' / (module + '.lean')).read_bytes()
    assert sha(current) == checks[run]['source_sha256'] and checks[run]['exit_code'] == 0
    assert not re.search(rb'\b(sorry|admit|axiom)\b', current)
for name, report in checks.items():
    raw = (area / name / 'raw.log').read_bytes()
    assert len(raw) == report['bytes'] and sha(raw) == report['sha256'], name
public_bytes = (area / 'public-final/raw.log').read_bytes()
public = public_bytes.decode()
assert public.count('depends on axioms:') == 17 and '⋯' not in public and '...' not in public
for axioms in re.findall(r'depends on axioms:\s*\[([^]]*)\]', public):
    assert set(re.findall(r'[A-Za-z_.]+', axioms)) <= {'propext', 'Classical.choice', 'Quot.sound'}
assert 'Checked axiom dependencies of 76834 MicroCFTA theorems.' in (area / 'aggregate-audit/raw.log').read_text()

headers = {}
for module, names in [
    ('SourcePruningEnumerationNativeBranchCompletion', ['complete_with_posts', 'complete']),
    ('SourcePruningEnumerationNativeOrdinary', ['complete_with_posts', 'complete', 'selected_complete']),
    ('SourcePruningEnumerationSelectedOrdinary', ['complete']),
]:
    relative = 'lean/MicroCFTA/' + module + '.lean'
    old, current = old_source(relative), (root / relative).read_text()
    def header(text, name):
        start = text.index('theorem ' + name + '\n')
        return text[start:text.index(' := by\n', start)]
    for name in names:
        assert header(old, name) == header(current, name), (module, name)
        headers[module + '.' + name] = sha(header(current, name).encode())
    old_name = 'complete' if module.endswith('SelectedOrdinary') else 'complete_with_posts'
    def inputs(text):
        return text[text.index('\n'):].split(' :\n    ∃', 1)[0]
    assert inputs(header(current, 'complete_with_history')) == inputs(header(old, old_name)), module
    if not module.endswith('SelectedOrdinary'):
        assert old[old.index('theorem complete\n'):] == current[current.index('theorem complete\n'):]
ordinary = 'lean/MicroCFTA/SourcePruningEnumerationNativeOrdinary.lean'
marker = '/-- Actual ready entry retains the full prefix Caller receipt for each processed alternative. -/'
assert old_source(ordinary).split('theorem complete_with_posts\n')[0].rsplit('/--', 1)[0] == (root / ordinary).read_text().split('theorem complete_with_history\n')[0].rsplit('/--', 1)[0]
unchanged = ['lean/MicroCFTA/' + name + '.lean' for name in [
    'Audit', 'EnumerationState', 'EnumerationCorrectness', 'EnumerationDriver',
    'EnumerationOrder', 'EnumerationReferences', 'EnumerationCompressionFrame',
    'EnumerationPartialCompletion', 'EnumerationPartialBounds', 'SourcePruningCallbackCompletion',
    'SourcePruningRecordTypes', 'SourcePruningEnumerationCapturedEdge',
    'SourcePruningEnumerationNativeBranches', 'SourcePruningEnumerationSelectedNarrow',
    'SourcePruningEnumerationRecursion', 'SourcePruningEnumerationAction',
    'SourcePruningEnumerationSelectedEntry', 'SourceCurrentColdFiniteWarmCalls',
]]
unchanged += ['cfta/src/Data/CFTA/' + name for name in [
    'Enumeration.hs', 'Interned/Type.hs', 'Interned/Cache.hs', 'Interned/Memo.hs', 'Interned/Operations.hs',
]]
for relative in unchanged:
    assert old_source(relative).encode() == (root / relative).read_bytes(), relative
subprocess.run(['git', 'diff', '--quiet', base, '--', '*.hs', '*.cabal'], cwd=root, check=True)
assert subprocess.check_output(['git', 'rev-parse', 'origin/main'], cwd=root).decode().strip() == '153e1a211b56dd78bd22f6b427fb78e673041d55'

block = '''## Selected ordinary receipts derive concrete fragment callbacks

Native receipt history: `59706bb3f`. Prefix and callbacks: `0f8037add`.
The goal stays ACTIVE.

Every processed native alternative now retains completion-only fragment
history at its own actual cache. Successful receipts retain allocation growth,
pending hole targets and conditional frontier advancement. Ordinary entry and
original selection transport that history through their actual reads, false
recursion guard and pending-handle replacement. No producer input changes.

The selected result now derives finite concrete Left callbacks for every
completed receipt, from original dependency levels and parked-ID bounds.
Each callback uses that receipt's cache and the supplied metadata. It returns
safe framed storage, the exact type-position update and allocated pending IDs.
Either pruning Boolean is allowed. Siblings use the same input metadata in
the source; each callback output feeds its own recursive continuation.
This proof does not execute callbacks inside the serial alternative scan.

All six changed modules, public readback and Audit pass. Audit checks 76834
dependencies. Six older public declaration types remain exact. H6 remains
the strongest end-to-end language result. Haskell and Audit source stay exact.
Next: retain the full native indexed-cache packet through actual callback
reads, then model callback and recursive-continuation interleaving with shared
native effects. Initial-only capacity, native Graph correspondence, scheduler
restart, extraction and whole-driver language semantics remain open.
Details: `lean/notes-current-pruning-enumeration-receipt-history.md`.

'''
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/COVERAGE.md', 'lean/API-COVERAGE.md',
             'lean/notes-current-system-claim.md', 'lean/notes-proof-status-20261017.md']
for relative in documents:
    path = root / relative
    text = path.read_text()
    marker = '## Native captured edges preserve fragment dependency history'
    assert marker in text and block.splitlines()[0] not in text
    path.write_text(text.replace(marker, block + marker, 1))
path = root / 'FINDINGS.md'
text = path.read_text()
addition = '''### Selected receipts and concrete callback availability

The selected ordinary model now retains fragment history and allocation
growth for each completed alternative at its own cache. Initial dependency
levels and parked-ID bounds derive a finite concrete Left callback there.
The callback can accept or reject. Both outcomes retain safe framed storage,
exact metadata fields and allocated returned pending IDs.
No successful callback execution is an input premise. No runtime worker changes.

Enumeration.hs:975 captures the same ost' for sibling alternatives. Each
callback returns its own ost'', which feeds that branch's recursive continuation.
A metadata fold across sibling alternatives is not required by this source.
The proof derives independent callbacks. Exact interleaving of native effects,
callbacks and recursive continuations remains open. No Haskell runtime defect
or new repair is identified. External action: no new patch is proposed.
Keep the repair table and pending Sized documentation repair above.
Details: lean/notes-current-pruning-enumeration-receipt-history.md.

'''
marker = '### Native fragment dependencies survive captured finalization'
assert marker in text and addition.splitlines()[0] not in text
path.write_text(text.replace(marker, addition + marker, 1))
assert path.read_text().index('## Haskell fix handoff') < path.read_text().index(block.splitlines()[0])

note = f'''# Native receipt history and concrete callback completion

## Current result

Native history and entry transport: `59706bb3f`.
Selected prefix and concrete callbacks: `0f8037add`.
Main remains `153e1a211b56dd78bd22f6b427fb78e673041d55` after fetch.
The whole formalization goal stays ACTIVE.

Original selection now reaches admitted ordinary expansion with a fragment
history certificate for each completed alternative. From original dependency
levels and original parked-ID bounds, that same receipt derives finite
execution of the concrete fragment callback at its own cache. The proof
uses actual producer witnesses throughout. It adds no admission inputs.

## Native receipt history

NativeBranchCompletion.FragmentHistory is indexed by the original enumeration
state and each receipt. A completed receipt supplies actual allocation growth,
PendingFragment at its embedded final cache and conditional advancement from
any original Stratified order to frontier+1. Other receipt constructors supply
True. Rejection and unsupported outcomes gain no Safe or rank claim.

The private head producer now calls CapturedEdge.complete_with_history once.
It retains that call's exact counter-growth and completed-fragment witnesses.
The alternative induction threads native Caller and memo effects while it
restores the same enumeration input for each sibling. Head and tail histories
therefore have the same original cache parameter. They do not use a previous
alternative's cache. Per-receipt prefix Post and saved queries remain intact.

NativeOrdinary.complete_with_history uses the same actual entry and branch
scan as before. RenderStable supplies counter equality and dependency-order
transport from the original ordinary input to its actual entry state.
fragmentHistory_transport composes counter growth and dependency levels.

## Original selected prefix

EnumerationOrder.frame_stratified preserves exactly the same level function
and frontier through representative compression. It uses values and actual
root paths. It neither requires Safe nor infers Safe from Frame.
setValue_pending_stratified preserves the same levels when an actual stored
pending slot is replaced by another pending slot. Old and new handles and
suspended buckets can differ. This rank-only helper creates no safety claim.

RecursionOrder.checkRepeated_false_frame proves that an actual false native
check preserves all fields and representative paths. Missing native lookup
cannot succeed. A repeated-key write returns true and cannot supply the
observed false result. The remaining boundary branch retains the actual
representative read. The theorem uses totality and actual execution, without
another producer call, assumed decoded result or supplied successful read.

SelectedOrdinary.complete_with_history calls SelectedNarrow.complete once.
Its actual read receipt gives the first Frame. Its actual false check gives
the second Frame. The unchanged-handle branch retains those fields. The
changed-handle branch retains the same representative reread and pending
write. It derives old storage from the actual frames and original stored
slot. Both paths keep the original counter, level function and frontier.
The ordinary producer runs once at that reached Caller/cache/memo endpoint.
Its per-receipt Post composes from the original selected Caller. Fragment
history transports back to the original selected enumeration state.

Six older public declaration types are byte-identical: branch complete and
complete_with_posts; ordinary complete, complete_with_posts and selected_complete;
and selected-ordinary complete. The older branch complete and the older
ordinary complete/selected_complete declarations stay byte-identical. The
other older interfaces are projection wrappers. Strengthened
producers have exactly the same input binders as their older interfaces.
All existing runtime workers and Haskell expressions remain unchanged.

## Concrete callbacks at the actual receipt cache

ReceiptCallback.Completes is a completion-only output predicate. For each
completed fragment it takes original Stratified levels and allocation bounds
for the supplied metadata.pending. Actual receipt growth lifts those bounds
to the receipt's own final counter. Admitted supplies Safe and FragmentBound;
FragmentHistory supplies the final dependency order. The proof then calls
recordTypes_inl_complete_bounded, without assuming rendering or callback success.

The callback result has actual recordTypes Success, RenderStable, Frame and
Stratified at frontier+1. It derives the exact updated type-position field,
unchanged openHoles and typing, and allocated IDs in all returned pending
groups. Either Boolean is allowed. Completion does not assert acceptance,
pruning soundness or equality with a concrete external solver.

The selected producer derives Completes for every processed receipt from
those same admitted/history witnesses. Its old complete wrapper projects
away only the new history and callback conclusions. No callback is inserted
into NativeBranches.run, and no future-success premise is added to Ranges.

## Source branch metadata and interleaving

Enumeration.hs:975 defines continue ost'. The source binds each alternative
fragment and calls oracle ost' for that alternative. The returned ost'' feeds
only that branch's recursive enumerateUntil' continuation at line 980.
The CPS bind at line 348 runs continuations depth first. Sibling callbacks
therefore use the same input metadata. A sequential metadata fold across
siblings is not a source requirement. Source readback corrects the earlier
review wording about such a fold; no Haskell repair is needed.

The formal scan still forces alternatives serially before these independent
callback receipts. It does not yet establish the source's exact shared native
effect history across callback and recursive-continuation demand. Independent
callback availability is the result proved here. Exact interleaving remains
open. Do not substitute the aggregate scan Caller for a receipt Caller.

## Verification and evidence

Lean 4.34.1 strictly checks all six changed modules with all linters and
warnings as errors. Nine strict attempts retain one failed first branch
check: unqualified State was ambiguous between the enumeration and interned
heap types. Qualification fixes it. A checked intermediate branch history
and ordinary transport are then strengthened with actual counter growth;
their corrected final strict checks pass. The other four modules pass first.

Three installed helper builds pass. Aggregate Audit passes with 3766 jobs
and 76834 theorem dependencies. Audit source is unchanged. Installed public
readback checks 17 declarations, including generic helpers, receipt predicates,
strengthened producers, preserved interfaces and H6. The full output has
{len(public.splitlines())} lines and {len(public_bytes)} bytes. Its SHA-256 is
`{sha(public_bytes)}`. No output ellipsis is present.
All axiom sets are subsets of propext, Classical.choice and Quot.sound.
The pre-existing unused inputs warning is unchanged. All fourteen checks
run serially under heavy-management 4 GiB caps with no swap.

Independent source reviews confirm the same actual prefix and per-receipt
witnesses, original parked-ID bound transport, rejection boundaries and the
legacy selected declaration type. Runtime preservation and unchanged Haskell
are checked directly against the base source. No Haskell suite is rerun
because no Haskell source or package file changes.

Evidence: lean/restart-evidence/20261026-native-receipt-history.
The manifest records each payload's exact bytes and SHA-256. It includes
commands, exit codes, complete public output, the failed check, final strict
source copies, final source snapshots, preserved old sources, proof diff,
verification report and memory-cap records. Force-add the exact manifest
payload list, including ignored raw.log files, and verify committed bytes.

## Next work and claim boundary

First retain native indexed-cache invariants through the actual callback
read frame: roots, realized pending handles, canonical waiting, candidate
flags and suspended-reference history. Safe alone does not supply this full
packet. Use the callback's actual receipt Caller and original branch cache.
Then compose the concrete callback with recursive continuation and scheduler
restart while retaining depth-first native effects and branch-local metadata.

Native Graph classification and concrete heap correspondence remain open.
Initial-only capacity forecasts still need all actual native query bounds.
Terminal/nonordinary outer parents retain their existing fallback boundary.
Scheduler language preservation, general pruning/order laws, arbitrary lazy
forcing, finite-machine containers and integers, extraction and complete
Haskell correspondence remain separate obligations.

H6 constructed_node_calls is unchanged. It remains the strongest end-to-end
language theorem: covered closed construction, valid initial constraint
history, any prescribed finite budget/rounds, derived sufficient finite fuels
and one mathematical width chosen after construction, and exact preservation
of the initial finite-tree language under the formal solver interfaces.
It does not prove the whole typing/pruning enumeration driver.
'''
(root / 'lean/notes-current-pruning-enumeration-receipt-history.md').write_text(note)
verification = {
    'base': base,
    'source_commits': ['59706bb3f', '0f8037add'],
    'main': '153e1a211b56dd78bd22f6b427fb78e673041d55',
    'checks': checks,
    'final_strict_modules': finals,
    'legacy_header_sha256': headers,
    'audit_dependencies': 76834,
    'public_declarations': 17,
    'public_lines': len(public.splitlines()),
    'public_bytes': len(public_bytes),
    'public_sha256': sha(public_bytes),
    'final_source_sha256': {rel: sha((root / rel).read_bytes()) for rel in sources},
    'unchanged_source_sha256': {rel: sha((root / rel).read_bytes()) for rel in unchanged},
    'runtime_workers_and_haskell_unchanged': True,
    'goal_status': 'active',
}
(area / 'verification.json').write_text(json.dumps(verification, indent=2) + '\n')
(area / 'proof-change.patch').write_bytes(subprocess.check_output(['git', 'diff', base, 'HEAD', '--', *sources], cwd=root))
for relative in sources + unchanged:
    destination = area / 'sources' / relative
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(root / relative, destination)
assert not evidence.exists()
shutil.copytree(area, evidence)
manifest = {str(path.relative_to(evidence)): {'bytes': path.stat().st_size, 'sha256': sha(path.read_bytes())}
            for path in sorted(evidence.rglob('*')) if path.is_file()}
(evidence / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps({'payloads': len(manifest), 'bytes': sum(item['bytes'] for item in manifest.values()),
                  'manifest_sha256': sha((evidence / 'manifest.json').read_bytes())}))
