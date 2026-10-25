import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-native-fragment-history-20261025')
evidence = root / 'lean/restart-evidence/20261025-native-fragment-history'
base = 'c1db1b0512c22f9f7772189a7f883c35024b4c68'
sha = lambda data: hashlib.sha256(data).hexdigest()
old_source = lambda relative: subprocess.check_output(['git', 'show', base + ':' + relative], cwd=root).decode()
checks = {p.parent.name: json.loads(p.read_text()) for p in sorted(area.glob('*/report.json'))}
strict = {name for name in checks if name.startswith('strict-')}
failed = {name for name, report in checks.items() if report['exit_code'] != 0}
assert len(checks) == 17 and len(strict) == 11
assert failed == {'strict-child-history-1', 'strict-child-history-2',
                  'strict-selected-history-1', 'strict-traversal-history-1'}
final_strict = {'strict-fragment-history-2', 'strict-stratified-transport-1', 'strict-child-history-3',
                'strict-traversal-history-2', 'strict-selected-history-2', 'strict-captured-history-1'}
assert not failed.intersection(final_strict)
public_bytes = (area / 'public-final/raw.log').read_bytes()
public = public_bytes.decode()
assert public.count('depends on axioms:') == 14 and '⋯' not in public and '...' not in public
for axioms in re.findall(r'depends on axioms:\s*\[([^]]*)\]', public):
    assert set(re.findall(r'[A-Za-z_.]+', axioms)) <= {'propext', 'Classical.choice', 'Quot.sound'}
assert 'Checked axiom dependencies of 76825 MicroCFTA theorems.' in (area / 'aggregate-audit/raw.log').read_text()

modules = ['EnumerationFragmentHistory', 'EnumerationStratifiedTransport',
           'SourcePruningEnumerationChildCompletion', 'SourcePruningEnumerationTraversalCompletion',
           'SourcePruningEnumerationSelectedEdge', 'SourcePruningEnumerationCapturedEdge']
sources = ['lean/MicroCFTA/' + name + '.lean' for name in modules]
headers = {}
for module, short in zip(modules[2:], ['child', 'traversal', 'selected', 'captured']):
    relative = 'lean/MicroCFTA/' + module + '.lean'
    old = old_source(relative)
    current = (root / relative).read_text()
    start = current.index('theorem complete\n')
    header = current[start:current.index(' := by\n', start)]
    old_start = old.index('theorem complete\n')
    old_header = old[old_start:old.index(' := by\n', old_start)]
    assert header == old_header == (area / ('original-' + short + '-header.txt')).read_text().rstrip(), module
    headers[module + '.complete'] = sha(header.encode())
    prefix = current
    for extra in ['import MicroCFTA.EnumerationFragmentHistory\n', 'import MicroCFTA.EnumerationStratifiedTransport\n']:
        prefix = prefix.replace(extra, '', 1)
    assert prefix[:prefix.index('theorem complete_with_')].rsplit('/--', 1)[0] == old[:old_start].rsplit('/--', 1)[0], module
    new_start = current.index('theorem complete_with_')
    new_header = current[new_start:current.index(' := by\n', new_start)]
    assert new_header[new_header.index('\n'):].split(' :\n    ∃', 1)[0] == header[header.index('\n'):].split(' :\n    ∃', 1)[0], module
traversal = sources[3]
marker = '/-- Enumerated origin and protected old roots retain every separate parent bucket. -/'
assert old_source(traversal)[old_source(traversal).index(marker):] == (root / traversal).read_text()[(root / traversal).read_text().index(marker):]
unchanged = ['lean/MicroCFTA/' + name + '.lean' for name in [
    'Audit', 'EnumerationState', 'EnumerationCorrectness', 'EnumerationOrder', 'EnumerationReferences',
    'EnumerationDriver', 'EnumerationPartialCompletion', 'EnumerationPartialBounds',
    'SourcePruningCallbackCompletion', 'SourcePruningRecordTypes', 'SourcePruningEnumerationFinalize',
    'SourcePruningEnumerationChildDispatch', 'SourcePruningEnumerationCachedTerminalAdapter',
    'SourcePruningEnumerationNativeBranches', 'SourcePruningEnumerationNativeBranchCompletion',
    'SourcePruningEnumerationNativeOrdinary', 'SourcePruningEnumerationSelectedOrdinary',
    'SourcePruningEnumerationSelectedNarrow', 'SourcePruningEnumerationAction', 'SourceCurrentColdFiniteWarmCalls']]
unchanged += ['cfta/src/Data/CFTA/' + name for name in [
    'Enumeration.hs', 'Interned/Type.hs', 'Interned/Cache.hs', 'Interned/Memo.hs', 'Interned/Operations.hs']]
for relative in unchanged:
    assert old_source(relative) == (root / relative).read_text(), relative
subprocess.run(['git', 'diff', '--quiet', base, '--', '*.hs', '*.cabal'], cwd=root, check=True)
for relative in sources:
    assert not re.search(r'\b(sorry|admit|axiom)\b', (root / relative).read_text()), relative

block = '''## Native captured edges preserve fragment dependency history

Child and traversal history: `9c3091a3a`. Native finalization: `4b23cd411`.
The goal stays ACTIVE.

Admitted native child completion now derives pending targets for returned
holes and separation from protected parent classes. Traversal retains
both facts through the actual successful suffix. Selected-edge completion
retains them after residual recording. The same actual captured-slot write
then preserves pending targets and advances every initial Stratified order
to frontier+1. No new producer admission input is added. All four older
complete interfaces retain their exact declaration types.

All six changed modules pass strict checking. Installed public readback
and Audit pass. Audit checks 76825 dependencies. H6 remains the strongest
end-to-end language result. Haskell and Audit source stay unchanged.
Next: propagate these histories through actual alternative receipts and
selected-prefix composition, then run concrete Left callbacks at each
receipt's own cache/Caller/memos. Preserve initial stratification through
the preceding read, guard and narrowing steps. Native Graph classification,
initial-only capacity, scheduler restart, forcing, extraction and whole-driver
language semantics remain open. Rejected caches gain no Safe/rank promise.
Details: `lean/notes-current-pruning-enumeration-fragment-history.md`.

'''
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/COVERAGE.md', 'lean/API-COVERAGE.md',
             'lean/notes-current-system-claim.md', 'lean/notes-proof-status-20261017.md']
for relative in documents:
    path = root / relative
    text = path.read_text()
    marker = '## Concrete callbacks preserve allocated pending IDs'
    assert marker in text and block.splitlines()[0] not in text
    path.write_text(text.replace(marker, block + marker, 1))
path = root / 'FINDINGS.md'
text = path.read_text()
marker = '### Returned callback pending IDs stay allocated'
addition = '''### Native fragment dependencies survive captured finalization

The admitted native captured-edge model now derives pending targets and
protected-parent separation for returned fragment holes. Child traversal
retains both facts through actual suffix states. Finalization uses the same
captured raw slot and the same indexed write witness. It derives pending
targets after that write and frontier+1 from any initial Stratified order.
No producer input, runtime worker or older completion type changes.
This closes fragment-history preservation for the admitted captured-edge
path. Alternative receipt integration and whole-driver semantics remain open.
It identifies no Haskell runtime defect. External action: no new patch is
proposed. Keep the external repair table and Sized documentation repair above.
Details: lean/notes-current-pruning-enumeration-fragment-history.md.

'''
assert addition.splitlines()[0] not in text
path.write_text(text.replace(marker, addition + marker, 1))
assert path.read_text().index('## Haskell fix handoff') < path.read_text().index(block.splitlines()[0])

note = f'''# Native fragment history through captured finalization

## Current result

Generic history and native child traversal: `9c3091a3a`.
Selected edge and captured finalization: `4b23cd411`.
Main remains `153e1a211b56dd78bd22f6b427fb78e673041d55`.
The whole formalization goal stays ACTIVE.

The admitted native captured-edge producer now derives pending targets for
its returned holes and the next dependency frontier. Its inputs stay exact.
The rank result is conditional on a genuine initial Stratified order and
belongs to the same actual successful finalization witness. It supplies
the acyclic fragment-history fact needed by finite partial rendering.
It does not yet compose an alternative receipt with its concrete callback.

## Pending targets and protected classes

EnumerationDependencies.PendingFragment records an actual root path and
pending stored slot for every returned fragment hole. It differs from
PendingReferences, which concerns suspended equality references.

pendingFragment_preserved transports those targets through later safe
storage, allocation growth, enumerated origin and protection of earlier
expanded classes. The actual final root stays allocated. Safe storage
excludes eliminated roots. If that root were expanded, its protected old
class would contradict the earlier pending-root receipt.
pendingFragment_write retains the targets through a separate captured-slot
write. It uses actual class separation to exclude that target as a hole root.

EnumerationOrder.stratified_preserved reconstructs levels from actual final
roots. Preserved expanded slots keep their old levels. Other classes receive
the current frontier. Enumerated origin and protected expanded classes
retain the strict dependency order. No Graph or future execution premise
is needed. An unused proposed before-Safe argument is removed before checking.

## Actual native producers

ChildCompletion.complete_with_fragments derives history without new inputs.
The nonterminal branch returns the fresh raw hole. Its unchanged forest,
Safe storage and origin receipt supply an actual pending slot and exclude
older protected classes. The terminal branch retains the actual winnerStored,
winnerMember and representative-root witnesses. These supply pending targets
and parent separation at the same final cache. Empty/rejected branches keep
their original receipts and gain no Safe or fragment-history promise.

TraversalCompletion.complete_with_fragments transports the first child's
pending targets through the actual successful suffix. It transports parent
separation through the same held-class frame. Later children retain their
own final pending targets, and their separation uses the root protected
through the head. The source still runs children in their original order.

SelectedEdge.complete_with_fragments combines the actual child fragments
under the selected symbol. Residual recording changes obligations only.
The resulting fragment retains pending targets and parent separation at
its actual completed cache. No successful child or final fragment is supplied
as an admission premise.

CapturedEdge.complete_with_history calls that producer once and retains the
same Finalize.complete witness as before. Ready and the protected parent
receipt identify the original captured raw slot. The proof supplies actual
pending targets and separation to write_stratified. Earlier expanded classes
first retain a valid middle order through stratified_preserved. The actual
write then advances the frontier by one. Ancestry reset preserves that order.
pendingFragment_write also proves that all returned holes still resolve to
pending slots after the parent fragment is stored.

The four older complete declarations remain exact-type projection wrappers.
Strengthened producers retain identical input binders and numeric Ranges.
Runtime workers, native queries, indexed writes and forcing order do not change.
Rejection branches receive no new Safe, pending-fragment or rank assertion.

## Verification and evidence

All six changed modules pass Lean 4.34.1 with all linters and warnings as
errors. Eleven strict attempts contain four retained failures: child symbol
inference, an unsuitable named-argument repair under local Symbol notation,
traversal variable substitution, and dependent elimination before exposing
the selected node shape. The corrected six final module checks pass.
The initial generic transport version also passes before the write helper
is appended. Captured finalization passes its first strict attempt.

Four installed helper builds pass. Aggregate Audit passes with 3763 jobs
and 76825 checked dependencies. Audit source stays byte-identical.
Installed public readback checks five generic helpers, four strengthened
producers, four preserved interfaces and H6. Its full output has
{len(public.splitlines())} lines and {len(public_bytes)} bytes. Its SHA-256 is
`{sha(public_bytes)}`.
All axiom sets are subsets of propext, Classical.choice and Quot.sound.
The old unused inputs warning remains unchanged. All seventeen checks run
serially under 4 GiB heavy-management caps with no swap.

Source reviews confirm actual suffix endpoints, the same final write witness,
conditional frontier advancement and the rejection boundary. Preservation
checks compare all four older headers byte for byte and all strengthened
input lists. Runtime prefixes remain exact apart from new imports and theorem
comments. Older sources and headers remain in the evidence package.
H6, callback proofs, native worker bodies and all Haskell sources stay exact.
No Haskell suite is repeated. No new Haskell defect or repair is found.
Root FINDINGS keeps the external Haskell handoff first.
Full attempted inputs, logs, reports, source snapshots, original headers,
proof patch and cap records remain in
restart-evidence/20261025-native-fragment-history.

## Remaining work and strongest claim

Propagate the new histories through NativeBranches and every successful
alternative receipt. The current legacy wrappers intentionally discard them.
Preserve initial Stratified through original selection, read, native recursion
checks, narrowing and ordinary entry. Then use each successful receipt's own
Caller, memos, queries and cache for concrete Left callback completion.
The aggregate scan's final Caller cannot replace an earlier branch endpoint.

Native Graph.node classification and actual handle decoding still need a
correspondence proof for rendering semantics. Initial-only numeric admission
needs the existing scheduler-specific capacity forecast. Terminal/nonordinary
parent dispatch, parked restart, arbitrary Haskell forcing, callback/loop
interleaving, extraction and whole-driver language semantics remain open.
No full scheduler termination or convergence is proved.

H6 remains the strongest end-to-end language theorem. Covered closed
construction, a valid initial cache, original allocation history and any
prescribed finite budget and modeled node-call rounds derive sufficient
finite bounds and one mathematical width chosen after construction. With
empty inherited payload, the final available value has exactly the original
finite-tree language under the formal formula and entailment interfaces.
Concrete solver and physical runtime correspondence remain outside that claim.
'''
(root / 'lean/notes-current-pruning-enumeration-fragment-history.md').write_text(note)

evidence.mkdir()
for name in checks:
    shutil.copytree(area / name, evidence / name)
for name in ['check.py', 'prepare-handoff.py', 'stage.py', 'heavy-peaks']:
    shutil.copyfile(area / name, evidence / name)
for short in ['child', 'traversal', 'selected', 'captured']:
    shutil.copyfile(area / ('original-' + short + '-header.txt'), evidence / ('original-' + short + '-header.txt'))
for name, report in checks.items():
    raw = (evidence / name / 'raw.log').read_bytes()
    assert len(raw) == report['bytes'] and sha(raw) == report['sha256']
    if name in strict:
        source = next((evidence / name / 'MicroCFTA').glob('*.lean'))
        assert sha(source.read_bytes()) == report['source_sha256']
        if name in final_strict:
            assert source.read_bytes() == (root / 'lean/MicroCFTA' / source.name).read_bytes()
            assert not raw
assert sha((evidence / 'public-final/public.lean').read_bytes()) == checks['public-final']['source_sha256']
snapshots = sources + unchanged
for relative in snapshots:
    target = evidence / 'sources' / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(root / relative, target)
for relative in sources[2:]:
    target = evidence / 'original-sources' / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(old_source(relative))
(evidence / 'proof-change.patch').write_bytes(subprocess.check_output(
    ['git', 'diff', base, 'HEAD', '--', 'lean/MicroCFTA'], cwd=root))
summary = dict(base=base, proof_head=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
               checks=17, strict_attempts=11, rejected_strict_attempts=4, final_strict_modules=6,
               public_declarations=14, audit_dependencies=76825, public_lines=len(public.splitlines()),
               public_bytes=len(public_bytes), public_sha256=sha(public_bytes), unchanged_paths=unchanged,
               preserved_declaration_type_sha256=headers, strengthened_producer_inputs='byte-identical',
               old_runtime_prefixes='byte-identical after removing new imports and theorem comments',
               new_runtime_workers=0, audit_changes='none',
               admission_scope='original native producer premises and Ranges; rank is an initial-state conditional output',
               native_captured_fragment_history=True, alternative_receipt_history=False,
               full_driver_language=False,
               source_sha256={p: sha((root / p).read_bytes()) for p in snapshots})
(evidence / 'verification.json').write_text(json.dumps(summary, indent=2) + '\n')
manifest = {str(p.relative_to(evidence)): dict(bytes=p.stat().st_size, sha256=sha(p.read_bytes()))
            for p in sorted(evidence.rglob('*')) if p.is_file()}
(evidence / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps(dict(payloads=len(manifest), total_bytes=sum(v['bytes'] for v in manifest.values()),
                     manifest_sha256=sha((evidence / 'manifest.json').read_bytes()))))
