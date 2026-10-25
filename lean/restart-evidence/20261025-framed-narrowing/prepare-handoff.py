import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-framed-narrowing-20261025')
evidence = root / 'lean/restart-evidence/20261025-framed-narrowing'
base = 'c43e8e64d2b0e8f87cadc883a89bc65b8a104802'
block = '''## Original selection reaches native narrowing and the Right callback

Framed replacement: `fc1e38a19`. Cache and Caller: `93d621a5c`.
Selected composition: `5106259fa`. The goal stays ACTIVE.

Original selection now derives the single pending read, native recursion
guard and, on the false branch, narrowing's full Caller and indexed-cache
result. The proof uses the actual guard frame and genuine endpoint Ready.
The same fuel, native result heap, memos and enumeration endpoint persist.
The concrete nonempty Right callback returns false and all original metadata
at that same cache. Repeated recursion retains its actual parked receipt.
No new selection, second initial read or early entry ancestry update occurs.
The three older producer interfaces retain their exact types.

All five strict checks pass on their first attempts. Public readback and
Audit pass. Audit checks 76734 dependencies. H6 remains the strongest
end-to-end language result. Haskell is unchanged. Next: compose ordinary
entry/expansion at this reached Caller/cache with its actual numeric Ranges.
Terminal/nonordinary outcomes, scheduler restart, the Left callback, fragment
history, extraction and whole-driver language semantics remain open.
Details: `lean/notes-current-pruning-enumeration-selected-narrow.md`.

'''
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/COVERAGE.md', 'lean/API-COVERAGE.md',
             'lean/notes-current-system-claim.md', 'lean/notes-proof-status-20261017.md']
for relative in documents:
    path = root / relative
    text = path.read_text()
    marker = '## Selected reads and native recursion checks complete'
    assert marker in text and block.splitlines()[0] not in text
    path.write_text(text.replace(marker, block + marker, 1))
path = root / 'FINDINGS.md'
text = path.read_text()
marker = '### Native repeated-recursion clearing and source order'
addition = '''### Actual guard frames through narrowing and the Right callback

A false native recursion guard can compress representatives between the
source's initial value read and narrowing's later representative reread.
The cache and Caller producers now accept that actual frame and genuine
endpoint Ready. Their original interfaces keep their exact declaration types.
Original selection, one read, the native guard and narrowing now compose at
the same result heap and cache. The concrete pre-expansion Right callback
uses the new narrowed handle and retains all metadata and enumeration state.
The repeated branch parks without narrowing. Empty rejects before the callback.
Whole-driver semantics and arbitrary callback preservation remain open.
No new Haskell runtime defect or repair is found.
External action: no patch is proposed for this source observation.
Details: lean/notes-current-pruning-enumeration-selected-narrow.md.

'''
assert addition.splitlines()[0] not in text
path.write_text(text.replace(marker, addition + marker, 1))
assert path.read_text().index('## Haskell fix handoff') < path.read_text().index(block.splitlines()[0])

sha = lambda data: hashlib.sha256(data).hexdigest()
checks = {p.parent.name: json.loads(p.read_text()) for p in sorted(area.glob('*/report.json'))}
assert len(checks) == 10 and all(r['exit_code'] == 0 for r in checks.values())
strict = {name for name in checks if '-strict-' in name}
assert len(strict) == 5
assert strict == {'replacement-frame-strict-1', 'narrow-cache-frame-strict-1',
                  'narrow-context-frame-strict-1', 'selected-narrow-strict-1', 'audit-import-strict-1'}
evidence.mkdir()
for name in checks:
    shutil.copytree(area / name, evidence / name)
for name in ['check.py', 'prepare-handoff.py', 'heavy-peaks',
             'original-replacement-header.txt', 'original-narrow-cache-header.txt', 'original-narrow-context-header.txt']:
    shutil.copyfile(area / name, evidence / name)
for name, report in checks.items():
    raw = (evidence / name / 'raw.log').read_bytes()
    assert len(raw) == report['bytes'] and sha(raw) == report['sha256']
    if name in strict:
        source = next((evidence / name / 'MicroCFTA').glob('*.lean'))
        assert sha(source.read_bytes()) == report['source_sha256']
        assert source.read_bytes() == (root / 'lean/MicroCFTA' / source.name).read_bytes()
        if source.name != 'Audit.lean':
            assert not raw
        else:
            assert raw.decode().strip() == 'Checked axiom dependencies of 76734 MicroCFTA theorems.'
public_bytes = (evidence / 'public-final/raw.log').read_bytes()
public = public_bytes.decode()
assert public.count('depends on axioms:') == 8 and '⋯' not in public and '...' not in public
assert sha((evidence / 'public-final/public.lean').read_bytes()) == checks['public-final']['source_sha256']
for axioms in re.findall(r'depends on axioms:\s*\[([^]]*)\]', public):
    assert set(re.findall(r'[A-Za-z_.]+', axioms)) <= {'propext', 'Classical.choice', 'Quot.sound'}
assert 'Checked axiom dependencies of 76734 MicroCFTA theorems.' in (evidence / 'aggregate-audit/raw.log').read_text()

sources = ['lean/MicroCFTA/' + name + '.lean' for name in [
    'SourcePruningEnumerationReplacement', 'SourcePruningEnumerationNarrowCache',
    'SourcePruningEnumerationNarrowContext', 'SourcePruningEnumerationSelectedNarrow', 'Audit']]
snapshots = sources + ['lean/MicroCFTA/' + name + '.lean' for name in [
    'SourceCurrentColdFiniteWarmCalls', 'SourcePruningEnumerationAction', 'SourcePruningEnumerationRecursion',
    'SourcePruningEnumerationSelection', 'SourcePruningEnumerationEntry', 'SourcePruningRecordTypes',
    'SourcePruningEnumerationNativeOrdinary', 'SourcePruningNativeContext']]
snapshots += ['cfta/src/Data/CFTA/Enumeration.hs']
for relative in snapshots:
    target = evidence / 'sources' / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(root / relative, target)
    if relative in sources[:4]:
        assert not re.search(r'\b(sorry|admit|axiom)\b', (root / relative).read_text())
        assert not re.search(r'^(?:noncomputable )?def ', (root / relative).read_text(), re.M)
old_source = lambda relative: subprocess.check_output(['git', 'show', base + ':' + relative], cwd=root).decode()
unchanged = ['lean/MicroCFTA/' + name + '.lean' for name in [
    'EnumerationDriver', 'SourcePruningEnumerationEntry', 'SourcePruningEnumerationSelection',
    'SourcePruningEnumerationAction', 'SourcePruningEnumerationRecursion', 'SourcePruningEnumerationClear',
    'SourcePruningNativeContext', 'SourcePruningEnumerationNativeIndex',
    'SourcePruningOuterNarrow', 'SourcePruningNativeView', 'SourcePruningEnumerationNativeOrdinary',
    'SourcePruningEnumerationNativeBranchCompletion', 'SourcePruningEnumerationNativeBranches',
    'SourcePruningEnumerationSelectedEntry', 'SourcePruningRecordTypes', 'SourceCurrentColdFiniteWarmCalls']]
unchanged += ['cfta/src/Data/CFTA/' + name for name in [
    'Enumeration.hs', 'Interned/Type.hs', 'Interned/Cache.hs', 'Interned/Memo.hs', 'Interned/Operations.hs']]
for relative in unchanged:
    assert old_source(relative) == (root / relative).read_text(), relative
subprocess.run(['git', 'diff', '--quiet', base, '--', '*.hs', '*.cabal'], cwd=root, check=True)
assert (root / sources[4]).read_text() == ('import MicroCFTA.SourcePruningEnumerationSelectedNarrow\n' + old_source(sources[4]))
interfaces = [('SourcePruningEnumerationReplacement', 'after_read', 'replacement'),
              ('SourcePruningEnumerationNarrowCache', 'complete', 'narrow-cache'),
              ('SourcePruningEnumerationNarrowContext', 'complete', 'narrow-context')]
headers = {}
for module, name, filename in interfaces:
    relative = 'lean/MicroCFTA/' + module + '.lean'
    def header(text):
        start = text.index('theorem ' + name + '\n')
        return text[start:text.index(' := by\n', start)]
    old = header(old_source(relative))
    current = header((root / relative).read_text())
    assert old == current
    saved = (evidence / ('original-' + filename + '-header.txt')).read_text()
    assert old in saved
    headers[module + '.' + name] = sha(old.encode())
(evidence / 'proof-change.patch').write_bytes(subprocess.check_output(
    ['git', 'diff', base, 'HEAD', '--', 'lean/MicroCFTA'], cwd=root))
summary = dict(base=base, proof_head=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
               checks=10, strict_attempts=5, rejected_strict_attempts=0, final_strict_modules=5,
               public_declarations=8, audit_dependencies=76734, public_lines=len(public.splitlines()),
               public_bytes=len(public_bytes), public_sha256=sha(public_bytes), unchanged_paths=unchanged,
               new_runtime_workers=0, preserved_declaration_type_sha256=headers, audit_changes='one import only',
               prefix_scope='through native narrowing and pure Right callback; before ordinary entry or scheduler restart',
               memo_fuel_scope='chosen native exposure fuel only',
               source_sha256={p: sha((root / p).read_bytes()) for p in snapshots})
(evidence / 'verification.json').write_text(json.dumps(summary, indent=2) + '\n')
manifest = {str(p.relative_to(evidence)): dict(bytes=p.stat().st_size, sha256=sha(p.read_bytes()))
            for p in sorted(evidence.rglob('*')) if p.is_file()}
(evidence / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps(dict(payloads=len(manifest), total_bytes=sum(v['bytes'] for v in manifest.values()),
                     manifest_sha256=sha((evidence / 'manifest.json').read_bytes()))))
