import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-selected-ordinary-20261025')
evidence = root / 'lean/restart-evidence/20261025-selected-ordinary'
base = '3891a08671aaa949f64ad90d5dc8e48f31d55997'
block = '''## Original selection reaches admitted ordinary expansion

Per-receipt Caller/memos: `8d8693df7`. Selected composition: `82bfc44ff`.
The goal stays ACTIVE.

Original selection now connects through read, native guard, narrowing, pure
Right callback and admitted ordinary entry/scan. The ordinary continuation
uses the actual narrowed Caller/cache/memos. Each processed alternative now
retains its actual advance endpoint and full prefix Post from the original
Caller, plus its own cache and pending-reference certificate.
Initial global pending history is a genuine input. Ordinary node shape,
nonterminal bucket, selected narrowed rows and reached-state Ranges remain
explicit conditions. Parked, Empty and unsupported outcomes stay exact.
Both older completion interfaces retain their declaration types.

All strict checks, public readback and Audit pass. Audit checks 76737
dependencies. H6 remains the strongest end-to-end language result. Haskell
is unchanged. Next: branch-endpoint Left callbacks, initial-only capacity
forecasts, fragment-hole history and extraction. The serial scan does not
establish arbitrary Haskell forcing or callback interleaving. Scheduler
restart and whole-driver language semantics remain open.
Details: `lean/notes-current-pruning-enumeration-selected-ordinary.md`.

'''
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/COVERAGE.md', 'lean/API-COVERAGE.md',
             'lean/notes-current-system-claim.md', 'lean/notes-proof-status-20261017.md']
for relative in documents:
    path = root / relative
    text = path.read_text()
    marker = '## Original selection reaches native narrowing and the Right callback'
    assert marker in text and block.splitlines()[0] not in text
    path.write_text(text.replace(marker, block + marker, 1))
path = root / 'FINDINGS.md'
text = path.read_text()
marker = '### Actual guard frames through narrowing and the Right callback'
addition = '''### Native ordinary alternatives retain their own caller receipts

The selected model prefix now connects to admitted ordinary entry and scan
at the actual narrowed Caller/cache. Each processed receipt has its own
actual advance result, full prefix Caller Post and valid saved memos.
The proof retains existing intermediate witnesses. It does not rerun a
producer or substitute the aggregate final heap for a branch endpoint.
The original completion interfaces retain their exact declaration types.
Rendered Left callbacks must use those branch endpoints. Exact forcing and
callback interleaving, fragment history and whole-driver semantics stay open.
Initial-only machine-key admission needs a quantitative scheduler forecast.
No new Haskell runtime defect or repair is found.
External action: no patch is proposed for this source observation.
Details: lean/notes-current-pruning-enumeration-selected-ordinary.md.

'''
assert addition.splitlines()[0] not in text
path.write_text(text.replace(marker, addition + marker, 1))
assert path.read_text().index('## Haskell fix handoff') < path.read_text().index(block.splitlines()[0])

sha = lambda data: hashlib.sha256(data).hexdigest()
checks = {p.parent.name: json.loads(p.read_text()) for p in sorted(area.glob('*/report.json'))}
assert len(checks) == 10 and all(r['exit_code'] == 0 for r in checks.values())
strict = {name for name in checks if '-strict-' in name}
assert len(strict) == 6
final_strict = {'branch-posts-strict-2', 'ordinary-posts-strict-1', 'selected-ordinary-strict-2', 'audit-import-strict-1'}
evidence.mkdir()
for name in checks:
    shutil.copytree(area / name, evidence / name)
for name in ['check.py', 'prepare-handoff.py', 'heavy-peaks', 'original-branch-header.txt', 'original-ordinary-header.txt']:
    shutil.copyfile(area / name, evidence / name)
for name, report in checks.items():
    raw = (evidence / name / 'raw.log').read_bytes()
    assert len(raw) == report['bytes'] and sha(raw) == report['sha256']
    if name in strict:
        source = next((evidence / name / 'MicroCFTA').glob('*.lean'))
        assert sha(source.read_bytes()) == report['source_sha256']
        if name in final_strict:
            assert source.read_bytes() == (root / 'lean/MicroCFTA' / source.name).read_bytes()
            if source.name != 'Audit.lean':
                assert not raw
            else:
                assert raw.decode().strip() == 'Checked axiom dependencies of 76737 MicroCFTA theorems.'
public_bytes = (evidence / 'public-final/raw.log').read_bytes()
public = public_bytes.decode()
assert public.count('depends on axioms:') == 7 and '⋯' not in public and '...' not in public
assert sha((evidence / 'public-final/public.lean').read_bytes()) == checks['public-final']['source_sha256']
for axioms in re.findall(r'depends on axioms:\s*\[([^]]*)\]', public):
    assert set(re.findall(r'[A-Za-z_.]+', axioms)) <= {'propext', 'Classical.choice', 'Quot.sound'}
assert 'Checked axiom dependencies of 76737 MicroCFTA theorems.' in (evidence / 'aggregate-audit/raw.log').read_text()

sources = ['lean/MicroCFTA/' + name + '.lean' for name in [
    'SourcePruningEnumerationNativeBranchCompletion', 'SourcePruningEnumerationNativeOrdinary',
    'SourcePruningEnumerationSelectedOrdinary', 'Audit']]
snapshots = sources + ['lean/MicroCFTA/' + name + '.lean' for name in [
    'SourceCurrentColdFiniteWarmCalls', 'SourcePruningEnumerationSelectedNarrow',
    'SourcePruningEnumerationAction', 'SourcePruningEnumerationRecursion', 'SourcePruningRecordTypes',
    'SourcePruningEnumerationNativeBranches', 'SourceCurrentAllocatedNativeRequestBounds',
    'SourceCurrentAllocatedRecursiveWarmInitialRanges']]
snapshots += ['cfta/src/Data/CFTA/Enumeration.hs', 'cfta/src/Data/CFTA/Interned/Type.hs']
for relative in snapshots:
    target = evidence / 'sources' / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(root / relative, target)
    if relative in sources[:3]:
        assert not re.search(r'\b(sorry|admit|axiom)\b', (root / relative).read_text())
old_source = lambda relative: subprocess.check_output(['git', 'show', base + ':' + relative], cwd=root).decode()
unchanged = ['lean/MicroCFTA/' + name + '.lean' for name in [
    'EnumerationDriver', 'SourcePruningEnumerationEntry', 'SourcePruningEnumerationSelection',
    'SourcePruningEnumerationAction', 'SourcePruningEnumerationRecursion', 'SourcePruningEnumerationClear',
    'SourcePruningEnumerationSelectedNarrow', 'SourcePruningEnumerationNarrowContext', 'SourcePruningEnumerationNarrowCache',
    'SourcePruningEnumerationCapturedEdge', 'SourcePruningEnumerationSelectedEdge',
    'SourcePruningEnumerationNativeBranches', 'SourcePruningRecordTypes', 'SourceCurrentColdFiniteWarmCalls',
    'SourceCurrentAllocatedNativeRequestBounds', 'SourceCurrentAllocatedRecursiveWarmInitialRanges']]
unchanged += ['cfta/src/Data/CFTA/' + name for name in [
    'Enumeration.hs', 'Interned/Type.hs', 'Interned/Cache.hs', 'Interned/Memo.hs', 'Interned/Operations.hs']]
for relative in unchanged:
    assert old_source(relative) == (root / relative).read_text(), relative
subprocess.run(['git', 'diff', '--quiet', base, '--', '*.hs', '*.cabal'], cwd=root, check=True)
assert (root / sources[3]).read_text() == ('import MicroCFTA.SourcePruningEnumerationSelectedOrdinary\n' + old_source(sources[3]))
interfaces = [('SourcePruningEnumerationNativeBranchCompletion', 'branch'),
              ('SourcePruningEnumerationNativeOrdinary', 'ordinary')]
headers = {}
for module, filename in interfaces:
    relative = 'lean/MicroCFTA/' + module + '.lean'
    old = old_source(relative)
    current = (root / relative).read_text()
    def header(text):
        start = text.index('theorem complete\n')
        return text[start:text.index(' := by\n', start)]
    assert header(old) == header(current)
    saved = (evidence / ('original-' + filename + '-header.txt')).read_text().rstrip()
    assert header(old) in saved
    assert old[:old.index(saved)] == current[:current.index('/-- Each processed alternative' if filename == 'branch' else '/-- Actual ready entry retains')]
    headers[module + '.complete'] = sha(header(old).encode())
ordinary = 'lean/MicroCFTA/SourcePruningEnumerationNativeOrdinary.lean'
marker = '/-- Actual selection derives ready entry'
assert old_source(ordinary)[old_source(ordinary).index(marker):] == (root / ordinary).read_text()[(root / ordinary).read_text().index(marker):]
assert not re.search(r'^(?:noncomputable )?def ', (root / sources[2]).read_text(), re.M)
(evidence / 'proof-change.patch').write_bytes(subprocess.check_output(
    ['git', 'diff', base, 'HEAD', '--', 'lean/MicroCFTA'], cwd=root))
summary = dict(base=base, proof_head=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
               checks=10, strict_attempts=6, rejected_strict_attempts=0, final_strict_modules=4,
               public_declarations=7, audit_dependencies=76737, public_lines=len(public.splitlines()),
               public_bytes=len(public_bytes), public_sha256=sha(public_bytes), unchanged_paths=unchanged,
               new_runtime_workers=0, preserved_declaration_type_sha256=headers, audit_changes='one import only',
               admission_scope='ordinary node, nonterminal bucket, actual selected-row membership, reached-state Ranges',
               prefix_scope='through admitted ordinary serial scan; before Left callbacks or scheduler restart',
               source_sha256={p: sha((root / p).read_bytes()) for p in snapshots})
(evidence / 'verification.json').write_text(json.dumps(summary, indent=2) + '\n')
manifest = {str(p.relative_to(evidence)): dict(bytes=p.stat().st_size, sha256=sha(p.read_bytes()))
            for p in sorted(evidence.rglob('*')) if p.is_file()}
(evidence / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps(dict(payloads=len(manifest), total_bytes=sum(v['bytes'] for v in manifest.values()),
                     manifest_sha256=sha((evidence / 'manifest.json').read_bytes()))))
