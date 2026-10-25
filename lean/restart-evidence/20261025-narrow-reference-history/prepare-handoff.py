import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-narrow-reference-history-20261025')
evidence = root / 'lean/restart-evidence/20261025-narrow-reference-history'
base = '3c0f3f2c39bd16d1db41dd8f549a065b624c5815'
block = '''## Native narrowing retains pending-reference history

Compression and replacement: `0ab9d22a9`. Producer: `111c8d8fb`.
The goal stays ACTIVE.

The existing native narrowing producer now returns incoming-reference and
global pending-reference preservation on its actual entry and changed-handle
final-state witnesses. Compression retains values and classes. A pending
handle replacement retains the same suspended bucket. No new Safe premise,
producer input or runtime body is added. The concrete typing callback already
has a full frame receipt to which the new transport theorems apply.

Both strict modules, installed public readback and Audit pass. The audit checks
76716 theorem dependencies. H6 remains the strongest end-to-end language result.
Haskell is unchanged. Next: the native indexed replacement adapter, then actual
selection/read/narrow/callback/ordinary-entry composition. The new outputs
alone do not preserve the changed node's expandable flag. Fragment-hole history,
extraction, terminal parents and whole-driver semantics remain open.
Details: `lean/notes-current-pruning-enumeration-narrow-references.md`.

'''
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/COVERAGE.md', 'lean/API-COVERAGE.md',
             'lean/notes-current-system-claim.md', 'lean/notes-proof-status-20261017.md']
for relative in documents:
    path = root / relative
    text = path.read_text()
    marker = '## Selected ordinary alternatives retain pending references'
    assert marker in text and block.splitlines()[0] not in text
    path.write_text(text.replace(marker, block + marker, 1))
path = root / 'FINDINGS.md'
text = path.read_text()
marker = '### Selected references and the actual callback boundary'
addition = '''### Native narrowing reference preservation

The existing native narrowing theorem now retains incoming and global pending
reference history through actual reads and the actual changed-handle write.
The write keeps its suspended bucket. Generic full-frame transport also applies
to the existing concrete typing callback receipt, including compression.
The native indexed replacement and full selected-driver composition remain open.
In particular, narrowing can change the expandable flag of the stored node.
These are proof boundaries. No new Haskell runtime defect or repair is found.
External action: no patch is proposed for this source observation.
Details: lean/notes-current-pruning-enumeration-narrow-references.md.

'''
assert addition.splitlines()[0] not in text
path.write_text(text.replace(marker, addition + marker, 1))
assert path.read_text().index('## Haskell fix handoff') < path.read_text().index(block.splitlines()[0])

sha = lambda data: hashlib.sha256(data).hexdigest()
checks = {p.parent.name: json.loads(p.read_text()) for p in sorted(area.glob('*/report.json'))}
assert len(checks) == 5 and all(report['exit_code'] == 0 for report in checks.values())
strict = {name for name in checks if '-strict-' in name}
assert len(strict) == 2
evidence.mkdir()
for name in checks:
    shutil.copytree(area / name, evidence / name)
for name in ['check.py', 'prepare-handoff.py', 'heavy-peaks']:
    shutil.copyfile(area / name, evidence / name)
for name, report in checks.items():
    raw = (evidence / name / 'raw.log').read_bytes()
    assert len(raw) == report['bytes'] and sha(raw) == report['sha256']
    if name in strict:
        source = next((evidence / name / 'MicroCFTA').glob('*.lean'))
        assert sha(source.read_bytes()) == report['source_sha256'] and not raw
        assert source.read_bytes() == (root / 'lean/MicroCFTA' / source.name).read_bytes()
public_bytes = (evidence / 'public-final/raw.log').read_bytes()
public = public_bytes.decode()
assert public.count('depends on axioms:') == 6 and '⋯' not in public and '...' not in public
assert sha((evidence / 'public-final/public.lean').read_bytes()) == checks['public-final']['source_sha256']
for axioms in re.findall(r'depends on axioms:\s*\[([^]]*)\]', public):
    assert set(re.findall(r'[A-Za-z_.]+', axioms)) <= {'propext', 'Classical.choice', 'Quot.sound'}
assert 'Checked axiom dependencies of 76716 MicroCFTA theorems.' in (evidence / 'aggregate-audit/raw.log').read_text()

sources = ['lean/MicroCFTA/EnumerationPendingReplacement.lean', 'lean/MicroCFTA/SourcePruningEnumerationAction.lean']
snapshots = sources + ['lean/MicroCFTA/' + name + '.lean' for name in [
    'Audit', 'SourceCurrentColdFiniteWarmCalls', 'SourcePruningRecordTypes']]
snapshots += ['cfta/src/Data/CFTA/Enumeration.hs']
for relative in snapshots:
    target = evidence / 'sources' / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(root / relative, target)
    if relative in sources:
        assert not re.search(r'\b(sorry|admit|axiom)\b', (root / relative).read_text())
old_source = lambda relative: subprocess.check_output(['git', 'show', base + ':' + relative], cwd=root).decode()
unchanged = ['lean/MicroCFTA/' + name + '.lean' for name in [
    'SourcePruningEnumerationOuter', 'SourcePruningEnumerationNarrowing',
    'SourcePruningEnumerationReread', 'SourcePruningEnumerationWrites',
    'SourcePruningEnumerationNativeOrdinary', 'SourcePruningEnumerationNativeBranchCompletion',
    'SourcePruningEnumerationSelection', 'SourcePruningEnumerationSelectedEntry',
    'SourcePruningRecordTypes', 'SourcePruningOracle', 'SourceCurrentColdFiniteWarmCalls', 'Audit']]
unchanged += ['cfta/src/Data/CFTA/' + name for name in [
    'Enumeration.hs', 'Interned/Type.hs', 'Interned/Cache.hs', 'Interned/Memo.hs', 'Interned/Operations.hs']]
for relative in unchanged:
    assert old_source(relative) == (root / relative).read_text(), relative
subprocess.run(['git', 'diff', '--quiet', base, '--', '*.hs', '*.cabal'], cwd=root, check=True)

def definitions(text):
    pattern = r'^(?:noncomputable )?def (\w+)[\s\S]*?(?=^/--|^private theorem |^theorem |^variable |^end |\Z)'
    return {match.group(1): match.group(0) for match in re.finditer(pattern, text, re.M)}

assert not definitions((root / sources[0]).read_text())
current, previous = (root / sources[1]).read_text(), old_source(sources[1])
assert definitions(current) == definitions(previous)
declaration = 'theorem prepare_pending_complete\n'
assert previous.split(declaration, 1)[1].split(' :\n    ∃', 1)[0] == current.split(declaration, 1)[1].split(' :\n    ∃', 1)[0]
(evidence / 'proof-change.patch').write_bytes(subprocess.check_output(
    ['git', 'diff', base, 'HEAD', '--', 'lean/MicroCFTA'], cwd=root))
summary = dict(base=base, proof_head=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
               checks=5, strict_attempts=2, rejected_strict_attempts=0, final_strict_modules=2,
               public_declarations=6, audit_theorems=76716, public_lines=len(public.splitlines()),
               public_bytes=len(public_bytes), public_sha256=sha(public_bytes), unchanged_paths=unchanged,
               runtime_definitions_preserved=['SourcePruningEnumerationAction.prepare'],
               producer_admission_preserved=['SourcePruningEnumerationAction.prepare_pending_complete'],
               source_sha256={p: sha((root / p).read_bytes()) for p in snapshots})
(evidence / 'verification.json').write_text(json.dumps(summary, indent=2) + '\n')
manifest = {str(p.relative_to(evidence)): dict(bytes=p.stat().st_size, sha256=sha(p.read_bytes()))
            for p in sorted(evidence.rglob('*')) if p.is_file()}
(evidence / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps(dict(payloads=len(manifest), total_bytes=sum(v['bytes'] for v in manifest.values()),
                     manifest_sha256=sha((evidence / 'manifest.json').read_bytes()))))
