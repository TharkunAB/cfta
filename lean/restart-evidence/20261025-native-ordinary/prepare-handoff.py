import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-native-ordinary-20261025')
evidence = root / 'lean/restart-evidence/20261025-native-ordinary'
base = '1e426fb100a4b7b04b9d685d6be46920afefc4cc'
block = '''## Actual entry and native ordinary alternatives

Entry preservation: `4f85bd0adff78903bbe771f4816b2033d39b69ec`.
Ordinary composition: `ae1a6b4cb99e6532e53c3f5ebb68bdfb8a712a90`.
The goal stays ACTIVE.

Actual ready entry now composes with the native ordinary alternative scan.
It derives common sufficient bounds and retains the full raw entry receipt.
The source's nonterminal parent gate remains explicit. The edge callback
selects actual stored edges. Each alternative restores the entered enumeration
cache while retaining reached native caller and query effects. Supported
annotations complete the scan, including valid rejections. Entry also exports
RenderStable, which transports existing global reference facts through entry.

Both changed modules pass strict checking. Installed public readback and Audit
pass. The audit checks 76699 theorem dependencies. Haskell and H6 are unchanged.
H6 remains the strongest end-to-end result. Next: native reference provenance
and incoming avoidance through child writes, then global pending/fragment
history and successful receipt/whole-driver language semantics. Ready and
PendingReferences alone do not exclude other buckets from the pending target.
Terminal parents, parent normalization, narrowing/oracle preservation and
arbitrary Haskell demand remain open integration boundaries.
Details: `lean/notes-current-pruning-enumeration-native-ordinary.md`.

'''
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/COVERAGE.md', 'lean/API-COVERAGE.md',
             'lean/notes-current-system-claim.md', 'lean/notes-proof-status-20261017.md']
for relative in documents:
    path = root / relative
    text = path.read_text()
    marker = '## Ordered native alternatives with enumeration rollback'
    assert marker in text and block.splitlines()[0] not in text
    path.write_text(text.replace(marker, block + marker, 1))
findings = root / 'FINDINGS.md'
text = findings.read_text()
old = 'Details: lean/notes-current-pruning-enumeration-native-alternatives.md.\n'
new = '''The actual-entry composition also retains the source gate at line 783:
only ordinary parents without terminal suspended tries use this shallow scan.
It uses an explicit edge-selection callback corresponding to _edgesOf.
Terminal parents retain the existing enumerateNode fallback boundary. Native
children can still take their terminal dispatcher. No Haskell fix is needed.
Details: lean/notes-current-pruning-enumeration-native-ordinary.md.
'''
assert old in text
findings.write_text(text.replace(old, new, 1))
assert findings.read_text().index('## Haskell fix handoff') < findings.read_text().index(block.splitlines()[0])

runs = ['entry-stable-strict-1', 'installed-entry-stable', 'ordinary-strict-1',
        'ordinary-strict-2', 'aggregate-audit', 'public-final']
evidence.mkdir()
for name in runs:
    shutil.copytree(area / name, evidence / name)
for name in ['check.py', 'prepare-handoff.py', 'heavy-peaks']:
    shutil.copyfile(area / name, evidence / name)
sources = ['lean/MicroCFTA/' + name + '.lean' for name in [
    'SourcePruningEnumerationSelectedEntry', 'SourcePruningEnumerationNativeOrdinary',
    'Audit', 'SourceCurrentColdFiniteWarmCalls']]
for relative in sources + ['cfta/src/Data/CFTA/Enumeration.hs']:
    target = evidence / 'sources' / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(root / relative, target)
sha = lambda data: hashlib.sha256(data).hexdigest()
checks = {name: json.loads((evidence / name / 'report.json').read_text()) for name in runs}
assert {name for name, report in checks.items() if report['exit_code']} == {'ordinary-strict-1'}
for name, report in checks.items():
    raw = (evidence / name / 'raw.log').read_bytes()
    assert len(raw) == report['bytes'] and sha(raw) == report['sha256']
    if '-strict-' in name:
        source = next((evidence / name / 'MicroCFTA').glob('*.lean'))
        assert sha(source.read_bytes()) == report['source_sha256']
        if name != 'ordinary-strict-1':
            assert source.read_bytes() == (root / 'lean/MicroCFTA' / source.name).read_bytes()
            assert not raw
assert sha((evidence / 'public-final/public.lean').read_bytes()) == checks['public-final']['source_sha256']
public = (evidence / 'public-final/raw.log').read_text()
assert public.count('depends on axioms:') == 6 and '⋯' not in public and '...' not in public
for axioms in re.findall(r'depends on axioms:\s*\[([^]]*)\]', public):
    assert set(re.findall(r'[A-Za-z_.]+', axioms)) <= {'propext', 'Classical.choice', 'Quot.sound'}
assert 'Checked axiom dependencies of 76699 MicroCFTA theorems.' in (evidence / 'aggregate-audit/raw.log').read_text()
unchanged = ['lean/MicroCFTA/' + name + '.lean' for name in [
    'SourcePruningEnumerationCapturedEdge', 'SourcePruningEnumerationNativeGrowth',
    'SourcePruningEnumerationNativeBranches', 'SourcePruningEnumerationNativeBranchCompletion',
    'SourcePruningEnumerationChildDispatch', 'SourcePruningEnumerationChildTraversal',
    'SourcePruningEnumerationTraversalCompletion', 'SourceCurrentAllocatedPartialInvariant',
    'SourceCurrentColdFiniteWarmCalls']]
unchanged += ['cfta/src/Data/CFTA/' + name for name in [
    'Enumeration.hs', 'Interned/Type.hs', 'Interned/Cache.hs', 'Interned/Memo.hs', 'Interned/Operations.hs']]
for relative in unchanged:
    old = subprocess.check_output(['git', 'show', base + ':' + relative], cwd=root)
    assert old == (root / relative).read_bytes(), relative
subprocess.run(['git', 'diff', '--quiet', base, '--', '*.hs', '*.cabal'], cwd=root, check=True)
for relative in sources[:2]:
    assert not re.search(r'\b(sorry|admit|axiom)\b', (root / relative).read_text())
patch = subprocess.check_output(['git', 'diff', base, 'HEAD', '--', 'lean/MicroCFTA'], cwd=root)
(evidence / 'proof-change.patch').write_bytes(patch)
summary = dict(base=base, proof_head=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
               checks=6, strict_attempts=3, rejected_strict_attempts=1, public_declarations=6,
               audit_theorems=76699, public_lines=len(public.splitlines()),
               unchanged_paths=unchanged, source_sha256={p: sha((root / p).read_bytes()) for p in sources})
(evidence / 'verification.json').write_text(json.dumps(summary, indent=2) + '\n')
manifest = {str(p.relative_to(evidence)): dict(bytes=p.stat().st_size, sha256=sha(p.read_bytes()))
            for p in sorted(evidence.rglob('*')) if p.is_file()}
(evidence / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps(dict(payloads=len(manifest), total_bytes=sum(v['bytes'] for v in manifest.values()),
                     manifest_sha256=sha((evidence / 'manifest.json').read_bytes()))))
