import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-native-alternatives-20261025')
evidence = root / 'lean/restart-evidence/20261025-native-alternatives'
base = '3d3bfc002e5ceaa6ff6ace26b58d541fffa0072a'
block = '''## Ordered native alternatives with enumeration rollback

Worker and transport: `a3b400c4f2cc2146368d37e5f80ec4d2152c7637`.
Admitted completion: `e8bcb10c65090595572c6edc930ad52a20f624a6`.
The goal stays ACTIVE.

The new serial worker restores the identical enumeration cache for each
alternative and threads the reached native caller and queries. Each receipt
keeps its own branch cache. Valid child rejection continues from the original
safe cache while retaining its native effects. Conditional numeric ranges
now derive common sufficient finite bounds. Unsupported preparation stops
explicitly. Supported annotations derive completion of the whole ordered list,
including valid rejection receipts. There is no merged enumeration cache.
Every processed receipt retains its own reached-heap cache certificate.

All three strict modules, installed readback and Audit pass. The audit checks
76695 theorem dependencies. Haskell runtime and H6 are unchanged.
H6 remains the strongest end-to-end result. Next: actual entry composition,
global pending-reference and fragment-dependency history, then successful
receipt extraction and whole-driver language semantics. This worker chooses
serial forcing; arbitrary Haskell demand and full raw-stream erasure stay open.
Details: `lean/notes-current-pruning-enumeration-native-alternatives.md`.

'''
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/COVERAGE.md', 'lean/API-COVERAGE.md',
             'lean/notes-current-system-claim.md', 'lean/notes-proof-status-20261017.md']
for relative in documents:
    path = root / relative
    content = path.read_text()
    assert '## Ordered native alternatives with enumeration rollback' not in content
    marker = '## Native captured-slot edge finalization'
    assert marker in content
    path.write_text(content.replace(marker, block + marker, 1))
findings = root / 'FINDINGS.md'
content = findings.read_text()
old = '''The next native formal wrapper must restore the branch-local enumeration
cache while accounting for shared native growth and memo effects. The lazy
result list and cached result thunks leave forcing order explicit. Independent
runs from one complete caller/query state do not reproduce that global history.
This is a correspondence boundary. No Haskell runtime defect or repair is
identified. External action: no patch is proposed for this source observation.
Details: lean/notes-current-pruning-enumeration-captured-edge.md.
'''
new = '''The native formal alternative worker now restores the branch-local enumeration
cache and threads the reached caller and queries through evaluated alternatives.
Its admitted theorem derives common finite bounds and keeps a cache certificate
for each receipt at its own reached heap. Supported annotations complete the
ordered scan, including valid rejection receipts.

The worker chooses serial forcing. The lazy result list and cached result thunks
leave exact agreement with arbitrary Haskell demand open. Independent runs from
one complete caller/query state do not reproduce that shared global history.
No Haskell runtime defect or repair is identified. External action: no patch is
proposed for this source observation.
Details: lean/notes-current-pruning-enumeration-native-alternatives.md.
'''
assert old in content
findings.write_text(content.replace(old, new, 1))
assert findings.read_text().index('## Haskell fix handoff') < findings.read_text().index('## Ordered native alternatives')

runs = ['native-growth-strict-1', 'native-branches-strict-1', 'native-branches-strict-2',
        'installed-growth-branches', 'native-branch-completion-strict-1',
        'native-branch-completion-strict-2', 'native-branch-completion-strict-3',
        'native-branches-strict-3', 'installed-branches-final', 'native-branch-completion-strict-4',
        'aggregate-audit', 'public-final']
evidence.mkdir()
for name in runs:
    shutil.copytree(area / name, evidence / name)
for name in ['check.py', 'prepare-handoff.py', 'heavy-peaks']:
    shutil.copyfile(area / name, evidence / name)
sources = ['lean/MicroCFTA/' + module + '.lean' for module in [
    'SourcePruningEnumerationNativeGrowth', 'SourcePruningEnumerationNativeBranches',
    'SourcePruningEnumerationNativeBranchCompletion', 'Audit', 'SourceCurrentColdFiniteWarmCalls']]
for relative in sources + ['cfta/src/Data/CFTA/Enumeration.hs']:
    destination = evidence / 'sources' / relative
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(root / relative, destination)

sha = lambda data: hashlib.sha256(data).hexdigest()
checks = {name: json.loads((evidence / name / 'report.json').read_text()) for name in runs}
expected_failures = {'native-branches-strict-1', 'native-branch-completion-strict-1',
                     'native-branch-completion-strict-2', 'native-branch-completion-strict-3'}
assert {name for name, check in checks.items() if check['exit_code']} == expected_failures
final_strict = {'native-growth-strict-1', 'native-branches-strict-3', 'native-branch-completion-strict-4'}
for name, check in checks.items():
    raw = (evidence / name / 'raw.log').read_bytes()
    assert len(raw) == check['bytes'] and sha(raw) == check['sha256']
    if 'strict-' in name:
        source = next((evidence / name / 'MicroCFTA').glob('*.lean'))
        assert sha(source.read_bytes()) == check['source_sha256']
        if name in final_strict:
            assert source.read_bytes() == (root / 'lean/MicroCFTA' / source.name).read_bytes()
            assert not raw
assert sha((evidence / 'public-final/public.lean').read_bytes()) == checks['public-final']['source_sha256']
audit = (evidence / 'aggregate-audit/raw.log').read_text()
assert 'Checked axiom dependencies of 76695 MicroCFTA theorems.' in audit
public = (evidence / 'public-final/raw.log').read_text()
assert public.count('depends on axioms:') == 11
assert '⋯' not in public and '...' not in public
for raw_axioms in re.findall(r'depends on axioms:\s*\[([^]]*)\]', public):
    assert set(re.findall(r'[A-Za-z_.]+', raw_axioms)) <= {'propext', 'Classical.choice', 'Quot.sound'}
unchanged_paths = ['lean/MicroCFTA/' + module + '.lean' for module in [
    'SourcePruningEnumerationCapturedEdge', 'SourcePruningEnumerationSelectedEntry',
    'SourcePruningEnumerationSelectedEdge', 'SourcePruningEnumerationNativeIndex',
    'SourcePruningEnumerationChildDispatch', 'SourcePruningEnumerationChildTraversal',
    'SourcePruningEnumerationTraversalCompletion', 'SourceCurrentAllocatedPartialInvariant',
    'SourceCurrentColdFiniteWarmCalls']]
unchanged_paths += ['cfta/src/Data/CFTA/' + name for name in [
    'Enumeration.hs', 'Interned/Type.hs', 'Interned/Cache.hs', 'Interned/Memo.hs', 'Interned/Operations.hs']]
for relative in unchanged_paths:
    old = subprocess.check_output(['git', 'show', base + ':' + relative], cwd=root)
    assert old == (root / relative).read_bytes(), relative
subprocess.run(['git', 'diff', '--quiet', base, '--', '*.hs', '*.cabal'], cwd=root, check=True)
for relative in sources[:3]:
    assert not re.search(r'\b(sorry|admit|axiom)\b', (root / relative).read_text())
diff = subprocess.check_output(['git', 'diff', base, 'HEAD', '--', 'lean/MicroCFTA'], cwd=root)
(evidence / 'proof-change.patch').write_bytes(diff)
summary = dict(base=base, checks=len(runs), strict_attempts=8, rejected_strict_attempts=4,
               final_strict_passes=3, audit_dependencies=76695, public_declarations=11,
               public_bytes=len(public.encode()), public_lines=len(public.splitlines()),
               public_sha256=sha(public.encode()), haskell_unchanged=True,
               unchanged_sources={relative: sha((root / relative).read_bytes()) for relative in unchanged_paths},
               source_sha256={relative: sha((root / relative).read_bytes()) for relative in sources})
(evidence / 'verification.json').write_text(json.dumps(summary, indent=2) + '\n')
manifest = {str(path.relative_to(evidence)): dict(bytes=path.stat().st_size, sha256=sha(path.read_bytes()))
            for path in sorted(evidence.rglob('*')) if path.is_file()}
(evidence / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps(dict(payloads=len(manifest), bytes=sum(item['bytes'] for item in manifest.values()),
                      manifest_sha256=sha((evidence / 'manifest.json').read_bytes()),
                      checks=len(runs), audit_dependencies=76695), indent=2))
