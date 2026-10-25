import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-edge-inputs-20261025')
evidence = root / 'lean/restart-evidence/20261025-native-selected-edge'
base = '932b6c6c12062a7fc92a8822ec36df491b2f2f3c'
block = '''## Native selected-edge admission and completion

Input admission: `80a2935ca94caf8a99beacc39a3a43be528c2a10`.
Selected-edge completion: `9c2dae8934c63a26b466d6acb62ebb130cc73425`.
The goal stays ACTIVE.

Actual own-class preparation now derives admission for the ordered native
children of a supported selected edge. Conditional numeric ranges derive
sufficient common bounds. Complete traversal constructs the parent fragment
and records its residual at the actual result cache. The other admitted
outcome is the first valid raw-empty child rejection with its exact cache.
Both outcomes retain caller and index invariants and inherited pending inputs.
Only complete output retains unconditional Safe. Separate fixed-bound laws
retain arity rejection, unsupported preparation and every stopped receipt.
Protection of a separate old root keeps allocation, rootness and inherited
avoidance premises explicit. No future successful trace is assumed.

Both strict modules, installed readback and Audit pass. The audit checks
76650 theorem dependencies. Haskell runtime and H6 are unchanged.
H6 remains the strongest end-to-end result. Next: original captured-slot
finalization, then ordered alternatives and whole-driver semantics.
Details: `lean/notes-current-pruning-enumeration-selected-edge.md`.

'''
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/COVERAGE.md', 'lean/API-COVERAGE.md',
             'lean/notes-current-system-claim.md', 'lean/notes-proof-status-20261017.md']
for relative in documents:
    path = root / relative
    content = path.read_text()
    assert '## Native selected-edge admission and completion' not in content
    marker = '## Admitted ordered native child traversal'
    assert marker in content
    path.write_text(content.replace(marker, block + marker, 1))
assert (root / 'FINDINGS.md').read_text().index('## Haskell fix handoff') < (root / 'FINDINGS.md').read_text().index('## Native selected-edge admission')

runs = ['edge-inputs-strict-1', 'edge-inputs-strict-2', 'installed-edge-inputs',
        'selected-edge-strict-1', 'selected-edge-strict-2', 'selected-edge-strict-3',
        'selected-edge-strict-4', 'installed-selected-edge', 'public', 'public-final', 'aggregate-audit']
evidence.mkdir()
for name in runs:
    shutil.copytree(area / name, evidence / name)
for name in ['check.py', 'prepare-handoff.py', 'heavy-peaks']:
    shutil.copyfile(area / name, evidence / name)
sources = ['lean/MicroCFTA/' + module + '.lean' for module in [
    'SourcePruningEnumerationEdgeInputs', 'SourcePruningEnumerationSelectedEdge',
    'Audit', 'SourceCurrentColdFiniteWarmCalls']]
for relative in sources:
    destination = evidence / 'sources' / relative
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(root / relative, destination)

sha = lambda data: hashlib.sha256(data).hexdigest()
checks = {name: json.loads((evidence / name / 'report.json').read_text()) for name in runs}
expected_failures = {'edge-inputs-strict-1', 'selected-edge-strict-1', 'selected-edge-strict-2', 'public'}
assert {name for name, check in checks.items() if check['exit_code']} == expected_failures
final_strict = {'edge-inputs-strict-2', 'selected-edge-strict-4'}
for name, check in checks.items():
    raw = (evidence / name / 'raw.log').read_bytes()
    assert len(raw) == check['bytes'] and sha(raw) == check['sha256']
    if 'strict-' in name:
        source = next((evidence / name / 'MicroCFTA').glob('*.lean'))
        assert sha(source.read_bytes()) == check['source_sha256']
        if name in final_strict:
            assert source.read_bytes() == (root / 'lean/MicroCFTA' / source.name).read_bytes()
            assert not raw
    if name in {'public', 'public-final'}:
        assert sha((evidence / name / 'public.lean').read_bytes()) == check['source_sha256']
audit = (evidence / 'aggregate-audit/raw.log').read_text()
assert 'Checked axiom dependencies of 76650 MicroCFTA theorems.' in audit
public = (evidence / 'public-final/raw.log').read_text()
assert public.count('depends on axioms:') == 10
assert public.count('does not depend on any axioms') == 2
assert '⋯' not in public and '...' not in public
for raw_axioms in re.findall(r'depends on axioms:\s*\[([^]]*)\]', public):
    assert set(re.findall(r'[A-Za-z_.]+', raw_axioms)) <= {'propext', 'Classical.choice', 'Quot.sound'}
unchanged_paths = ['lean/MicroCFTA/' + module + '.lean' for module in [
    'SourcePruningEnumerationCachedOwn', 'SourcePruningEnumerationChildDispatch',
    'SourcePruningEnumerationChildTraversal', 'SourcePruningEnumerationChildEffects',
    'SourcePruningEnumerationTraversalCompletion', 'SourcePruningEnumerationCachedTerminalAdapter',
    'SourcePruningEnumerationFinalize', 'EnumerationConstruction', 'SourceCurrentColdFiniteWarmCalls']]
for relative in unchanged_paths:
    old = subprocess.check_output(['git', 'show', base + ':' + relative], cwd=root)
    assert old == (root / relative).read_bytes(), relative
subprocess.run(['git', 'diff', '--quiet', base, '--', '*.hs', '*.cabal'], cwd=root, check=True)
for relative in sources[:2]:
    assert not re.search(r'\b(sorry|admit|axiom)\b', (root / relative).read_text())
diff = subprocess.check_output(['git', 'diff', base, 'HEAD', '--', 'lean/MicroCFTA'], cwd=root)
(evidence / 'proof-change.patch').write_bytes(diff)
summary = dict(base=base, checks=len(runs), strict_attempts=6, rejected_strict_attempts=3,
               final_strict_passes=2, rejected_public_attempts=1, audit_dependencies=76650,
               public_declarations=12, public_bytes=len(public.encode()), public_lines=len(public.splitlines()),
               public_sha256=sha(public.encode()), haskell_unchanged=True,
               unchanged_sources={relative: sha((root / relative).read_bytes()) for relative in unchanged_paths},
               source_sha256={relative: sha((root / relative).read_bytes()) for relative in sources})
(evidence / 'verification.json').write_text(json.dumps(summary, indent=2) + '\n')
manifest = {str(path.relative_to(evidence)): dict(bytes=path.stat().st_size, sha256=sha(path.read_bytes()))
            for path in sorted(evidence.rglob('*')) if path.is_file()}
(evidence / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps(dict(payloads=len(manifest), bytes=sum(item['bytes'] for item in manifest.values()),
                      manifest_sha256=sha((evidence / 'manifest.json').read_bytes()), verification=summary), indent=2))
