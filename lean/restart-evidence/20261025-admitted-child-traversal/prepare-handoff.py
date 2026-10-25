import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-child-completion-20261025')
evidence = root / 'lean/restart-evidence/20261025-admitted-child-traversal'
base = '3efeccad4c210af6a93a12fdad9262578b25f993'
block = '''## Admitted ordered native child traversal

Child completion: `a8593e70a465299b3f1d2f6bda1320b9b07005f9`.
Traversal completion: `06fc7521a9d83a0d7a053c5f6496f02fc1e8d510`.
The goal stays ACTIVE.

Genuine caller/cache invariants and conditional numeric ranges now derive
common sufficient bounds for all executed children. The worker completes
or stops at its first valid raw-empty rejection with the actual cache.
No future-success premise is used. Both outcomes retain indexes, caller
effects, enumerated-value origin and old enumerated-root protection.
Complete output retains Safe. Rejection has no unconditional Safe claim.
Any old allocated root avoided by all child buckets is also protected.
Parent InputsPending transports, including on rejection. The captured-slot
root and avoidance obligations remain explicit.

All three strict proof modules, installed readback and Audit pass.
The audit checks 76623 theorem dependencies. Haskell runtime is unchanged.
H6 remains the strongest end-to-end result. Next: actual selected-edge
input admission, then the residual and original captured-slot final write.
Details: `lean/notes-current-pruning-enumeration-admitted-traversal.md`.

'''
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/COVERAGE.md', 'lean/API-COVERAGE.md',
             'lean/notes-current-system-claim.md', 'lean/notes-proof-status-20261017.md']
for relative in documents:
    path = root / relative
    content = path.read_text()
    assert '## Admitted ordered native child traversal' not in content
    marker = '## Deterministic Sized gate from main'
    assert marker in content
    path.write_text(content.replace(marker, block + marker, 1))

runs = ['terminal-ranges-strict-1', 'installed-terminal-ranges',
        'child-completion-strict-1', 'child-completion-strict-2', 'child-completion-strict-3',
        'installed-child-completion', 'traversal-completion-strict-1',
        'traversal-completion-strict-2', 'traversal-completion-strict-3',
        'aggregate-audit', 'installed-public']
evidence.mkdir()
for name in runs:
    shutil.copytree(area / name, evidence / name)
for name in ['check.py', 'prepare-handoff.py', 'heavy-peaks']:
    shutil.copyfile(area / name, evidence / name)
sources = ['lean/MicroCFTA/' + module + '.lean' for module in [
    'SourcePruningEnumerationCachedTerminalAdapter', 'SourcePruningEnumerationChildCompletion',
    'SourcePruningEnumerationTraversalCompletion', 'Audit', 'SourceCurrentColdFiniteWarmCalls']]
for relative in sources:
    destination = evidence / 'sources' / relative
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(root / relative, destination)

sha = lambda data: hashlib.sha256(data).hexdigest()
checks = {name: json.loads((evidence / name / 'report.json').read_text()) for name in runs}
expected_failures = {'child-completion-strict-1', 'child-completion-strict-2', 'traversal-completion-strict-1'}
assert {name for name, check in checks.items() if check['exit_code']} == expected_failures
final_strict = {'terminal-ranges-strict-1', 'child-completion-strict-3', 'traversal-completion-strict-3'}
for name, check in checks.items():
    raw = (evidence / name / 'raw.log').read_bytes()
    assert len(raw) == check['bytes'] and sha(raw) == check['sha256']
    if 'strict-' in name:
        source = next((evidence / name / 'MicroCFTA').glob('*.lean'))
        assert sha(source.read_bytes()) == check['source_sha256']
        if name in final_strict:
            assert source.read_bytes() == (root / 'lean/MicroCFTA' / source.name).read_bytes()
            assert not raw
audit = (evidence / 'aggregate-audit/raw.log').read_text()
assert 'Checked axiom dependencies of 76623 MicroCFTA theorems.' in audit
public = (evidence / 'installed-public/raw.log').read_text()
assert public.count("depends on axioms:") == 7
assert '⋯' not in public and '...' not in public
unchanged_paths = ['lean/MicroCFTA/' + module + '.lean' for module in [
    'SourcePruningEnumerationChildDispatch', 'SourcePruningEnumerationChildTraversal',
    'SourcePruningEnumerationChildEffects', 'SourceCurrentColdFiniteWarmCalls']]
for relative in unchanged_paths:
    old = subprocess.check_output(['git', 'show', base + ':' + relative], cwd=root)
    assert old == (root / relative).read_bytes(), relative
subprocess.run(['git', 'diff', '--quiet', base, 'HEAD', '--', '*.hs', '*.cabal'], cwd=root, check=True)
terminal = 'lean/MicroCFTA/SourcePruningEnumerationCachedTerminalAdapter.lean'
old = subprocess.check_output(['git', 'show', base + ':' + terminal], cwd=root).decode()
current = (root / terminal).read_text()
old_marker = '/-- Genuine admitted inputs produce the exact terminal observation and cache. -/'
new_marker = '/-- Each reached terminal request fits the fixed mathematical machine width. -/'
assert old.split(old_marker)[0] == current.split(new_marker)[0]
body_marker = '  obtain ⟨r, n, p, h, recorded, winner, joined, foldRows, foldCaller, foldQueries,\n'
assert old.split(body_marker)[1] == current.split(body_marker)[1]
diff = subprocess.check_output(['git', 'diff', base, 'HEAD', '--', 'lean/MicroCFTA'], cwd=root)
(evidence / 'proof-change.patch').write_bytes(diff)
summary = dict(checks=len(runs), strict_attempts=7, rejected_strict_attempts=3,
               final_strict_passes=3, audit_dependencies=76623, public_declarations=7,
               public_bytes=len(public.encode()), public_lines=len(public.splitlines()),
               public_sha256=sha(public.encode()), haskell_unchanged=True,
               terminal_runtime_and_proof_body_unchanged=True,
               unchanged_sources={relative: sha((root / relative).read_bytes()) for relative in unchanged_paths},
               source_sha256={relative: sha((root / relative).read_bytes()) for relative in sources})
(evidence / 'verification.json').write_text(json.dumps(summary, indent=2) + '\n')
manifest = {str(path.relative_to(evidence)): dict(bytes=path.stat().st_size, sha256=sha(path.read_bytes()))
            for path in sorted(evidence.rglob('*')) if path.is_file()}
(evidence / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps(dict(payloads=len(manifest), bytes=sum(item['bytes'] for item in manifest.values()),
                      manifest_sha256=sha((evidence / 'manifest.json').read_bytes()), verification=summary), indent=2))
