import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-captured-finalization-20261025')
evidence = root / 'lean/restart-evidence/20261025-native-captured-edge'
base = '7d9ef8e4087fce5349d00c0a090437a41135d54f'
block = '''## Native captured-slot edge finalization

Finalization safety: `3197aaaa47cf0080e9097da1191f36947bb2fd5b`.
Selected entry: `2bfd43cfe3e7001dbdec7adbae2c98b98a7d1ca7`.
Captured edge: `736d95555def03b909a25d5b1a756270f95055dd`.
The goal stays ACTIVE.

Actual entry retains readiness and proves captured target identity.
The separately composed captured-edge worker derives sufficient bounds
for a supported edge and its original raw-slot write, or exact child rejection.
Successful output resets expansion ancestry and retains Safe and all indexes.
Rejection does not finalize or claim unconditional Safe. Enumerated origin
and unchanged-value protection are restricted away from the new target.
Inherited InputsPending is retained. Its original premise and conditional
numeric admission remain. Readiness is required at the actual entry state.
Oracle preservation, global PendingReferences and fragment acyclicity stay open.

All three strict modules, installed readback and Audit pass. The audit checks
76656 theorem dependencies. Haskell runtime and H6 are unchanged.
H6 remains the strongest end-to-end result. Next: combine the entry and
captured-edge steps into ordered alternatives. Restore enumeration input
per branch, but account for shared native growth and query memo effects.
The Haskell result list is lazy; exact forcing correspondence remains open.
Details: `lean/notes-current-pruning-enumeration-captured-edge.md`.

'''
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/COVERAGE.md', 'lean/API-COVERAGE.md',
             'lean/notes-current-system-claim.md', 'lean/notes-proof-status-20261017.md']
for relative in documents:
    path = root / relative
    content = path.read_text()
    assert '## Native captured-slot edge finalization' not in content
    marker = '## Native selected-edge admission and completion'
    assert marker in content
    path.write_text(content.replace(marker, block + marker, 1))
findings = root / 'FINDINGS.md'
content = findings.read_text()
marker = '### Specftacular parallel completion follow-ups'
native_boundary = '''### Native alternative state boundary

Source inspection for the captured-slot proof confirms that each alternative
restores its input EnumerationState. It does not restore native interners or
memo tables. Enumeration.hs:328 defines pure CPS branching. Interned/Type.hs:453
and line 510 define process-global interning caches and identity supplies.
Interned/Cache.hs:169 and Interned/Memo.hs:91 use shared mutable tables.
Rejected branches retain evaluated native effects too.

The next native formal wrapper must restore the branch-local enumeration
cache while accounting for shared native growth and memo effects. The lazy
result list and cached result thunks leave forcing order explicit. Independent
runs from one complete caller/query state do not reproduce that global history.
This is a correspondence boundary. No Haskell runtime defect or repair is
identified. External action: no patch is proposed for this source observation.
Details: lean/notes-current-pruning-enumeration-captured-edge.md.

'''
assert '### Native alternative state boundary' not in content
assert marker in content
findings.write_text(content.replace(marker, native_boundary + marker, 1))
assert findings.read_text().index('## Haskell fix handoff') < findings.read_text().index('## Native captured-slot edge')

runs = ['finalize-strict-1', 'finalize-strict-2', 'selected-entry-strict-1', 'selected-entry-strict-2',
        'installed-entry-finalize', 'captured-edge-strict-1', 'captured-edge-strict-2',
        'installed-captured-edge', 'public-final', 'aggregate-audit']
evidence.mkdir()
for name in runs:
    shutil.copytree(area / name, evidence / name)
for name in ['check.py', 'prepare-handoff.py', 'heavy-peaks']:
    shutil.copyfile(area / name, evidence / name)
sources = ['lean/MicroCFTA/' + module + '.lean' for module in [
    'SourcePruningEnumerationFinalize', 'SourcePruningEnumerationSelectedEntry',
    'SourcePruningEnumerationCapturedEdge', 'Audit', 'SourceCurrentColdFiniteWarmCalls']]
native_sources = ['cfta/src/Data/CFTA/' + name for name in [
    'Enumeration.hs', 'Interned/Type.hs', 'Interned/Cache.hs', 'Interned/Memo.hs', 'Interned/Operations.hs']]
for relative in sources + native_sources:
    destination = evidence / 'sources' / relative
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(root / relative, destination)

sha = lambda data: hashlib.sha256(data).hexdigest()
checks = {name: json.loads((evidence / name / 'report.json').read_text()) for name in runs}
expected_failures = {'finalize-strict-1', 'selected-entry-strict-1', 'captured-edge-strict-1'}
assert {name for name, check in checks.items() if check['exit_code']} == expected_failures
final_strict = {'finalize-strict-2', 'selected-entry-strict-2', 'captured-edge-strict-2'}
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
assert 'Checked axiom dependencies of 76656 MicroCFTA theorems.' in audit
public = (evidence / 'public-final/raw.log').read_text()
assert public.count('depends on axioms:') == 6
assert '⋯' not in public and '...' not in public
for raw_axioms in re.findall(r'depends on axioms:\s*\[([^]]*)\]', public):
    assert set(re.findall(r'[A-Za-z_.]+', raw_axioms)) <= {'propext', 'Classical.choice', 'Quot.sound'}
unchanged_paths = ['lean/MicroCFTA/' + module + '.lean' for module in [
    'SourcePruningEnumerationEntry', 'SourcePruningEnumerationSelection',
    'SourcePruningEnumerationSelectedEdge', 'SourcePruningEnumerationChildDispatch',
    'SourcePruningEnumerationChildTraversal', 'SourcePruningEnumerationChildEffects',
    'SourcePruningEnumerationTraversalCompletion', 'SourceCurrentColdFiniteWarmCalls']]
for relative in unchanged_paths + native_sources:
    old = subprocess.check_output(['git', 'show', base + ':' + relative], cwd=root)
    assert old == (root / relative).read_bytes(), relative
subprocess.run(['git', 'diff', '--quiet', base, '--', '*.hs', '*.cabal'], cwd=root, check=True)
finalize = 'lean/MicroCFTA/SourcePruningEnumerationFinalize.lean'
old = subprocess.check_output(['git', 'show', base + ':' + finalize], cwd=root).decode()
current = (root / finalize).read_text()
old_marker = '/-- Derive finite finalization and the retained storage and index invariants. -/'
new_marker = '/-- Resetting ancestry and replacing a root by a bounded fragment retains safety. -/'
assert old.split(old_marker)[0] == current.split(new_marker)[0]
for relative in sources[:3]:
    assert not re.search(r'\b(sorry|admit|axiom)\b', (root / relative).read_text())
diff = subprocess.check_output(['git', 'diff', base, 'HEAD', '--', 'lean/MicroCFTA'], cwd=root)
(evidence / 'proof-change.patch').write_bytes(diff)
summary = dict(base=base, checks=len(runs), strict_attempts=6, rejected_strict_attempts=3,
               final_strict_passes=3, audit_dependencies=76656, public_declarations=6,
               public_bytes=len(public.encode()), public_lines=len(public.splitlines()),
               public_sha256=sha(public.encode()), haskell_unchanged=True, finalize_runtime_unchanged=True,
               unchanged_sources={relative: sha((root / relative).read_bytes()) for relative in unchanged_paths + native_sources},
               source_sha256={relative: sha((root / relative).read_bytes()) for relative in sources})
(evidence / 'verification.json').write_text(json.dumps(summary, indent=2) + '\n')
manifest = {str(path.relative_to(evidence)): dict(bytes=path.stat().st_size, sha256=sha(path.read_bytes()))
            for path in sorted(evidence.rglob('*')) if path.is_file()}
(evidence / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps(dict(payloads=len(manifest), bytes=sum(item['bytes'] for item in manifest.values()),
                      manifest_sha256=sha((evidence / 'manifest.json').read_bytes()), verification=summary), indent=2))
