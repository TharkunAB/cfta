import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-selected-reference-receipts-20261025')
evidence = root / 'lean/restart-evidence/20261025-selected-reference-receipts'
base = '4b84478664788bfc7e12e258772f72528a466032'
block = '''## Selected ordinary alternatives retain pending references

Selection: `9f3674ba1`. Ordinary history: `519d62a80`.
The goal stays ACTIVE.

Actual pure selection now derives no incoming reference to its target at
the same input cache. Actual ordinary entry transports initial global pending
history and incoming avoidance. Every processed alternative retains pending
history at its own returned cache and native heap. The selected completion
theorem derives Ready and local pending inputs too. Existing producer inputs,
numeric Ranges conditions and runtime worker bodies stay unchanged.

All three strict modules, installed readback and Audit pass. The audit checks
76712 theorem dependencies. H6 remains the strongest end-to-end language
theorem. Haskell is unchanged. Next: carry these facts through actual reads,
native narrowing and accepted callbacks before driver entry. The new selected
theorem covers selection and entry at the same cache, without those operations
between them. Fragment-hole history, extraction, terminal parents, parent
normalization and whole-driver language semantics remain open.
Details: `lean/notes-current-pruning-enumeration-selected-references.md`.

'''
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/COVERAGE.md', 'lean/API-COVERAGE.md',
             'lean/notes-current-system-claim.md', 'lean/notes-proof-status-20261017.md']
for relative in documents:
    path = root / relative
    text = path.read_text()
    marker = '## Native suspended-reference history through captured finalization'
    assert marker in text
    if block.splitlines()[0] not in text:
        path.write_text(text.replace(marker, block + marker, 1))
path = root / 'FINDINGS.md'
text = path.read_text()
marker = '### Native reference mutation order'
addition = '''### Selected references and the actual callback boundary

The formal same-cache selection theorem now derives incoming avoidance and
per-receipt pending-reference history through ordinary expansion.
Enumeration.hs:968 to 1004 also reads the selected value, runs native narrow,
may replace its node, and accepts the Right oracle before entry at line 976.
The ordered driver also has an activation refresh after callback acceptance.
Those actual intermediate operations still need preservation proofs.
The existing native action theorem exposes the changed-handle write with the
same suspended bucket. An exact-state ReadOnlyOracle assumption is stronger
than a callback that permits representative compression. Arbitrary callbacks
do not automatically preserve the reference conditions.
This is a formal correspondence gap. No new runtime defect or repair is found.
External action: no patch is proposed for this source observation.
Details: lean/notes-current-pruning-enumeration-selected-references.md.

'''
if addition.splitlines()[0] not in text:
    path.write_text(text.replace(marker, addition + marker, 1))
assert path.read_text().index('## Haskell fix handoff') < path.read_text().index(block.splitlines()[0])

checks = {p.parent.name: json.loads(p.read_text()) for p in sorted(area.glob('*/report.json'))}
assert len(checks) == 6 and all(report['exit_code'] == 0 for report in checks.values())
strict = {name for name in checks if '-strict-' in name}
assert len(strict) == 3
evidence.mkdir(exist_ok=True)
for name in checks:
    shutil.copytree(area / name, evidence / name, dirs_exist_ok=True)
for name in ['check.py', 'prepare-handoff.py', 'heavy-peaks', 'preparation-events.txt']:
    shutil.copyfile(area / name, evidence / name)
sha = lambda data: hashlib.sha256(data).hexdigest()
for name, report in checks.items():
    raw = (evidence / name / 'raw.log').read_bytes()
    assert len(raw) == report['bytes'] and sha(raw) == report['sha256']
    if name in strict:
        source = next((evidence / name / 'MicroCFTA').glob('*.lean'))
        assert sha(source.read_bytes()) == report['source_sha256']
        assert source.read_bytes() == (root / 'lean/MicroCFTA' / source.name).read_bytes()
        assert not raw
public_bytes = (evidence / 'public-final/raw.log').read_bytes()
public = public_bytes.decode()
assert public.count('depends on axioms:') == 9 and '⋯' not in public and '...' not in public
assert sha((evidence / 'public-final/public.lean').read_bytes()) == checks['public-final']['source_sha256']
for axioms in re.findall(r'depends on axioms:\s*\[([^]]*)\]', public):
    assert set(re.findall(r'[A-Za-z_.]+', axioms)) <= {'propext', 'Classical.choice', 'Quot.sound'}
assert 'Checked axiom dependencies of 76712 MicroCFTA theorems.' in (evidence / 'aggregate-audit/raw.log').read_text()

modules = ['SourcePruningEnumerationSelection', 'SourcePruningEnumerationNativeBranchCompletion',
           'SourcePruningEnumerationNativeOrdinary']
sources = ['lean/MicroCFTA/' + name + '.lean' for name in modules]
snapshots = sources + ['lean/MicroCFTA/Audit.lean', 'lean/MicroCFTA/SourceCurrentColdFiniteWarmCalls.lean',
                       'cfta/src/Data/CFTA/Enumeration.hs']
for relative in snapshots:
    target = evidence / 'sources' / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(root / relative, target)
    if relative in sources:
        assert not re.search(r'\b(sorry|admit|axiom)\b', (root / relative).read_text())
old_source = lambda relative: subprocess.check_output(['git', 'show', base + ':' + relative], cwd=root).decode()
unchanged = ['lean/MicroCFTA/' + name + '.lean' for name in [
    'SourcePruningEnumerationSelectedEntry', 'SourcePruningEnumerationFinalize',
    'SourcePruningEnumerationCapturedEdge', 'SourcePruningEnumerationSelectedEdge',
    'SourcePruningEnumerationNativeReferences', 'SourcePruningEnumerationChildCompletion',
    'SourcePruningEnumerationTraversalCompletion', 'SourcePruningEnumerationCachedTerminalAdapter',
    'SourcePruningEnumerationNativeBranches', 'SourcePruningEnumerationNativeIndex',
    'SourceCurrentColdFiniteWarmCalls', 'Audit']]
unchanged += ['cfta/src/Data/CFTA/' + name for name in [
    'Enumeration.hs', 'Interned/Type.hs', 'Interned/Cache.hs', 'Interned/Memo.hs', 'Interned/Operations.hs']]
for relative in unchanged:
    assert old_source(relative) == (root / relative).read_text(), relative
subprocess.run(['git', 'diff', '--quiet', base, '--', '*.hs', '*.cabal'], cwd=root, check=True)

def definitions(text):
    pattern = r'^(?:noncomputable )?def (\w+)[\s\S]*?(?=^/--|^private theorem |^theorem |^variable |^end |\Z)'
    return {match.group(1): match.group(0) for match in re.finditer(pattern, text, re.M)}

runtime_preserved = []
admission_preserved = []
for name in modules:
    relative = 'lean/MicroCFTA/' + name + '.lean'
    current, previous = (root / relative).read_text(), old_source(relative)
    old_defs, new_defs = definitions(previous), definitions(current)
    if name.endswith('NativeBranchCompletion'):
        assert set(new_defs) - set(old_defs) == {'Pending'}
        new_defs.pop('Pending')
    assert old_defs == new_defs, name
    runtime_preserved.append(name)
    if name.endswith('Selection'):
        for declaration in ['offered', 'unblocked_avoids', 'ready', 'realized']:
            old_contract = previous.split('theorem ' + declaration + '\n', 1)[1].split(':= by', 1)[0]
            new_contract = current.split('theorem ' + declaration + '\n', 1)[1].split(':= by', 1)[0]
            assert old_contract == new_contract, declaration
    else:
        old_head = previous.split('theorem complete\n', 1)[1].split(' :\n    ∃', 1)[0]
        new_head = current.split('theorem complete\n', 1)[1].split(' :\n    ∃', 1)[0]
        assert old_head == new_head, name
        admission_preserved.append(name)
patch = subprocess.check_output(['git', 'diff', base, 'HEAD', '--', 'lean/MicroCFTA'], cwd=root)
(evidence / 'proof-change.patch').write_bytes(patch)
summary = dict(base=base, proof_head=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
               checks=len(checks), strict_attempts=len(strict), rejected_strict_attempts=0,
               final_strict_modules=3, public_declarations=9, audit_theorems=76712,
               public_lines=len(public.splitlines()), public_bytes=len(public_bytes),
               public_sha256=sha(public_bytes), unchanged_paths=unchanged,
               runtime_definitions_preserved=runtime_preserved, producer_admission_preserved=admission_preserved,
               source_sha256={p: sha((root / p).read_bytes()) for p in snapshots})
(evidence / 'verification.json').write_text(json.dumps(summary, indent=2) + '\n')
manifest = {str(p.relative_to(evidence)): dict(bytes=p.stat().st_size, sha256=sha(p.read_bytes()))
            for p in sorted(evidence.rglob('*')) if p.is_file()}
(evidence / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps(dict(payloads=len(manifest), total_bytes=sum(v['bytes'] for v in manifest.values()),
                     manifest_sha256=sha((evidence / 'manifest.json').read_bytes()))))
