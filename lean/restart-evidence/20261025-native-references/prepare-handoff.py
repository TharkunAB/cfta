import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-native-references-20261025')
evidence = root / 'lean/restart-evidence/20261025-native-references'
base = 'dccf997655b4560f24485b1e0ea0a95cc58e7a12'
block = '''## Native suspended-reference history through captured finalization

Mutation shape: `fa26b8e1b14aeb15a9c04bdc178200fb0b3db068`.
Reference history: `3a765d71dee49787ab5f191a3a9eb59818c180c2`.
The goal stays ACTIVE.

Actual terminal, child, traversal and selected-edge completion now retain
fixed allowed references and global pending-reference history. Selected-edge
completion also preserves incoming avoidance of a protected old root.
Captured-edge completion preserves global pending references through the
original raw-slot final write, given initial pending history and no incoming
reference to its target. These are output implications. No producer admission
premise, numeric Ranges condition or runtime worker body changed. Both valid
rejection paths remain covered without an unconditional Safe claim.

All nine changed modules pass strict checking. Installed public readback and
Audit pass. The audit checks 76709 theorem dependencies. Haskell and H6 are
unchanged. H6 remains the strongest end-to-end language theorem. Next carry
the captured-edge history into each alternative receipt and derive initial
incoming avoidance from actual unblocked selection. Fragment-hole history,
extraction, narrowing/oracle preservation and whole-driver semantics remain.
Details: `lean/notes-current-pruning-enumeration-native-references.md`.

'''
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/COVERAGE.md', 'lean/API-COVERAGE.md',
             'lean/notes-current-system-claim.md', 'lean/notes-proof-status-20261017.md']
for relative in documents:
    path = root / relative
    text = path.read_text()
    marker = '## Actual entry and native ordinary alternatives'
    assert marker in text and block.splitlines()[0] not in text
    path.write_text(text.replace(marker, block + marker, 1))
path = root / 'FINDINGS.md'
text = path.read_text()
marker = '### Specftacular parallel completion follow-ups'
addition = '''### Native reference mutation order

Assimilation rejects Empty before its target replacement and source elimination.
Incoming restriction writes its pending payload and inherits ancestry before
Empty rejection. A raw-empty result therefore does not always mean no mutation.
The actual incoming cache adapter reconstructs that post-write cache.
The native reference proof now covers both cases on the actual returned
producer witnesses. Captured finalization additionally needs no incoming
reference to the target that becomes enumerated. Ready.avoids alone covers
only that target's own bucket. No Haskell runtime defect or new repair is
identified. External action: no patch is proposed for this source observation.
Details: lean/notes-current-pruning-enumeration-native-references.md.

'''
assert addition.splitlines()[0] not in text
path.write_text(text.replace(marker, addition + marker, 1))
assert path.read_text().index('## Haskell fix handoff') < path.read_text().index(block.splitlines()[0])

checks = {p.parent.name: json.loads(p.read_text()) for p in sorted(area.glob('*/report.json'))}
assert len(checks) == 24
failed = {'dispatch-shape-strict-2', 'native-references-strict-1',
          'terminal-references-strict-1', 'terminal-references-strict-2'}
assert {name for name, report in checks.items() if report['exit_code']} == failed
strict = {name for name in checks if '-strict-' in name}
assert len(strict) == 14
final_strict = {'dispatch-shape-strict-3', 'fold-invariants-strict-1', 'native-references-strict-3',
                'terminal-references-strict-3', 'child-references-strict-1', 'traversal-references-strict-1',
                'selected-reference-history-strict-1', 'captured-reference-history-strict-1', 'branch-consumer-strict-1'}
evidence.mkdir()
for name in checks:
    shutil.copytree(area / name, evidence / name)
for name in ['check.py', 'prepare-handoff.py', 'heavy-peaks', 'preparation-events.txt']:
    shutil.copyfile(area / name, evidence / name)
shutil.copyfile('/tmp/mcfta-reference-shape.py', evidence / 'shape-generator.py')
sha = lambda data: hashlib.sha256(data).hexdigest()
for name, report in checks.items():
    raw = (evidence / name / 'raw.log').read_bytes()
    assert len(raw) == report['bytes'] and sha(raw) == report['sha256']
    if name in strict:
        source = next((evidence / name / 'MicroCFTA').glob('*.lean'))
        assert sha(source.read_bytes()) == report['source_sha256']
        if name in final_strict:
            assert source.read_bytes() == (root / 'lean/MicroCFTA' / source.name).read_bytes()
            assert not raw
public_bytes = (evidence / 'public-final/raw.log').read_bytes()
public = public_bytes.decode()
assert public.count('depends on axioms:') == 15 and '⋯' not in public and '...' not in public
assert sha((evidence / 'public-final/public.lean').read_bytes()) == checks['public-final']['source_sha256']
for axioms in re.findall(r'depends on axioms:\s*\[([^]]*)\]', public):
    assert set(re.findall(r'[A-Za-z_.]+', axioms)) <= {'propext', 'Classical.choice', 'Quot.sound'}
assert 'Checked axiom dependencies of 76709 MicroCFTA theorems.' in (evidence / 'aggregate-audit/raw.log').read_text()

modules = ['SourcePruningEnumerationDispatchShape', 'SourcePruningEnumerationFoldInvariants',
           'SourcePruningEnumerationNativeReferences', 'SourcePruningEnumerationCachedTerminalAdapter',
           'SourcePruningEnumerationChildCompletion', 'SourcePruningEnumerationTraversalCompletion',
           'SourcePruningEnumerationSelectedEdge', 'SourcePruningEnumerationCapturedEdge',
           'SourcePruningEnumerationNativeBranchCompletion']
sources = ['lean/MicroCFTA/' + name + '.lean' for name in modules]
snapshots = sources + ['lean/MicroCFTA/' + name + '.lean' for name in [
    'Audit', 'SourceCurrentColdFiniteWarmCalls', 'SourcePruningEnumerationNativeOrdinary']]
snapshots += ['cfta/src/Data/CFTA/Enumeration.hs']
for relative in snapshots:
    target = evidence / 'sources' / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(root / relative, target)
    if relative in sources:
        assert not re.search(r'\b(sorry|admit|axiom)\b', (root / relative).read_text())
unchanged = ['lean/MicroCFTA/' + name + '.lean' for name in [
    'SourcePruningEnumerationSelectedEntry', 'SourcePruningEnumerationFinalize',
    'SourcePruningEnumerationNativeOrdinary', 'SourcePruningEnumerationNativeBranches',
    'SourcePruningEnumerationNativeIndex', 'SourcePruningEnumerationChildDispatch',
    'SourcePruningEnumerationChildTraversal', 'SourceCurrentAllocatedPartialInvariant',
    'SourceCurrentColdFiniteWarmCalls', 'Audit']]
unchanged += ['cfta/src/Data/CFTA/' + name for name in [
    'Enumeration.hs', 'Interned/Type.hs', 'Interned/Cache.hs', 'Interned/Memo.hs', 'Interned/Operations.hs']]
old_source = lambda relative: subprocess.check_output(['git', 'show', base + ':' + relative], cwd=root).decode()
for relative in unchanged:
    assert old_source(relative) == (root / relative).read_text(), relative
subprocess.run(['git', 'diff', '--quiet', base, '--', '*.hs', '*.cabal'], cwd=root, check=True)

def definitions(text):
    pattern = r'^(?:noncomputable )?def (\w+)[\s\S]*?(?=^/--|^private theorem |^theorem |^end |\Z)'
    return {match.group(1): match.group(0) for match in re.finditer(pattern, text, re.M)}

runtime_preserved = []
admission_preserved = []
for name in modules:
    relative = 'lean/MicroCFTA/' + name + '.lean'
    current = (root / relative).read_text()
    if name in ['SourcePruningEnumerationDispatchShape', 'SourcePruningEnumerationNativeReferences']:
        assert not definitions(current)
        continue
    previous = old_source(relative)
    assert definitions(previous) == definitions(current), name
    runtime_preserved.append(name)
    if name not in ['SourcePruningEnumerationFoldInvariants', 'SourcePruningEnumerationNativeBranchCompletion']:
        old_head = previous.split('theorem complete\n', 1)[1].split(' :\n    ∃', 1)[0]
        new_head = current.split('theorem complete\n', 1)[1].split(' :\n    ∃', 1)[0]
        assert old_head == new_head, name
        admission_preserved.append(name)
    else:
        declaration = 'dispatch_preserves' if name.endswith('FoldInvariants') else 'complete'
        old_contract = previous.split('theorem ' + declaration + '\n', 1)[1].split(':= by', 1)[0]
        new_contract = current.split('theorem ' + declaration + '\n', 1)[1].split(':= by', 1)[0]
        assert old_contract == new_contract, name

patch = subprocess.check_output(['git', 'diff', base, 'HEAD', '--', 'lean/MicroCFTA'], cwd=root)
(evidence / 'proof-change.patch').write_bytes(patch)
summary = dict(base=base, proof_head=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
               checks=len(checks), strict_attempts=len(strict), rejected_strict_attempts=len(failed),
               final_strict_modules=len(final_strict), public_declarations=15, audit_theorems=76709,
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
