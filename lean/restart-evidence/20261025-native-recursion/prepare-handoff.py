import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-native-recursion-20261025')
evidence = root / 'lean/restart-evidence/20261025-native-recursion'
base = '70a3dbc5b52aff81e3be7ba072ce789e269bbd16'
block = '''## Selected reads and native recursion checks complete

Clearing history and indexes: `0e9d54829`. Native prefix: `b13953d85`.
The goal stays ACTIVE.

Original selection and initial invariants now derive the actual pending read
and native recursion check. No successful read or check is supplied. Mu and
explicit Union use the native boundary test. A false check retains its full
compression frame and bucket. A repeated key clears the bucket, subtracts
all lost references from waiting counts and disables the selected slot.
Both endpoints retain safety and native cache/reference invariants.
The selected proof uses no early ordinary-entry ancestry update.

All four changed modules, installed public readback and Audit pass. Audit
checks 76730 dependencies. H6 remains the strongest end-to-end language result.
Haskell is unchanged. Next: expose the false check's actual compression frame
in NarrowCache/NarrowContext via the existing framed Action producer, without
an extra source read. Then compose the pure Right callback and ordinary entry.
The repeated branch's scheduler restart, fragment history, extraction and
whole-driver language semantics remain open. No loop termination is proved.
Details: `lean/notes-current-pruning-enumeration-native-recursion.md`.

'''
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/COVERAGE.md', 'lean/API-COVERAGE.md',
             'lean/notes-current-system-claim.md', 'lean/notes-proof-status-20261017.md']
for relative in documents:
    path = root / relative
    text = path.read_text()
    marker = '## Actual native narrowing derives caller and indexed caches together'
    assert marker in text and block.splitlines()[0] not in text
    path.write_text(text.replace(marker, block + marker, 1))
path = root / 'FINDINGS.md'
text = path.read_text()
marker = '### Actual native narrowing retains the full caller and memos'
addition = '''### Native repeated-recursion clearing and source order

Enumeration.hs:993 reads the selected pending value before checking recursion.
Interned/Type.hs:608 treats both Mu and explicit Union as recursive boundaries.
The new native guard follows those cases. A repeated key clears the full
suspended bucket, removes every lost waiting count and disables the slot.
It restarts selection without narrowing or an oracle call. A false check can
compress representatives. The proof retains that actual frame and does not
perform the later ordinary-entry ancestry update early. Stable finite prefix
execution and native cache invariants are proved from original selection.
Whole-loop progress and language equivalence of clearing remain open.
No new Haskell runtime defect or repair is found.
External action: no patch is proposed for this source observation.
Details: lean/notes-current-pruning-enumeration-native-recursion.md.

'''
assert addition.splitlines()[0] not in text
path.write_text(text.replace(marker, addition + marker, 1))
assert path.read_text().index('## Haskell fix handoff') < path.read_text().index(block.splitlines()[0])

sha = lambda data: hashlib.sha256(data).hexdigest()
checks = {p.parent.name: json.loads(p.read_text()) for p in sorted(area.glob('*/report.json'))}
failed = {'clear-reference-strict-1', 'native-clear-strict-1', 'native-recursion-strict-1',
          'native-recursion-strict-2', 'native-recursion-strict-3', 'native-recursion-selected-strict-1'}
assert len(checks) == 15 and {n for n, r in checks.items() if r['exit_code']} == failed
strict = {name for name in checks if '-strict-' in name}
assert len(strict) == 11
final_strict = {'clear-reference-strict-2', 'native-clear-strict-2',
                'native-recursion-selected-strict-2', 'audit-import-strict-1'}
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
        assert sha(source.read_bytes()) == report['source_sha256']
        if name in final_strict:
            assert source.read_bytes() == (root / 'lean/MicroCFTA' / source.name).read_bytes()
            if source.name != 'Audit.lean':
                assert not raw
            else:
                assert raw.decode().strip() == 'Checked axiom dependencies of 76730 MicroCFTA theorems.'
public_bytes = (evidence / 'public-final/raw.log').read_bytes()
public = public_bytes.decode()
assert public.count('depends on axioms:') == 6 and '⋯' not in public and '...' not in public
assert sha((evidence / 'public-final/public.lean').read_bytes()) == checks['public-final']['source_sha256']
for axioms in re.findall(r'depends on axioms:\s*\[([^]]*)\]', public):
    assert set(re.findall(r'[A-Za-z_.]+', axioms)) <= {'propext', 'Classical.choice', 'Quot.sound'}
assert 'Checked axiom dependencies of 76730 MicroCFTA theorems.' in (evidence / 'aggregate-audit/raw.log').read_text()

sources = ['lean/MicroCFTA/' + name + '.lean' for name in [
    'EnumerationPendingReplacement', 'SourcePruningEnumerationClear', 'SourcePruningEnumerationRecursion', 'Audit']]
snapshots = sources + ['lean/MicroCFTA/' + name + '.lean' for name in [
    'SourceCurrentColdFiniteWarmCalls', 'SourcePruningEnumerationEntry', 'SourcePruningEnumerationSelection',
    'SourcePruningEnumerationNativeIndex', 'SourcePruningEnumerationNarrowContext', 'SourcePruningEnumerationAction']]
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
    'SourcePruningEnumerationAction', 'SourcePruningEnumerationNarrowCache', 'SourcePruningEnumerationNarrowContext',
    'SourcePruningNativeContext', 'SourcePruningEnumerationReplacement', 'SourcePruningEnumerationNativeIndex',
    'SourcePruningOuterNarrow', 'SourcePruningNativeView', 'SourcePruningEnumerationNativeOrdinary',
    'SourcePruningEnumerationNativeBranchCompletion', 'SourcePruningEnumerationNativeBranches',
    'SourcePruningEnumerationSelectedEntry', 'SourcePruningRecordTypes', 'SourceCurrentColdFiniteWarmCalls']]
unchanged += ['cfta/src/Data/CFTA/' + name for name in [
    'Enumeration.hs', 'Interned/Type.hs', 'Interned/Cache.hs', 'Interned/Memo.hs', 'Interned/Operations.hs']]
for relative in unchanged:
    assert old_source(relative) == (root / relative).read_text(), relative
subprocess.run(['git', 'diff', '--quiet', base, '--', '*.hs', '*.cabal'], cwd=root, check=True)
assert (root / sources[3]).read_text() == ('import MicroCFTA.SourcePruningEnumerationRecursion\n' + old_source(sources[3]))
old_history = old_source(sources[0])
old_end = 'end MicroCFTA.EnumerationPendingReplacement\n'
assert old_history.endswith(old_end)
assert (root / sources[0]).read_text().startswith(old_history[:-len(old_end)])
assert not re.search(r'^(?:noncomputable )?def ', (root / sources[1]).read_text(), re.M)
worker_names = re.findall(r'^def ([A-Za-z_][A-Za-z_0-9]*)', (root / sources[2]).read_text(), re.M)
assert worker_names == ['checkRepeated']
(evidence / 'proof-change.patch').write_bytes(subprocess.check_output(
    ['git', 'diff', base, 'HEAD', '--', 'lean/MicroCFTA'], cwd=root))
summary = dict(base=base, proof_head=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
               checks=15, strict_attempts=11, rejected_strict_attempts=6, final_strict_modules=4,
               public_declarations=6, audit_dependencies=76730, public_lines=len(public.splitlines()),
               public_bytes=len(public_bytes), public_sha256=sha(public_bytes), unchanged_paths=unchanged,
               new_runtime_workers=1, new_worker='SourcePruningEnumerationRecursion.checkRepeated',
               old_producer_contracts_preserved=True, audit_changes='one import only',
               prefix_scope='ends before narrowing/oracles or the repeated branch scheduler restart',
               source_sha256={p: sha((root / p).read_bytes()) for p in snapshots})
(evidence / 'verification.json').write_text(json.dumps(summary, indent=2) + '\n')
manifest = {str(p.relative_to(evidence)): dict(bytes=p.stat().st_size, sha256=sha(p.read_bytes()))
            for p in sorted(evidence.rglob('*')) if p.is_file()}
(evidence / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps(dict(payloads=len(manifest), total_bytes=sum(v['bytes'] for v in manifest.values()),
                     manifest_sha256=sha((evidence / 'manifest.json').read_bytes()))))
