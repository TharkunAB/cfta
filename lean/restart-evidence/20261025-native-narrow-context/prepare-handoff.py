import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-native-narrow-context-20261025')
evidence = root / 'lean/restart-evidence/20261025-native-narrow-context'
base = 'a12a9605b36b2d55fd290ec29c6f26ef578b45bf'
block = '''## Actual native narrowing derives caller and indexed caches together

Caller and memos: `d677fd77b`. Combined producer: `6e83025d8`.
The goal stays ACTIVE.

One actual native narrowing result now derives the full checked Caller Post,
valid saved global memos and indexed enumeration cache at the same result
heap. The proof uses the actual exposure and filtered constructor. The
combined producer derives completion and the final Context from initial
invariants and an actual value-read receipt. Equal handles retain their
framed cache. Changed handles retain the actual reread and indexed write.
Empty retains reached Caller effects and has no successful enumeration state.
Saved memos belong to the chosen exposure fuel; their equality across all
larger fuels is not proved. No old producer or runtime worker changes.

Both new modules, Audit import and installed public readback pass. Audit
checks 76724 theorem dependencies. H6 remains the strongest end-to-end language
result. Haskell is unchanged. Next: actual selection/recursion/callback/entry
composition. Fragment-hole history, extraction and whole-driver semantics
remain open. Arbitrary narrowing predicates have no new semantic guarantee.
Details: `lean/notes-current-pruning-enumeration-narrow-context.md`.

'''
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/COVERAGE.md', 'lean/API-COVERAGE.md',
             'lean/notes-current-system-claim.md', 'lean/notes-proof-status-20261017.md']
for relative in documents:
    path = root / relative
    text = path.read_text()
    marker = '## Actual native narrowing derives indexed caches'
    assert marker in text and block.splitlines()[0] not in text
    path.write_text(text.replace(marker, block + marker, 1))
path = root / 'FINDINGS.md'
text = path.read_text()
marker = '### Indexed native narrowing and the full caller boundary'
addition = '''### Actual native narrowing retains the full caller and memos

The modeled native narrowing producer now derives the full checked Caller
Post, global memo validity and indexed enumeration cache at one result heap.
The proof follows the actual row exposure and filtered constructor. It keeps
native effects on Empty before enumeration rejects. The earlier full Caller
boundary is closed for this operation. The saved memo receipt uses one
concrete exposure fuel; equality of saved tables across larger fuels is open.
Actual recursion checks, callbacks and whole-driver composition remain open.
These are proof boundaries. No new Haskell runtime defect or repair is found.
External action: no patch is proposed for this source observation.
Details: lean/notes-current-pruning-enumeration-narrow-context.md.

'''
assert addition.splitlines()[0] not in text
path.write_text(text.replace(marker, addition + marker, 1))
assert path.read_text().index('## Haskell fix handoff') < path.read_text().index(block.splitlines()[0])

sha = lambda data: hashlib.sha256(data).hexdigest()
checks = {p.parent.name: json.loads(p.read_text()) for p in sorted(area.glob('*/report.json'))}
failed = {'native-context-strict-1', 'native-context-strict-2', 'native-context-strict-3',
          'native-context-strict-4', 'combined-context-strict-1'}
assert len(checks) == 11 and {n for n, r in checks.items() if r['exit_code']} == failed
strict = {name for name in checks if '-strict-' in name}
assert len(strict) == 8
final_strict = {'native-context-strict-5', 'combined-context-strict-2', 'audit-import-strict-1'}
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
                assert raw.decode().strip() == 'Checked axiom dependencies of 76724 MicroCFTA theorems.'
public_bytes = (evidence / 'public-final/raw.log').read_bytes()
public = public_bytes.decode()
assert public.count('depends on axioms:') == 6 and '⋯' not in public and '...' not in public
assert sha((evidence / 'public-final/public.lean').read_bytes()) == checks['public-final']['source_sha256']
for axioms in re.findall(r'depends on axioms:\s*\[([^]]*)\]', public):
    assert set(re.findall(r'[A-Za-z_.]+', axioms)) <= {'propext', 'Classical.choice', 'Quot.sound'}
assert 'Checked axiom dependencies of 76724 MicroCFTA theorems.' in (evidence / 'aggregate-audit/raw.log').read_text()

sources = ['lean/MicroCFTA/' + name + '.lean' for name in [
    'SourcePruningNativeContext', 'SourcePruningEnumerationNarrowContext', 'Audit']]
snapshots = sources + ['lean/MicroCFTA/' + name + '.lean' for name in [
    'SourceCurrentColdFiniteWarmCalls', 'SourcePruningNativeView', 'SourcePruningOuterNarrow',
    'SourcePruningEnumerationNarrowCache', 'SourceEqualityQueryGlobalMemos']]
snapshots += ['cfta/src/Data/CFTA/Enumeration.hs']
for relative in snapshots:
    target = evidence / 'sources' / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(root / relative, target)
    if relative in sources[:2]:
        assert not re.search(r'\b(sorry|admit|axiom)\b', (root / relative).read_text())
old_source = lambda relative: subprocess.check_output(['git', 'show', base + ':' + relative], cwd=root).decode()
unchanged = ['lean/MicroCFTA/' + name + '.lean' for name in [
    'SourcePruningEnumerationAction', 'SourcePruningEnumerationNarrowCache', 'SourcePruningEnumerationReplacement',
    'SourcePruningOuterNarrow', 'SourcePruningNativeView',
    'SourcePruningEnumerationNativeOrdinary', 'SourcePruningEnumerationNativeBranchCompletion',
    'SourcePruningEnumerationNativeBranches', 'SourcePruningEnumerationSelection',
    'SourcePruningEnumerationSelectedEntry', 'SourcePruningRecordTypes',
    'SourceEqualityQueryGlobalMemos', 'SourceCurrentColdFiniteWarmCalls']]
unchanged += ['cfta/src/Data/CFTA/' + name for name in [
    'Enumeration.hs', 'Interned/Type.hs', 'Interned/Cache.hs', 'Interned/Memo.hs', 'Interned/Operations.hs']]
for relative in unchanged:
    assert old_source(relative) == (root / relative).read_text(), relative
subprocess.run(['git', 'diff', '--quiet', base, '--', '*.hs', '*.cabal'], cwd=root, check=True)
assert (root / sources[2]).read_text() == ('import MicroCFTA.SourcePruningEnumerationNarrowContext\n' + old_source(sources[2]))
for relative in sources[:2]:
    assert not re.search(r'^(?:noncomputable )?def ', (root / relative).read_text(), re.M)
(evidence / 'proof-change.patch').write_bytes(subprocess.check_output(
    ['git', 'diff', base, 'HEAD', '--', 'lean/MicroCFTA'], cwd=root))
summary = dict(base=base, proof_head=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
               checks=11, strict_attempts=8, rejected_strict_attempts=5, final_strict_modules=3,
               public_declarations=6, audit_theorems=76724, public_lines=len(public.splitlines()),
               public_bytes=len(public_bytes), public_sha256=sha(public_bytes), unchanged_paths=unchanged,
               new_runtime_workers=0, old_producer_contracts_preserved=True, audit_changes='one import only',
               memo_fuel_scope='chosen exposure fuel only; larger-fuel saved-memo equality remains open',
               source_sha256={p: sha((root / p).read_bytes()) for p in snapshots})
(evidence / 'verification.json').write_text(json.dumps(summary, indent=2) + '\n')
manifest = {str(p.relative_to(evidence)): dict(bytes=p.stat().st_size, sha256=sha(p.read_bytes()))
            for p in sorted(evidence.rglob('*')) if p.is_file()}
(evidence / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps(dict(payloads=len(manifest), total_bytes=sum(v['bytes'] for v in manifest.values()),
                     manifest_sha256=sha((evidence / 'manifest.json').read_bytes()))))
