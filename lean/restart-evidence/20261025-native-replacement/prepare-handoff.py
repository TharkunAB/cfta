import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-native-replacement-20261025')
evidence = root / 'lean/restart-evidence/20261025-native-replacement'
base = '736c89f6c3dd395d9161bd4400066b5d182419a1'
block = '''## Actual native narrowing derives indexed caches

Replacement and reads: `9d4de2db2`. Narrowing producer: `04a5ba6d0`.
The goal stays ACTIVE.

Actual narrowing now derives the complete native enumeration cache for each
nonempty result. Equal handles keep the framed read cache. Changed handles
retain the actual representative read and write. The full old bucket is
removed and the full new bucket is added. Canonicality proves waiting-map
identity. The target flag is recomputed from the new node. Ready, root paths,
realization and reference history persist at the same written core.
Empty still has no successful enumeration branch. Old producers and workers stay.

Both new modules, Audit imports and installed public readback pass. Audit
checks 76721 theorem dependencies. H6 remains the strongest end-to-end language
result. Haskell is unchanged. Next: actual selection/recursion/callback/entry
composition and the full checked Caller/memo Context producer for narrowing.
The new theorem derives a native heap, not that complete Caller/Post packet.
Fragment-hole history, extraction and whole-driver semantics remain open.
Details: `lean/notes-current-pruning-enumeration-indexed-narrowing.md`.

'''
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/COVERAGE.md', 'lean/API-COVERAGE.md',
             'lean/notes-current-system-claim.md', 'lean/notes-proof-status-20261017.md']
for relative in documents:
    path = root / relative
    text = path.read_text()
    marker = '## Native narrowing retains pending-reference history'
    assert marker in text and block.splitlines()[0] not in text
    path.write_text(text.replace(marker, block + marker, 1))
path = root / 'FINDINGS.md'
text = path.read_text()
marker = '### Native narrowing reference preservation'
addition = '''### Indexed native narrowing and the full caller boundary

Enumeration.hs:436 passes the full old suspended bucket to writeUVarValue as
lost references and the full new bucket as gained references. Narrowing keeps
that bucket. The new proof executes both folds and proves the canonical
waiting map unchanged. It recomputes the target's native expandable flag.
The actual narrowing producer now derives this indexed cache at its returned
write endpoint. An unchanged handle keeps its framed read cache; Empty rejects.
Full checked Caller, memo Context, recursion-check and callback composition
remain separate. A native heap Keeps receipt is not that complete packet.
These are proof boundaries. No new Haskell runtime defect or repair is found.
External action: no patch is proposed for this source observation.
Details: lean/notes-current-pruning-enumeration-indexed-narrowing.md.

'''
assert addition.splitlines()[0] not in text
path.write_text(text.replace(marker, addition + marker, 1))
assert path.read_text().index('## Haskell fix handoff') < path.read_text().index(block.splitlines()[0])

sha = lambda data: hashlib.sha256(data).hexdigest()
checks = {p.parent.name: json.loads(p.read_text()) for p in sorted(area.glob('*/report.json'))}
failed = {'replacement-strict-1', 'replacement-strict-2', 'replacement-strict-3',
          'replacement-strict-4', 'narrow-cache-strict-1'}
assert len(checks) == 13 and {n for n, r in checks.items() if r['exit_code']} == failed
strict = {name for name in checks if '-strict-' in name}
assert len(strict) == 9
final_strict = {'replacement-reads-strict-1', 'narrow-cache-strict-2', 'audit-imports-strict-1'}
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
                assert raw.decode().strip() == 'Checked axiom dependencies of 76721 MicroCFTA theorems.'
public_bytes = (evidence / 'public-final/raw.log').read_bytes()
public = public_bytes.decode()
assert public.count('depends on axioms:') == 7 and '⋯' not in public and '...' not in public
assert sha((evidence / 'public-final/public.lean').read_bytes()) == checks['public-final']['source_sha256']
for axioms in re.findall(r'depends on axioms:\s*\[([^]]*)\]', public):
    assert set(re.findall(r'[A-Za-z_.]+', axioms)) <= {'propext', 'Classical.choice', 'Quot.sound'}
assert 'Checked axiom dependencies of 76721 MicroCFTA theorems.' in (evidence / 'aggregate-audit/raw.log').read_text()

sources = ['lean/MicroCFTA/' + name + '.lean' for name in [
    'SourcePruningEnumerationReplacement', 'SourcePruningEnumerationNarrowCache', 'Audit']]
snapshots = sources + ['lean/MicroCFTA/' + name + '.lean' for name in [
    'SourceCurrentColdFiniteWarmCalls', 'SourcePruningEnumerationAction', 'SourcePruningRecordTypes',
    'SourcePruningEnumerationNativeIndex', 'SourcePruningEnumerationNativeGrowth']]
snapshots += ['cfta/src/Data/CFTA/Enumeration.hs']
for relative in snapshots:
    target = evidence / 'sources' / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(root / relative, target)
    if relative in sources[:2]:
        assert not re.search(r'\b(sorry|admit|axiom)\b', (root / relative).read_text())
old_source = lambda relative: subprocess.check_output(['git', 'show', base + ':' + relative], cwd=root).decode()
unchanged = ['lean/MicroCFTA/' + name + '.lean' for name in [
    'SourcePruningEnumerationAction', 'SourcePruningEnumerationOuter', 'SourcePruningEnumerationNarrowing',
    'SourcePruningEnumerationReread', 'SourcePruningEnumerationWrites',
    'SourcePruningEnumerationNativeOrdinary', 'SourcePruningEnumerationNativeBranchCompletion',
    'SourcePruningEnumerationSelection', 'SourcePruningEnumerationSelectedEntry',
    'SourcePruningEnumerationNativeIndex', 'SourcePruningEnumerationNativeGrowth',
    'EnumerationPendingReplacement', 'SourcePruningRecordTypes', 'SourcePruningOracle',
    'SourceCurrentColdFiniteWarmCalls']]
unchanged += ['cfta/src/Data/CFTA/' + name for name in [
    'Enumeration.hs', 'Interned/Type.hs', 'Interned/Cache.hs', 'Interned/Memo.hs', 'Interned/Operations.hs']]
for relative in unchanged:
    assert old_source(relative) == (root / relative).read_text(), relative
subprocess.run(['git', 'diff', '--quiet', base, '--', '*.hs', '*.cabal'], cwd=root, check=True)
assert (root / sources[2]).read_text() == ('import MicroCFTA.SourcePruningEnumerationNarrowCache\n'
    'import MicroCFTA.SourcePruningEnumerationReplacement\n' + old_source(sources[2]))
for relative in sources[:2]:
    assert not re.search(r'^(?:noncomputable )?def ', (root / relative).read_text(), re.M)
(evidence / 'proof-change.patch').write_bytes(subprocess.check_output(
    ['git', 'diff', base, 'HEAD', '--', 'lean/MicroCFTA'], cwd=root))
summary = dict(base=base, proof_head=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
               checks=13, strict_attempts=9, rejected_strict_attempts=5, final_strict_modules=3,
               public_declarations=7, audit_theorems=76721, public_lines=len(public.splitlines()),
               public_bytes=len(public_bytes), public_sha256=sha(public_bytes), unchanged_paths=unchanged,
               new_runtime_workers=0, old_producer_contracts_preserved=True, audit_changes='two imports only',
               source_sha256={p: sha((root / p).read_bytes()) for p in snapshots})
(evidence / 'verification.json').write_text(json.dumps(summary, indent=2) + '\n')
manifest = {str(p.relative_to(evidence)): dict(bytes=p.stat().st_size, sha256=sha(p.read_bytes()))
            for p in sorted(evidence.rglob('*')) if p.is_file()}
(evidence / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps(dict(payloads=len(manifest), total_bytes=sum(v['bytes'] for v in manifest.values()),
                     manifest_sha256=sha((evidence / 'manifest.json').read_bytes()))))
