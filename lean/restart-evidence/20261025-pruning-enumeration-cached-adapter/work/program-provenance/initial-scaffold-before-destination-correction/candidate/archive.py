import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-cached-adapter-20261025')
evidence = root / 'lean/restart-evidence/20261025-pruning-enumeration-cached-dispatch'
assert not evidence.exists()
custody = json.loads((area / 'prior-custody-index.json').read_text())
assert len(custody) == 26 and len({pin['target'] for pin in custody}) == 26
assert hashlib.sha256((area / 'prior-custody-index.json').read_bytes()).hexdigest() == 'd3f3c8c28b241a7b80cebcfb3271870da12e34a83cee69db9ddad30b7093efda'
summary = json.loads((area / 'previous-publication/post-publication-summary.json').read_text())
assert [pin['source'] for pin in custody] == summary['next_custody_inputs']
for pin in custody:
    assert not Path(pin['target']).is_absolute() and '..' not in Path(pin['target']).parts
    data = (area / 'previous-publication' / pin['target']).read_bytes()
    assert len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256']
assert {p.name for p in (area / 'previous-publication').iterdir()} == {pin['target'] for pin in custody}
assert Path('/tmp/mcfta-pruning-enumeration-cached-adapter-20261025-source-review.md').is_file()
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert Path('/tmp/mcfta-pruning-enumeration-cached-adapter-20261025-' + name + '-review.md').is_file()
evidence.mkdir()
for path in sorted(area.rglob('*')):
    if not path.is_file():
        continue
    target = evidence / 'work' / path.relative_to(area)
    target.parent.mkdir(parents=True, exist_ok=True)
    if path.name == 'baseline-tree.txt':
        target.with_suffix('.txt.gz').write_bytes(gzip.compress(path.read_bytes(), mtime=0))
    else:
        target.write_bytes(path.read_bytes())
inputs = evidence / 'inputs'
inputs.mkdir()
for pattern in ['mcfta-pruning-enumeration-cached-adapter-20261025-*']:
    for path in sorted(Path('/tmp').glob(pattern)):
        if path.is_file() and not path.name.startswith('mcfta-pruning-enumeration-cached-adapter-20261025-archive-1.'):
            shutil.copyfile(path, inputs / path.name)
shutil.copytree('/tmp/mcfta-pruning-enumeration-cached-adapter-20261025-proposal', evidence / 'owner-proposal')
prior = evidence / 'previous-publication'
prior.mkdir()
for pin in custody:
    shutil.copyfile(area / 'previous-publication' / pin['target'], prior / pin['target'])
production = evidence / 'production-sources'
production.mkdir()
shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningEnumerationCachedAdapter.lean', production / 'SourcePruningEnumerationCachedAdapter.lean')
shutil.copyfile(root / 'lean/notes-current-pruning-enumeration-cached-dispatch.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-cached-adapter-20261025-verify.py', evidence / 'verify-checkpoint.py')
(evidence / 'INDEX.md').write_text("# Native cached raw-row adapter\n\nUNFROZEN SOURCE/DATA SCAFFOLD. Root selected adapt and run definitions plus one complete theorem, four typed haves and one definition-local let raw. There are no other planned instances, helpers or induction. Exact contracts, type/return layout, source estimates, owner inventory and source-review binding remain pending. No body or result is claimed by this preparation.\n\nThe selected direction reuses existing dispatch once and its captured action once. Preserve reached Caller/query observations, lazy no-ops, actual raw rows, Empty rejection and outer missing/decode None distinctly. The previous assessment recommends classifying the actual singleton target slot at its reached heap, with explicit classifier failure and no default false. Root still owns the exact interface and genuine input domain. No closure inspection, proof-witness extraction, repeated native query, supplied successful callback or future Fold.Ranges premise is introduced by the scaffold.\n\nAll 147603 baseline files/modes/refs/stashes/worktrees remain guarded, with nine exact document inverses, one Audit prepend and separate audit-addition.json. Exactly 26 actual CachedDispatch custody items retain their listed order, complete 13618-byte summary, canonical assessment and separate sealed peer. All original owner literals must remain exact once and equal the original body gate. Full failure/raw/public/axiom checks, six-artifact 4 GiB cap families, documents-1 non-Lean ledger, all manifest files committed in HEAD, file/index/tree/mode equality and singleton ordinary publication destination remain unchanged.\n\nH6 remains strongest and the whole goal ACTIVE. All six Haskell repair handoffs remain first. No Haskell change, arbitrary fault invariant, future Fold admission, native selector/partition/fallback, wrapper integration, physical maps/machine integers, extraction, Safe/LiveRoots or full-driver result is claimed. All validation, failure, public axiom, seal and push fields remain unbound. This candidate is unactivated and must not execute before actual contracts/owner/source binding, independent review and Root's gate.\n")

files = sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence / 'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(evidence).as_posix() + '\n' for p in files))
result = subprocess.run(['/usr/bin/python3', str(evidence / 'verify-checkpoint.py'), '--root', str(root)], cwd=root, capture_output=True)
report = dict(exit_code=result.returncode,
    manifest_sha256=hashlib.sha256((evidence / 'SHA256SUMS').read_bytes()).hexdigest(),
    manifest_entries=len(files), stdout=result.stdout.decode(), stderr=result.stderr.decode())
(area / 'seal-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
assert result.returncode == 0
