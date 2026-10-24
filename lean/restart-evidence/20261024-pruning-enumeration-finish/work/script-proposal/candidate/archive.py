import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-finish-20261024')
evidence = root / 'lean/restart-evidence/20261024-pruning-enumeration-finish'
assert not evidence.exists()
custody = json.loads((area / 'prior-custody-index.json').read_text())
assert len(custody) == 26 and len({pin['target'] for pin in custody}) == 26
assert hashlib.sha256((area / 'prior-custody-index.json').read_bytes()).hexdigest() == 'f7a8f67d374d4fa2fff329717fb17770119d475f1c05599462dc36e724f816b1'
summary = json.loads((area / 'previous-publication/post-publication-summary.json').read_text())
assert [pin['source'] for pin in custody] == summary['next_custody_inputs']
for pin in custody:
    assert not Path(pin['target']).is_absolute() and '..' not in Path(pin['target']).parts
    data = (area / 'previous-publication' / pin['target']).read_bytes()
    assert len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256']
assert {p.name for p in (area / 'previous-publication').iterdir()} == {pin['target'] for pin in custody}
assert Path('/tmp/mcfta-pruning-enumeration-finish-20261024-source-review.md').is_file()
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert Path('/tmp/mcfta-pruning-enumeration-finish-20261024-' + name + '-review.md').is_file()
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
for pattern in ['mcfta-pruning-enumeration-finish-20261024-*']:
    for path in sorted(Path('/tmp').glob(pattern)):
        if path.is_file() and not path.name.startswith('mcfta-pruning-enumeration-finish-20261024-archive-1.'):
            shutil.copyfile(path, inputs / path.name)
shutil.copytree('/tmp/mcfta-pruning-enumeration-finish-20261024-proposal', evidence / 'owner-proposal')
prior = evidence / 'previous-publication'
prior.mkdir()
for pin in custody:
    shutil.copyfile(area / 'previous-publication' / pin['target'], prior / pin['target'])
production = evidence / 'production-sources'
production.mkdir()
shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningEnumerationFinish.lean', production / 'SourcePruningEnumerationFinish.lean')
shutil.copyfile(root / 'lean/notes-current-pruning-enumeration-finish.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-finish-20261024-verify.py', evidence / 'verify-checkpoint.py')
(evidence / 'INDEX.md').write_text('# Existing assimilation after the derived replacement\n\nThe exact frozen owner and complete checked public type fix finish_complete.\nThis theorem consumes the actual returned heap and complete replacement to\ncomplete the existing Assimilation.finish action. Empty gives exact raw\nrejection before writes. A nonempty replacement gives the existing assimilated\nsingleton, both actual slot reads and all-slot PendingRealized. Source parts\nprecede target parts. It adds no action or repeated native query.\n\nDistinct raw slots and the original stored-slot equations remain explicit.\nHeap coherence, replacement availability/closedness/encoding and realization\nare supplied by the completed producer. This theorem updates enumeration\nvalues and ancestry; it does not claim a complete compression Frame.\nThe native query/worker receipts remain in the preceding producer. Initial\nflags, optional-slot dispatch, cached indexes/containers and the full terminal\ncaller correspondence remain separate.\n\nWork preserves the complete baseline, literal owner contracts, actual source\nand public inputs, raw failures and resource receipts. Previous-publication\nretains all26 immediate custody inputs. Older failure and gate history remain\nprotected by baseline; they are not inherited as new failures or outcomes.\n\nRun verify-checkpoint.py with --root set to the repository root. It checks\nall baseline blobs and modes, nine exact document inverses, one Audit prefix,\nfrozen owner contracts, actual public axiom subsets and complete receipt sets.\nForce-add every manifest path and SHA256SUMS, including ignored raw logs.\nPublication requires every sealed path in HEAD and index/tree/file identity,\nthe singleton push URL and the ordinary formalize destination.\n\nNo Haskell change is claimed. The six imported repair handoffs stay first in\nFINDINGS. H6 remains strongest combined. The whole goal stays ACTIVE and\nincomplete. Runtime, solver, resource and convergence claims remain separate.\nNo future successful check, seal or publication is assumed.\n')

files = sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence / 'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(evidence).as_posix() + '\n' for p in files))
result = subprocess.run(['/usr/bin/python3', str(evidence / 'verify-checkpoint.py'), '--root', str(root)], cwd=root, capture_output=True)
report = dict(exit_code=result.returncode,
    manifest_sha256=hashlib.sha256((evidence / 'SHA256SUMS').read_bytes()).hexdigest(),
    manifest_entries=len(files), stdout=result.stdout.decode(), stderr=result.stderr.decode())
(area / 'seal-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
assert result.returncode == 0
