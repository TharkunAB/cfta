import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-enabled-empty-20261024')
evidence = root / 'lean/restart-evidence/20261024-pruning-enumeration-enabled-empty'
assert not evidence.exists()
custody = json.loads((area / 'prior-custody-index.json').read_text())
assert len(custody) == 26 and len({pin['target'] for pin in custody}) == 26
assert hashlib.sha256((area / 'prior-custody-index.json').read_bytes()).hexdigest() == '535a98dadce34e1b0b473e01556c44f7c12623a5f5fef9b9ddc5e0a7040b760c'
summary = json.loads((area / 'previous-publication/post-publication-summary.json').read_text())
assert [pin['source'] for pin in custody] == summary['next_custody_inputs']
for pin in custody:
    assert not Path(pin['target']).is_absolute() and '..' not in Path(pin['target']).parts
    data = (area / 'previous-publication' / pin['target']).read_bytes()
    assert len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256']
assert {p.name for p in (area / 'previous-publication').iterdir()} == {pin['target'] for pin in custody}
assert Path('/tmp/mcfta-pruning-enumeration-enabled-empty-20261024-source-review.md').is_file()
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert Path('/tmp/mcfta-pruning-enumeration-enabled-empty-20261024-' + name + '-review.md').is_file()
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
for pattern in ['mcfta-pruning-enumeration-enabled-empty-20261024-*']:
    for path in sorted(Path('/tmp').glob(pattern)):
        if path.is_file() and not path.name.startswith('mcfta-pruning-enumeration-enabled-empty-20261024-archive-1.'):
            shutil.copyfile(path, inputs / path.name)
shutil.copytree('/tmp/mcfta-pruning-enumeration-enabled-empty-20261024-proposal', evidence / 'owner-proposal')
prior = evidence / 'previous-publication'
prior.mkdir()
for pin in custody:
    shutil.copyfile(area / 'previous-publication' / pin['target'], prior / pin['target'])
production = evidence / 'production-sources'
production.mkdir()
shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningEnumerationEnabledEmpty.lean', production / 'SourcePruningEnumerationEnabledEmpty.lean')
shutil.copyfile(root / 'lean/notes-current-pruning-enumeration-enabled-empty.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-enabled-empty-20261024-verify.py', evidence / 'verify-checkpoint.py')
(evidence / 'INDEX.md').write_text('# Checked enabled emptiness after pending intersections\n\nThe exact frozen owner and complete checked public types fix this scope.\ncheck uses the existing descendant/predicate memo runner on the computed\nquery. False skips only the fourth-memo call and retains saved guard memos.\nTrue uses the existing checked worker at source budget1000. One Caller.finite\nreceipt, completion and checked lifting concern the same actual call.\nThe producer derives post-query Context from genuine input Context and the\nsame TargetQuery Receipt. It supplies no successful query or worker result.\n\nTrue selects Empty. Otherwise the original query remains and can itself be\nEmpty. This is not an Empty-if-and-only-if-true claim. This stage performs no\nenumeration write. Equal raw source and target IDs are permitted here.\nNative cached indexes, flag/slot dispatch, host cache extraction and the full\nfinish/terminal caller composition remain separate.\n\nWork retains the complete baseline, exact declarations, source cuts, actual\ninput/report/raw failures and resource receipts. Previous-publication keeps\nall26 immediate custody inputs; older history remains protected by baseline.\nNo old failure or successful build count becomes a new actual result.\n\nRun verify-checkpoint.py with --root set to the repository root. It checks\nall baseline blobs and modes, nine exact document inverses, one Audit prefix,\nfrozen owner contracts, actual public axiom subsets and complete receipt sets.\nForce-add every manifest path and SHA256SUMS, including ignored raw logs.\nPublication requires every sealed path in HEAD and index/tree/file identity,\nthe singleton push URL and the ordinary formalize destination.\n\nNo Haskell source change is claimed. The six imported repair handoffs stay\nfirst in FINDINGS. H6 remains strongest combined. The whole goal stays ACTIVE\nand incomplete. Whole-library runtime, solver, resource and convergence\nclaims remain separate. No future successful check or commit is assumed.\n')

files = sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence / 'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(evidence).as_posix() + '\n' for p in files))
result = subprocess.run(['/usr/bin/python3', str(evidence / 'verify-checkpoint.py'), '--root', str(root)], cwd=root, capture_output=True)
report = dict(exit_code=result.returncode,
    manifest_sha256=hashlib.sha256((evidence / 'SHA256SUMS').read_bytes()).hexdigest(),
    manifest_entries=len(files), stdout=result.stdout.decode(), stderr=result.stderr.decode())
(area / 'seal-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
assert result.returncode == 0
