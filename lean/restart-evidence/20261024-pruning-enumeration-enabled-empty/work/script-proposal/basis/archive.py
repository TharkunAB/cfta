import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-assimilation-20261024')
evidence = root / 'lean/restart-evidence/20261024-pruning-enumeration-assimilation'
assert not evidence.exists()
custody = json.loads((area / 'prior-custody-index.json').read_text())
assert len(custody) == 26 and len({pin['target'] for pin in custody}) == 26
assert hashlib.sha256((area / 'prior-custody-index.json').read_bytes()).hexdigest() == '0951f75d30d1eac92bd80251888977e2b5abc8923ed248151098b970011a5f9f'
summary = json.loads((area / 'previous-publication/post-publication-summary.json').read_text())
assert [pin['source'] for pin in custody] == summary['next_custody_inputs']
for pin in custody:
    assert not Path(pin['target']).is_absolute() and '..' not in Path(pin['target']).parts
    data = (area / 'previous-publication' / pin['target']).read_bytes()
    assert len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256']
assert {p.name for p in (area / 'previous-publication').iterdir()} == {pin['target'] for pin in custody}
assert Path('/tmp/mcfta-pruning-enumeration-assimilation-20261024-source-review.md').is_file()
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert Path('/tmp/mcfta-pruning-enumeration-assimilation-20261024-' + name + '-review.md').is_file()
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
for pattern in ['mcfta-pruning-enumeration-assimilation-20261024-*']:
    for path in sorted(Path('/tmp').glob(pattern)):
        if path.is_file() and not path.name.startswith('mcfta-pruning-enumeration-assimilation-20261024-archive-1.'):
            shutil.copyfile(path, inputs / path.name)
shutil.copytree('/tmp/mcfta-pruning-enumeration-assimilation-20261024-proposal', evidence / 'owner-proposal')
prior = evidence / 'previous-publication'
prior.mkdir()
for pin in custody:
    shutil.copyfile(area / 'previous-publication' / pin['target'], prior / pin['target'])
production = evidence / 'production-sources'
production.mkdir()
shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningEnumerationAssimilation.lean', production / 'SourcePruningEnumerationAssimilation.lean')
shutil.copyfile(root / 'lean/notes-current-pruning-enumeration-assimilation.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-assimilation-20261024-verify.py', evidence / 'verify-checkpoint.py')
(evidence / 'INDEX.md').write_text('# Checked pending-slot assimilation without conservative emptiness\n\nThe exact frozen owner and compiled public types fix the scope of finish and\npending_assimilation_complete. The selected route concerns distinct raw slots,\ntwo present pending payloads and checkEmpty=false. The checked query retains\nits actual result and native endpoint. Empty is rejected before enumeration\nwrites. A nonempty suffix writes the target, eliminates the source and then\ntransfers recursion ancestry. The canonical waiting endpoint law remains\nseparate from native IntMap/HashSet extraction and intermediate index updates.\nEnabled emptiness, omitted dispatch cases and the full caller remain separate.\n\nWork retains the complete baseline, exact declarations and source cuts,\nall actual input/report/raw failures and resource receipts. Previous-publication\nretains the immediate26 custody inputs. The older39 inputs and log-tracking\ncorrection are already sealed in the protected baseline. No old failure or\nsuccessful build count is inherited as a new result.\n\nRun verify-checkpoint.py with --root set to the repository root. It checks\nall baseline blobs and modes, nine exact document inverses, one Audit prefix,\nfrozen owner contracts, actual public axiom subsets and complete receipt sets.\nForce-add every manifest path plus SHA256SUMS, including ignored raw logs,\nbefore local publication. Publication checks manifest membership in HEAD,\nexact index/tree/file bytes and modes, singleton push URL and ordinary\nformalize destination. No future commit or successful check is assumed.\n\nNo Haskell source change is claimed. The six imported repair handoffs stay\nfirst in FINDINGS. H6 remains strongest combined. The full goal remains\nACTIVE and incomplete; this checkpoint does not prove whole-library runtime,\nsolver, enabled empty-policy, index extraction or convergence correctness.\n')

files = sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence / 'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(evidence).as_posix() + '\n' for p in files))
result = subprocess.run(['/usr/bin/python3', str(evidence / 'verify-checkpoint.py'), '--root', str(root)], cwd=root, capture_output=True)
report = dict(exit_code=result.returncode,
    manifest_sha256=hashlib.sha256((evidence / 'SHA256SUMS').read_bytes()).hexdigest(),
    manifest_entries=len(files), stdout=result.stdout.decode(), stderr=result.stderr.decode())
(area / 'seal-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
assert result.returncode == 0
