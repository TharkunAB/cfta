import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-checked-native-result-20261024')
evidence = root / 'lean/restart-evidence/20261024-pruning-enumeration-intersection-write'
assert not evidence.exists()
custody = json.loads((area / 'prior-custody-index.json').read_text())
assert len(custody) == 39 and len({pin['target'] for pin in custody}) == 39
assert hashlib.sha256((area / 'prior-custody-index.json').read_bytes()).hexdigest() == '0c4bf86bc474b55796aa6f3fe4ce2874bef6227d0e8ff8b1d07ba6f9929d175a'
summary = json.loads((area / 'previous-publication/post-publication-summary.json').read_text())
assert [pin['source'] for pin in custody] == summary['next_custody_inputs']
for pin in custody:
    assert not Path(pin['target']).is_absolute() and '..' not in Path(pin['target']).parts
    data = (area / 'previous-publication' / pin['target']).read_bytes()
    assert len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256']
assert {p.name for p in (area / 'previous-publication').iterdir()} == {pin['target'] for pin in custody}
assert Path('/tmp/mcfta-pruning-enumeration-intersection-write-20261024-source-review.md').is_file()
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert Path('/tmp/mcfta-pruning-enumeration-intersection-write-20261024-' + name + '-review.md').is_file()
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
for pattern in ['mcfta-pruning-enumeration-intersection-write-20261024-*', 'mcfta-checked-native-result-20261024-*']:
    for path in sorted(Path('/tmp').glob(pattern)):
        if path.is_file() and not path.name.startswith('mcfta-pruning-enumeration-intersection-write-20261024-archive-1.'):
            shutil.copyfile(path, inputs / path.name)
shutil.copytree('/tmp/mcfta-pruning-enumeration-intersection-write-20261024-proposal', evidence / 'owner-proposal')
prior = evidence / 'previous-publication'
prior.mkdir()
for pin in custody:
    shutil.copyfile(area / 'previous-publication' / pin['target'], prior / pin['target'])
production = evidence / 'production-sources'
production.mkdir()
shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningEnumerationIntersectionWrite.lean', production / 'SourcePruningEnumerationIntersectionWrite.lean')
shutil.copyfile(root / 'lean/notes-current-pruning-enumeration-intersection-write.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-intersection-write-20261024-verify.py', evidence / 'verify-checkpoint.py')
(evidence / 'INDEX.md').write_text('# Checked intersection result in an actual pending slot\n\nThe producer reads two actual present pending raw slots. It uses the existing\nchecked TargetQuery.finite request once. It writes the computed result handle\nat the actual target slot with source suspended parts before target parts.\nThe same returned native receipt, computed inventory and all PendingRealized\nslots remain. This is a write stage. It does not eliminate the source slot,\nupdate ancestry or waiting state, prove native cached-index extraction, or\ncomplete the terminal callback or shared enumeration driver.\n\nWork retains the exact baseline, actual source and public attempts, complete\nfailed inputs, raw logs, cap receipts and all independent reviews. A failed\nsetup is separate from a Lean attempt. Owner-proposal retains the actual\nfrozen declarations, literal contracts, scoped inventories and source cuts.\nPrevious-publication retains all39 immediate prior custody inputs, including\nboth successful local publication records and the seven log-tracking\ncorrection inputs. The earlier narrower local1 PASS remains historical.\nOnly refs/codex/turn-diffs/ is excluded from fixed-reference equality.\n\nRun verify-checkpoint.py with --root set to the repository root. It checks\nall baseline blobs and modes, nine exact document inverses, one Audit prefix,\nfrozen owner contracts, actual public axiom subsets, receipt sets and the\ncomplete manifest. Stage every manifest path and SHA256SUMS, including\nignored raw logs, before publication. The publication check requires every\nsealed path to be in the actual commit tree and keeps index, HEAD and file\ncontents and modes equal. No future commit or successful check is assumed.\n\nNo Haskell source changes. The six repair handoffs remain first in FINDINGS.\nH6 stays the strongest combined result. The full goal remains ACTIVE and\nincomplete. This producer does not establish the whole native runtime,\nsolver, resource or convergence claim.\n')

files = sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence / 'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(evidence).as_posix() + '\n' for p in files))
result = subprocess.run(['/usr/bin/python3', str(evidence / 'verify-checkpoint.py'), '--root', str(root)], cwd=root, capture_output=True)
report = dict(exit_code=result.returncode,
    manifest_sha256=hashlib.sha256((evidence / 'SHA256SUMS').read_bytes()).hexdigest(),
    manifest_entries=len(files), stdout=result.stdout.decode(), stderr=result.stderr.decode())
(area / 'seal-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
assert result.returncode == 0
