import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-selected-row-20261024')
evidence = root / 'lean/restart-evidence/20261024-pruning-enumeration-selected-row'
assert not evidence.exists()
assert Path('/tmp/mcfta-pruning-enumeration-checked-arity-20261024-next-assessment.md').is_file()
assert Path('/tmp/mcfta-pruning-enumeration-checked-arity-20261024/post-publication-summary.json').is_file()
assert Path('/tmp/mcfta-pruning-enumeration-selected-row-20261024-source-review.md').is_file()
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert Path('/tmp/mcfta-pruning-enumeration-selected-row-20261024-' + name + '-review.md').is_file()
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
for path in sorted(Path('/tmp').glob('mcfta-pruning-enumeration-selected-row-20261024-*')):
    if path.is_file() and not path.name.startswith('mcfta-pruning-enumeration-selected-row-20261024-archive-1.'):
        shutil.copyfile(path, inputs / path.name)
shutil.copytree('/tmp/mcfta-pruning-enumeration-selected-row-20261024-proposal', evidence / 'owner-proposal')
prior = evidence / 'previous-publication'
prior.mkdir()
for stem in ['archive-1', 'local-publication-1', 'authorized-push-1']:
    for suffix in ['json', 'log', 'limits.json', 'usage.json', 'source.py', 'peaks.txt']:
        path = Path('/tmp/mcfta-pruning-enumeration-checked-arity-20261024-' + stem + '.' + suffix)
        assert path.is_file()
        shutil.copyfile(path, prior / path.name)
for name in ['seal-result.json', 'local-publication.json', 'remote-publication.json', 'push.log', 'publication-spec.json', 'post-publication-summary.json']:
    shutil.copyfile(Path('/tmp/mcfta-pruning-enumeration-checked-arity-20261024') / name, prior / name)
shutil.copyfile('/tmp/mcfta-pruning-enumeration-checked-arity-20261024-publication.py', prior / 'publication.py')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-checked-arity-20261024-next-assessment.md', prior / 'next-assessment.md')
production = evidence / 'production-sources'
production.mkdir()
shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningEnumerationSelectedRow.lean', production / 'SourcePruningEnumerationSelectedRow.lean')
shutil.copyfile(root / 'lean/notes-current-pruning-enumeration-selected-row.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-selected-row-20261024-verify.py', evidence / 'verify-checkpoint.py')
(evidence / 'INDEX.md').write_text("""# Checked row origin through native node normalization

Read current-note.md for the actual checked row, native node construction
and selected-row enumeration caller. The selected survivor retains its real
checked origin, complete constraint and projected own bounds. Node effects,
current history, closed parent and pending realization stay explicit.
The inherited arity requirement and unsupported terminal boundary remain.

Work retains the complete baseline, every actual check, public signatures,
axiom reports and resource receipts. Inputs retain independent reviews.
Owner-proposal retains literal declarations, scoped types and defining cuts.
Previous-publication retains the preceding checked-output checkpoint's26
post-seal inputs, including its already-sealed prospective assessment.
Older failures, gate history and body-layout records remain in the baseline.
Only refs/codex/turn-diffs/ is excluded from fixed-reference checks.

Run verify-checkpoint.py with --root set to the repository root. It checks
all baseline blobs and modes, exact document inverses, one Audit import,
frozen declarations, actual reports and receipts. Universal all-producer
origin, native intersection/assimilation, terminal workers, ordering,
Graph/ID/index/memo2, extraction/signed bounds, cutoff language and full
pruning/typing/driver/runtime/solver/resources/convergence remain separate.
H6 stays strongest combined. All earlier work and the optimized core remain.
FINDINGS retains all six Haskell repair handoffs first. No Haskell changes.
The whole goal stays ACTIVE and incomplete.
""")
files = sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence / 'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(evidence).as_posix() + '\n' for p in files))
result = subprocess.run(['/usr/bin/python3', str(evidence / 'verify-checkpoint.py'), '--root', str(root)], cwd=root, capture_output=True)
report = dict(exit_code=result.returncode,
    manifest_sha256=hashlib.sha256((evidence / 'SHA256SUMS').read_bytes()).hexdigest(),
    manifest_entries=len(files), stdout=result.stdout.decode(), stderr=result.stderr.decode())
(area / 'seal-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
assert result.returncode == 0
