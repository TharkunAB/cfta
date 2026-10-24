import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-edge-traversal-20261024')
evidence = root / 'lean/restart-evidence/20261024-pruning-enumeration-edge-traversal'
assert not evidence.exists()
assert Path('/tmp/mcfta-pruning-enumeration-edge-prefix-20261024-next-assessment.md').is_file()
assert Path('/tmp/mcfta-pruning-enumeration-edge-prefix-20261024/post-publication-summary.json').is_file()
assert Path('/tmp/mcfta-pruning-enumeration-edge-traversal-20261024-source-review.md').is_file()
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert Path('/tmp/mcfta-pruning-enumeration-edge-traversal-20261024-' + name + '-review.md').is_file()
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
for path in sorted(Path('/tmp').glob('mcfta-pruning-enumeration-edge-traversal-20261024-*')):
    if path.is_file() and not path.name.startswith('mcfta-pruning-enumeration-edge-traversal-20261024-archive-1.'):
        shutil.copyfile(path, inputs / path.name)
shutil.copytree('/tmp/mcfta-pruning-enumeration-edge-traversal-20261024-proposal', evidence / 'owner-proposal')
prior = evidence / 'previous-publication'
prior.mkdir()
for stem in ['archive-1', 'local-publication-1', 'authorized-push-1']:
    for suffix in ['json', 'log', 'limits.json', 'usage.json', 'source.py', 'peaks.txt']:
        path = Path('/tmp/mcfta-pruning-enumeration-edge-prefix-20261024-' + stem + '.' + suffix)
        assert path.is_file()
        shutil.copyfile(path, prior / path.name)
for name in ['seal-result.json', 'local-publication.json', 'remote-publication.json', 'push.log', 'publication-spec.json', 'post-publication-summary.json']:
    shutil.copyfile(Path('/tmp/mcfta-pruning-enumeration-edge-prefix-20261024') / name, prior / name)
shutil.copyfile('/tmp/mcfta-pruning-enumeration-edge-prefix-20261024-publication.py', prior / 'publication.py')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-edge-prefix-20261024-next-assessment.md', prior / 'next-assessment.md')
production = evidence / 'production-sources'
production.mkdir()
shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningEnumerationEdgeTraversal.lean', production / 'SourcePruningEnumerationEdgeTraversal.lean')
shutil.copyfile(root / 'lean/notes-current-pruning-enumeration-edge-traversal.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-edge-traversal-20261024-verify.py', evidence / 'verify-checkpoint.py')
(evidence / 'INDEX.md').write_text("""# Ordered native edge child traversal

Read current-note.md for arity-first rejection and exact equality allocations.
The prefix retains the actual ordered children, their buckets and their
optional existing child actions. It retains the complete residual for later.
The actual projection inherits its noncomputable normalization model.
This does not establish extracted execution or native containers.

Work retains the full baseline, actual strict attempts, complete public types,
axiom reports and resource receipts. Inputs retain independent reviews.
Owner-proposal retains literal declarations, scoped types and defining cuts.
Previous-publication retains the prior constraint checkpoint's26 actual
inputs, including its prospective assessment and post-publication summary.

Run verify-checkpoint.py with --root set to the repository root. It checks
the complete manifest, every baseline blob/mode, nine exact document inverses,
one Audit import, frozen declarations, actual reports and resource receipts.
Child execution, terminal merging, own-path arity, residual insertion and
the default canonical and
weighted selector, native graph/ID/index/memo2, typing/pruning, full driver,
resources, practical width, runtime/solver and convergence remain open.
H6 stays strongest combined. All earlier work and the optimized core remain.
FINDINGS retains the six Haskell repair handoffs first. No Haskell changes.
The full formalization goal remains ACTIVE and incomplete.
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
