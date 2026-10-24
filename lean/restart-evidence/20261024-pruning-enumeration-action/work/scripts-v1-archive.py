import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-action-20261024')
evidence = root / 'lean/restart-evidence/20261024-pruning-enumeration-action'
assert not evidence.exists()
assert (area / 'source-plan/plan.md').is_file()
assert (area / 'result-payload-addendum/addendum.md').is_file()
assert (area / 'source-plan-review.md').is_file()
assert (area / 'result-payload-review.md').is_file()
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert Path('/tmp/mcfta-pruning-enumeration-action-20261024-' + name + '-review.md').is_file()
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
for path in sorted(Path('/tmp').glob('mcfta-pruning-enumeration-action-20261024-*')):
    if path.is_file() and not path.name.startswith('mcfta-pruning-enumeration-action-20261024-archive-1.'):
        shutil.copyfile(path, inputs / path.name)
shutil.copytree('/tmp/mcfta-pruning-enumeration-action-20261024-proposal', evidence / 'owner-proposal')
prior = evidence / 'previous-publication'
prior.mkdir()
for stem in ['archive-1', 'local-publication-1', 'authorized-push-1']:
    for suffix in ['json', 'log', 'limits.json', 'usage.json', 'source.py', 'peaks.txt']:
        path = Path('/tmp/mcfta-pruning-enumeration-outer-20261024-' + stem + '.' + suffix)
        assert path.is_file()
        shutil.copyfile(path, prior / path.name)
for name in ['seal-result.json', 'local-publication.json', 'remote-publication.json', 'push.log', 'publication-spec.json']:
    shutil.copyfile(Path('/tmp/mcfta-pruning-enumeration-outer-20261024') / name, prior / name)
shutil.copyfile('/tmp/mcfta-pruning-enumeration-outer-20261024-publication.py', prior / 'publication.py')
production = evidence / 'production-sources'
production.mkdir()
shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningEnumerationAction.lean', production / 'SourcePruningEnumerationAction.lean')
shutil.copyfile(root / 'lean/notes-current-pruning-enumeration-action.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-action-20261024-verify.py', evidence / 'verify-checkpoint.py')
(evidence / 'INDEX.md').write_text("""# Executable outer narrowing and enumeration actions

Read current-note.md for the actual pending observation and prepare result.
The existing native Result retains the actual Value, heap and optional action.
Empty rejects first. Equal handles retain the actual entry state.
Changed handles retain the same second representative read and final write.

Work retains the complete baseline, source plan, raw attempts, public types
and axiom reports. The original source plan and separate payload correction
remain with both reviews. Inputs retain independent reviews and capped receipts.
Owner-proposal retains every frozen header, scoped type and defining cut.
Previous-publication retains the outer pending checkpoint's post-seal inputs.

Run verify-checkpoint.py with --root set to the repository root. It checks the
complete manifest, every baseline blob/mode, nine exact document inverses,
one Audit import, frozen declarations, actual reports and resource receipts.
Concrete typing/key laws, native IDs/indices/memo2, the pure-graph/native-heap
bridge, full driver language preservation, resources, extraction/runtime/
solver correspondence and convergence remain open. H6 stays strongest combined.
Earlier proofs, counterexamples, repairs, drafts and optimized code remain.
FINDINGS retains all six Haskell repair handoffs first. No Haskell changes.
The full goal remains ACTIVE and incomplete.
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
