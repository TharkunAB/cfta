import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-reread-20261024')
evidence = root / 'lean/restart-evidence/20261024-pruning-enumeration-reread'
assert not evidence.exists()
assert (area / 'narrowing-plan/plan.md').is_file()
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
for name in ['declaration', 'model', 'repair', 'public', 'document', 'seal-script', 'root']:
    assert Path('/tmp/mcfta-pruning-enumeration-reread-20261024-' + name + '-review.md').is_file()
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
for path in sorted(Path('/tmp').glob('mcfta-pruning-enumeration-reread-20261024-*')):
    if path.is_file() and not path.name.startswith('mcfta-pruning-enumeration-reread-20261024-archive-1.'):
        shutil.copyfile(path, inputs / path.name)
shutil.copytree('/tmp/mcfta-pruning-enumeration-reread-20261024-proposal', evidence / 'owner-proposal')
prior = evidence / 'previous-publication'
prior.mkdir()
for stem in ['archive-1', 'local-publication-1', 'authorized-push-1']:
    for suffix in ['json', 'log', 'limits.json', 'usage.json', 'source.py', 'peaks.txt']:
        path = Path('/tmp/mcfta-pruning-enumeration-identity-20261024-' + stem + '.' + suffix)
        assert path.is_file()
        shutil.copyfile(path, prior / path.name)
for name in ['seal-result.json', 'local-publication.json', 'remote-publication.json', 'push.log', 'publication-spec.json']:
    shutil.copyfile(Path('/tmp/mcfta-pruning-enumeration-identity-20261024') / name, prior / name)
shutil.copyfile('/tmp/mcfta-pruning-enumeration-identity-20261024-publication.py', prior / 'publication.py')
production = evidence / 'production-sources'
production.mkdir()
shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningEnumerationReread.lean', production / 'SourcePruningEnumerationReread.lean')
shutil.copyfile(root / 'lean/notes-current-pruning-enumeration-reread.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-reread-20261024-verify.py', evidence / 'verify-checkpoint.py')
(evidence / 'INDEX.md').write_text("""# Actual pending-node representative reread evidence

Read current-note.md for the exact contracts and remaining obligations.
An actual pending slot read and an intervening complete frame derive a finite
actual representative reread at the same root. Its actual compressed state,
full frames, exact pending slot, ordered suspended list and slot bound remain.
An observed false recursion check also retains the complete frame.

Work retains the complete baseline, raw compiler/build/public attempts, actual
signatures and axiom reports. Inputs retain full independent reviews and fresh
capped 4 GiB/no-swap resource receipts. Owner-proposal retains every frozen
payload and exact declaration contract, including the prefreeze correction.
Previous-publication retains the identity checkpoint's post-seal receipts.
Work/narrowing-plan retains both source-only consumer assessments and sources.

Run verify-checkpoint.py with --root set to the repository root. It checks the
manifest, every baseline blob/mode, nine exact document inverses, one Audit
import, frozen proposal/source cuts and actual source/public/raw identities.
It does not compile or certify the coupled native narrowing and changed write,
native index caches, extraction, semantic pruning or the complete driver.
H6 remains the strongest combined theorem. Earlier proofs, counterexamples,
repairs, drafts and optimized code remain. FINDINGS keeps its external repair
index first. All six fixes are on main. No Haskell source changes.
The full goal remains active and incomplete.
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
