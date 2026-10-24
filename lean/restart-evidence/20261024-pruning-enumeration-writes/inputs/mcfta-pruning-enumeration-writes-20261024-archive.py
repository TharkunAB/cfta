import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-enumeration-writes-20261024')
evidence = root / 'lean/restart-evidence/20261024-pruning-enumeration-writes'
assert not evidence.exists()
plan = Path('/tmp/mcfta-pruning-enumeration-producers-20261024-plan.md')
assert plan.is_file()
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert Path('/tmp/mcfta-pruning-enumeration-writes-20261024-' + name + '-review.md').is_file()
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
for path in sorted(Path('/tmp').glob('mcfta-pruning-enumeration-writes-20261024-*')):
    if path.is_file() and not path.name.startswith('mcfta-pruning-enumeration-writes-20261024-archive-1.'):
        shutil.copyfile(path, inputs / path.name)
shutil.copytree('/tmp/mcfta-pruning-enumeration-writes-20261024-proposal', evidence / 'owner-proposal')
prior = evidence / 'previous-publication'
prior.mkdir()
for stem in ['archive-1', 'local-publication-1', 'authorized-push-1']:
    for suffix in ['json', 'log', 'limits.json', 'usage.json', 'source.py', 'peaks.txt']:
        path = Path('/tmp/mcfta-pruning-enumeration-observation-20261024-' + stem + '.' + suffix)
        assert path.is_file()
        shutil.copyfile(path, prior / path.name)
for name in ['seal-result.json', 'local-publication.json', 'remote-publication.json', 'push.log', 'publication-spec.json']:
    shutil.copyfile(Path('/tmp/mcfta-pruning-enumeration-observation-20261024') / name, prior / name)
shutil.copyfile('/tmp/mcfta-pruning-enumeration-observation-20261024-publication.py', prior / 'publication.py')
production = evidence / 'production-sources'
production.mkdir()
shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningEnumerationWrites.lean', production / 'SourcePruningEnumerationWrites.lean')
shutil.copyfile(root / 'lean/notes-current-pruning-enumeration-writes.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-enumeration-writes-20261024-verify.py', evidence / 'verify-checkpoint.py')
shutil.copyfile(plan, evidence / 'next-enumeration-producers-plan.md')
next_inputs = evidence / 'next-plan-inputs'
next_inputs.mkdir()
for path in sorted(Path('/tmp').glob('mcfta-pruning-enumeration-producers-20261024-plan*')):
    assert path.is_file()
    shutil.copyfile(path, next_inputs / path.name)
(evidence / 'INDEX.md').write_text("# Encoded enumeration-slot write evidence\n\nRead current-note.md for the exact contracts and remaining obligations.\nTwo actual modeled writes derive their handles and retain every pending-slot\ncertificate. Allocation returns the prior counter and the complete incremented state\nwith inherited ancestry.\nRaw replacement keeps the complete record update and arbitrary suspended list.\nAlignment and in-range premises make the returned/written slot explicit.\nThe native heap remains unchanged. Native cached-index correspondence is open.\n\nWork retains the complete baseline and all four compiler/build/public attempts.\nThe first strict check passes with an empty log. Both actual signatures and\nboth axiom reports remain. Each theorem uses only propext and Quot.sound.\nInputs retain full reviews and fresh capped 4 GiB/no-swap resource receipts.\nOwner-proposal retains all 42 frozen payloads and three exact STRING contracts.\nPrevious-publication retains the observation checkpoint's post-seal receipts.\nThe producer plan retains its companion freeze, original draft and correction.\nIts allocation/write proposals are now proved; native narrowing remains next.\n\nRun verify-checkpoint.py with --root set to the repository root. It checks the\nmanifest, every baseline blob/mode, nine exact document inverses, one Audit\nimport, frozen proposal/source cuts and actual source/public/raw identities.\nThe active external List API is pinned separately from project sources.\nIt does not compile or certify native index caches, extraction, intersection,\nsemantic pruning or the full driver. H6 remains the strongest combined theorem.\nEarlier proofs, counterexamples, repairs, drafts and optimized code remain.\nFINDINGS keeps its external repair index first. All six repairs are on main.\nNo Haskell source changes. The full goal remains active and incomplete.\n")
files = sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence / 'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(evidence).as_posix() + '\n' for p in files))
result = subprocess.run(['/usr/bin/python3', str(evidence / 'verify-checkpoint.py'), '--root', str(root)], cwd=root, capture_output=True)
report = dict(exit_code=result.returncode,
    manifest_sha256=hashlib.sha256((evidence / 'SHA256SUMS').read_bytes()).hexdigest(),
    manifest_entries=len(files), stdout=result.stdout.decode(), stderr=result.stderr.decode())
(area / 'seal-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
assert result.returncode == 0
