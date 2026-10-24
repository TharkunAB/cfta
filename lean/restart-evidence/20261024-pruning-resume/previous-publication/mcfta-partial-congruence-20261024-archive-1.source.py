import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-partial-congruence-20261024')
evidence = root / 'lean/restart-evidence/20261024-partial-congruence'
assert not evidence.exists()
assert (area / 'final-document-review.md').is_file()
assert (area / 'final-public-review.md').is_file()
assert Path('/tmp/mcfta-partial-congruence-20261024-callback-inventory.md').is_file()
evidence.mkdir()
for path in sorted(area.rglob('*')):
    if not path.is_file():
        continue
    relative = path.relative_to(area)
    target = evidence / 'work' / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    if path.name == 'baseline-tree.txt':
        target.with_suffix('.txt.gz').write_bytes(gzip.compress(path.read_bytes(), mtime=0))
    else:
        target.write_bytes(path.read_bytes())
inputs = evidence / 'inputs'
inputs.mkdir()
for path in sorted(Path('/tmp').glob('mcfta-partial-congruence-20261024-*')):
    if path.is_file() and not path.name.startswith('mcfta-partial-congruence-20261024-archive-1.'):
        shutil.copyfile(path, inputs / path.name)
prior = evidence / 'previous-publication'
prior.mkdir()
for stem in ['archive-1', 'local-publication-1', 'authorized-push-1']:
    for suffix in ['json', 'log', 'limits.json', 'usage.json', 'source.py', 'peaks.txt']:
        path = Path('/tmp/mcfta-observer-frame-20261024-' + stem + '.' + suffix)
        assert path.is_file(), path
        shutil.copyfile(path, prior / path.name)
for name in ['seal-result.json', 'local-publication.json', 'remote-publication.json', 'push.log']:
    shutil.copyfile(Path('/tmp/mcfta-observer-frame-20261024') / name, prior / name)
shutil.copyfile('/tmp/mcfta-observer-frame-20261024-publication.py', prior / 'publication.py')
production = evidence / 'production-sources'
production.mkdir()
for name in ['EnumerationRootObservation', 'EnumerationPartialCongruence', 'EnumerationPartialTransport', 'EnumerationPartialRoot']:
    shutil.copyfile(root / 'lean/MicroCFTA' / (name + '.lean'), production / (name + '.lean'))
shutil.copyfile(root / 'lean/notes-current-partial-congruence.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-partial-congruence-20261024-verify.py', evidence / 'verify-checkpoint.py')
(evidence / 'INDEX.md').write_text('''# Partial observation congruence checkpoint

The current note states the exact claims and remaining proof obligations.
Main was fetched and already incorporated. No new Haskell repair is claimed.
Work retains all eleven Lean attempts, including all three failed attempts.
Inputs retain original candidates and the verified cap receipts.
Production sources are the exact final strict-checked inputs.
Previous publication retains the preceding checkpoint's post-seal receipts.

Run verify-checkpoint.py with --root set to the repository root.
The verifier checks hashes, exact baseline preservation, the new sources,
public signatures, axiom sets and actual check reports. It does not compile.
All earlier proof bodies, drafts, counterexamples and sealed evidence remain.
The complete formalization goal is active and incomplete.
''')
files = sorted(path for path in evidence.rglob('*') if path.is_file())
(evidence / 'SHA256SUMS').write_text(''.join(
    hashlib.sha256(path.read_bytes()).hexdigest() + '  ' + path.relative_to(evidence).as_posix() + '\n'
    for path in files))
result = subprocess.run(['/usr/bin/python3', str(evidence / 'verify-checkpoint.py'), '--root', str(root)],
                        cwd=root, capture_output=True)
(area / 'seal-result.json').write_text(json.dumps({
    'exit_code': result.returncode,
    'manifest_sha256': hashlib.sha256((evidence / 'SHA256SUMS').read_bytes()).hexdigest(),
    'manifest_entries': len(files), 'stdout': result.stdout.decode(), 'stderr': result.stderr.decode(),
}, indent=2) + '\n')
print(result.stdout.decode(), end='')
print(result.stderr.decode(), end='')
assert result.returncode == 0
print((area / 'seal-result.json').read_text())
