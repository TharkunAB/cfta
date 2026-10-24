import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-native-view-20261024')
evidence = root / 'lean/restart-evidence/20261024-pruning-native-view'
assert not evidence.exists()
plan = Path('/tmp/mcfta-pruning-enumeration-bridge-20261024-plan.md')
assert plan.is_file()
caveat = Path('/tmp/mcfta-pruning-enumeration-bridge-20261024-laziness-caveat.md')
assert caveat.is_file()
for args in [('diff', '--quiet'), ('diff', '--cached', '--quiet')]:
    subprocess.run(['git', *args], cwd=root, check=True)
for name in ['declaration', 'model', 'public', 'document', 'seal-script', 'root']:
    assert Path('/tmp/mcfta-pruning-native-view-20261024-' + name + '-review.md').is_file()
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
for path in sorted(Path('/tmp').glob('mcfta-pruning-native-view-20261024-*')):
    if path.is_file() and not path.name.startswith('mcfta-pruning-native-view-20261024-archive-1.'):
        shutil.copyfile(path, inputs / path.name)
shutil.copytree('/tmp/mcfta-pruning-native-view-20261024-proposal', evidence / 'owner-proposal')
prior = evidence / 'previous-publication'
prior.mkdir()
for stem in ['archive-1', 'local-publication-1', 'authorized-push-1']:
    for suffix in ['json', 'log', 'limits.json', 'usage.json', 'source.py', 'peaks.txt']:
        path = Path('/tmp/mcfta-th-repair-main-20261024-' + stem + '.' + suffix)
        assert path.is_file()
        shutil.copyfile(path, prior / path.name)
for name in ['seal-result.json', 'local-publication.json', 'remote-publication.json', 'push.log', 'publication-spec.json']:
    shutil.copyfile(Path('/tmp/mcfta-th-repair-main-20261024') / name, prior / name)
shutil.copyfile('/tmp/mcfta-th-repair-main-20261024-publication.py', prior / 'publication.py')
production = evidence / 'production-sources'
production.mkdir()
shutil.copyfile(root / 'lean/MicroCFTA/SourcePruningNativeView.lean', production / 'SourcePruningNativeView.lean')
shutil.copyfile(root / 'lean/notes-current-pruning-native-view.md', evidence / 'current-note.md')
shutil.copyfile('/tmp/mcfta-pruning-native-view-20261024-verify.py', evidence / 'verify-checkpoint.py')
shutil.copyfile(plan, evidence / 'next-enumeration-bridge-plan.md')
shutil.copyfile(caveat, evidence / 'next-enumeration-bridge-laziness-caveat.md')
(evidence / 'INDEX.md').write_text('''# Actual interned-node narrowing evidence

Read current-note.md for the exact source contracts and remaining obligations.
The concrete filter, repaired reader and smart constructor derive narrowing,
retained cache validity/history, exact normalized rows and literal emptiness.
The non-Mu wrapper performs the actual second read. Mu alone bypasses the read.
This does not prove semantic pruning, full typedTypes or Haskell extraction.

Work retains the complete baseline and all eight compiler/build/public attempts.
Two failed source attempts retain the local-let and linter diagnostics.
The first public readback retains its unsupported display-option failure.
The successful retry removes only that display line. Final strict logs are empty.
Inputs retain complete reviews, exact commands, fresh allowance and capped
4 GiB/no-swap receipts. Owner-proposal retains all75 frozen payload files.
The original five-name gate and separate additive completion gate both remain.
Previous-publication retains the prior checkpoint's post-seal receipts.
The next plan identifies the enumeration-handle and canonical-cache bridge.
Its separate caveat retains lazy Boolean demand in the later callback trace.

Run verify-checkpoint.py with --root set to the repository root. It checks the
manifest, every baseline blob/mode, nine exact document inverses, one Audit
import, frozen proposal/source cuts and actual source/public/raw identities.
It does not compile or prove native extraction, canonicality or semantic pruning.
Earlier proofs, counterexamples, repairs, drafts and optimized interned code remain.
FINDINGS keeps the complete external Haskell repair index first. All six repairs
are on main. No Haskell source changes. The full goal remains active and incomplete.
''')
files = sorted(p for p in evidence.rglob('*') if p.is_file())
(evidence / 'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(evidence).as_posix() + '\n' for p in files))
result = subprocess.run(['/usr/bin/python3', str(evidence / 'verify-checkpoint.py'), '--root', str(root)], cwd=root, capture_output=True)
report = dict(exit_code=result.returncode,
    manifest_sha256=hashlib.sha256((evidence / 'SHA256SUMS').read_bytes()).hexdigest(),
    manifest_entries=len(files), stdout=result.stdout.decode(), stderr=result.stderr.decode())
(area / 'seal-result.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
assert result.returncode == 0
