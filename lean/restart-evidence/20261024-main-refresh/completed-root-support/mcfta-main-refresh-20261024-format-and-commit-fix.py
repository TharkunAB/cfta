import hashlib
import json
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
out = Path('/tmp/mcfta-main-refresh-20261024')
merge = json.loads((out / 'merge-report.json').read_text())
changed = merge['upstream_changed_paths']
hs = [name for name in changed if name.endswith('.hs')]
cabal = [name for name in changed if name.endswith('.cabal')]
log = out / 'format.log'
with log.open('xb') as output:
    for command in [['fourmolu', '--mode', 'check', *hs], ['cabal-gild', '--mode', 'check', *cabal]]:
        output.write((json.dumps(command) + '\n').encode())
        output.flush()
        result = subprocess.run(command, cwd=root, stdout=output, stderr=subprocess.STDOUT)
        assert result.returncode == 0, log.read_text()[-12000:]
sources = {'specftacular/src/Specftacular.hs': 'b5a19e8c83908ff2de3cf3ee704731733224d96f36b7fb597afcd0fa017dbace',
           'specftacular/src/Specftacular/Utils.hs': '2737df7df4bce7178e45c96db3bf550a0ce4c2d7d57ed131e2689071ec2e53ec'}
for name, digest in sources.items():
    assert hashlib.sha256((root / name).read_bytes()).hexdigest() == digest
native = (out / 'pending-probes-v2.log').read_text()
for label in ['PASS: parser rejects', 'PASS: grammar rejects', 'PASS: public search rejects',
              'PASS: phase 4 runs', 'PASS: serial, parallel and enumerate-ahead']:
    assert label in native
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip() == merge['merge']
assert set(subprocess.check_output(['git', 'diff', '--name-only'], cwd=root, text=True).splitlines()) == set(sources)
assert not subprocess.check_output(['git', 'diff', '--cached', '--name-only'], cwd=root)
subprocess.run(['git', 'add', '--', *sources], cwd=root, check=True)
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=root, check=True)
subprocess.run(['git', 'commit', '--quiet', '-m', 'Reject negative type-depth bounds before grammar construction'], cwd=root, check=True)
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip()
report = dict(status='PASS', commit=head, parent=merge['merge'], sources=sources,
              formatted_Haskell_paths=len(hs), formatted_Cabal_paths=len(cabal),
              three_negative_entry_checks_passed=True, depth_zero_passed=True,
              small_phase_four_modes_passed=True, independent_source_review='programs-review.md',
              new_committed_tests=0)
(out / 'type-depth-fix-report.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
