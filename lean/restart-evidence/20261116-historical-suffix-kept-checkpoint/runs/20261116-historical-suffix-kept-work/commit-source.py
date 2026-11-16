from pathlib import Path
import hashlib
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
run = root / 'lean/restart-evidence/20261116-immediate-historical-suffix-kept-publication'
report = json.loads((run / 'checked.json').read_text())
assert len(report['checks']) == 5
assert all(c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics'] and not c['sorryAx'] for c in report['checks'])
for name, digest in json.loads((run / 'source-pins.json').read_text()).items():
    assert hashlib.sha256((root / name).read_bytes()).hexdigest() == digest, name
git = lambda *args: subprocess.check_output(['git', *args], cwd=root)
assert git('rev-parse', '--abbrev-ref', 'HEAD').decode().strip() == 'formalize'
assert git('rev-parse', 'HEAD').decode().strip() == 'afff98c80ededd9f3b3003a9dcd6b1fb230c2902'
assert not git('diff', '--cached', '--name-only'), 'Preserve unrelated staged work'
names = ['lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean', 'lean/MicroCFTA/Audit.lean']
assert set(git('diff', '--name-only').decode().splitlines()) == set(names)
for name in names:
    old = git('show', 'HEAD:' + name)
    current = (root / name).read_bytes()
    if name.endswith('/Audit.lean'):
        assert current.startswith(old)
    else:
        assert current.split(b'\n', 1)[1].startswith(old)
for name, digest in json.loads((root / 'lean/restart-evidence/20261116-expanded-birth-and-actual-kept-publication/source-pins.json').read_text()).items():
    if name.startswith('lean/MicroCFTA/') and name not in names:
        assert hashlib.sha256((root / name).read_bytes()).hexdigest() == digest, name
subprocess.run(['git', 'add', '-f', '--', *names], cwd=root, check=True)
assert set(git('diff', '--cached', '--name-only').decode().splitlines()) == set(names)
subprocess.run(['git', 'commit', '--quiet', '-m', 'Prove removed-bucket dependency closure through actual parked restart'], cwd=root, check=True)
head = git('rev-parse', 'HEAD').decode().strip()
receipt = {'source_commit': head, 'parent': 'afff98c80ededd9f3b3003a9dcd6b1fb230c2902', 'files': names,
           'all_five_public_gates_passed': True, 'old_non_owner_non_audit_sources_byte_exact': 6183,
           'whole_old_owner_retained_after_one_normal_import': True,
           'whole_old_audit_retained_as_prefix': True, 'haskell_changed': False}
(work / 'SOURCE-COMMIT.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt))
