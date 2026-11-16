from pathlib import Path
import hashlib
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
run = root / 'lean/restart-evidence/20261116-real-eager-callback-output-block-publication'
report = json.loads((run / 'checked.json').read_text())
assert len(report['checks']) == 5
assert all(c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics'] and not c['sorryAx'] for c in report['checks'])
for name, digest in json.loads((run / 'source-pins.json').read_text()).items():
    assert hashlib.sha256((root / name).read_bytes()).hexdigest() == digest, name
git = lambda *args: subprocess.check_output(['git', *args], cwd=root)
assert git('rev-parse', '--abbrev-ref', 'HEAD').decode().strip() == 'formalize'
assert git('rev-parse', 'HEAD').decode().strip() == 'b7970c9bd553027e8d43c2e62e55e4b41763921a'
assert not git('diff', '--cached', '--name-only')
assert set(git('diff', '--name-only').decode().splitlines()) == {'lean/MicroCFTA/Audit.lean'}
specs = json.loads((run / 'selection.json').read_text())
names = ['lean/MicroCFTA/' + row[0] + '.lean' for row in specs] + ['lean/MicroCFTA/Audit.lean']
assert (root / names[-1]).read_bytes().split(b'\n', 5)[5].startswith(git('show', 'HEAD:' + names[-1]))
for row in json.loads((run / 'source-transformations.json').read_text()):
    raw = (root / 'lean/MicroCFTA' / (row['module'] + '.lean')).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == row['public_sha256']
    if row['annotation_only']:
        raw = raw.replace(row['annotation'].encode(), b'', 1)
    assert hashlib.sha256(raw).hexdigest() == row['checked_raw_sha256']
old = root / 'lean/restart-evidence/20261116-immediate-historical-suffix-kept-publication/source-pins.json'
preserved = 0
for name, digest in json.loads(old.read_text()).items():
    if name.startswith('lean/MicroCFTA/') and name != 'lean/MicroCFTA/Audit.lean':
        assert hashlib.sha256((root / name).read_bytes()).hexdigest() == digest, name
        preserved += 1
assert preserved == 6184
subprocess.run(['git', 'add', '-f', '--', *names], cwd=root, check=True)
assert set(git('diff', '--cached', '--name-only').decode().splitlines()) == set(names)
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=root, check=True)
subprocess.run(['git', 'commit', '--quiet', '-m', 'Prove real eager callback output-block origins'], cwd=root, check=True)
head = git('rev-parse', 'HEAD').decode().strip()
receipt = {'source_commit': head, 'parent': 'b7970c9bd553027e8d43c2e62e55e4b41763921a', 'files': names,
           'all_five_public_gates_passed': True, 'old_non_audit_source_files_byte_exact': preserved,
           'old_owner_byte_exact': True, 'old_audit_bytes_after_five_normal_imports': True,
           'indexed_executed_invocation_trace_proved': False, 'joint_finite_completion_proved': False,
           'haskell_changed': False}
(work / 'SOURCE-COMMIT.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt))
