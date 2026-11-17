from pathlib import Path
import hashlib
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
public = work.parent / '20261117-joint-held-ledger-publication'
prior = 'db9c0d09b42d5680819f8b5aa6bfc6f310bbffbb'
report = json.loads((public / 'checked.json').read_text())
assert len(report['checks']) == 5 and report['joint_held_event_history_proved']
assert all(c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics']
           and not c['sorryAx'] for c in report['checks'])
sha = lambda data: hashlib.sha256(data).hexdigest()
for name, digest in json.loads((public / 'source-pins.json').read_text()).items():
    assert sha((root / name).read_bytes()) == digest, name
git = lambda *args: subprocess.check_output(['git', *args], cwd=root)
assert git('rev-parse', '--abbrev-ref', 'HEAD').decode().strip() == 'formalize'
assert git('rev-parse', 'HEAD').decode().strip() == prior
assert not git('diff', '--cached', '--name-only')
audit_name = 'lean/MicroCFTA/Audit.lean'
assert git('diff', '--name-only').decode().splitlines() == [audit_name]
specs = json.loads((public / 'selection.json').read_text())
names = [spec['source_path'] for spec in specs] + [audit_name]
assert len(names) == 3
for spec in specs:
    assert sha((root / spec['source_path']).read_bytes()) == spec['public_sha256']
assert (root / audit_name).read_bytes().split(b'\n', 2)[2].startswith(git('show', 'HEAD:' + audit_name))
preserved = 0
for name, digest in json.loads((work / 'baseline-source-pins.json').read_text()).items():
    if name != audit_name:
        assert sha((root / name).read_bytes()) == digest, name
        preserved += 1
assert preserved == 6235
subprocess.run(['git', 'add', '-f', '--', *names], cwd=root, check=True)
assert set(git('diff', '--cached', '--name-only').decode().splitlines()) == set(names)
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=root, check=True)
subprocess.run(['git', 'commit', '--quiet', '-m',
                'Join causal event ledgers with outer entry protection'], cwd=root, check=True)
head = git('rev-parse', 'HEAD').decode().strip()
record = {'source_commit': head, 'parent': prior, 'files': names,
    'all_five_public_gates_passed': True, 'old_non_audit_sources_byte_exact': preserved,
    'entire_previous_resource_owner_byte_exact': True, 'old_owner_bytes': 2222363,
    'all_old_proof_bodies_and_limits_unchanged': True, 'old_audit_bytes_after_two_normal_imports': True,
    'new_modules': 2, 'new_public_theorem_reports': 3, 'new_private_component_reports': 9,
    'worker_a3c_theorem_declaration_byte_exact': True, 'core_shared_predicate_and_headers_byte_exact': True,
    'worker_historical_open_comment_removed': True, 'same_original_runtime_fuels': True,
    'joint_held_event_history_proved': True, 'nested_cut_protection_proved': False,
    'joint_finite_completion_proved': False, 'haskell_changed': False}
(work / 'SOURCE-COMMIT.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record))
