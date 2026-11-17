from pathlib import Path
import hashlib
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
public = work.parent / '20261117-nested-held-entry-publication'
prior = '21c39dee2d27c5a5cd4ab4166864325e2a1a1e88'
report = json.loads((public / 'checked.json').read_text())
assert len(report['checks']) == 5
assert report['actual_captured_invocation_nested_input_protection_proved']
assert report['closed_c316_original_budget_proved']
assert all(c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics']
           and not c['sorryAx'] for c in report['checks'])
sha = lambda data: hashlib.sha256(data).hexdigest()
for name, digest in json.loads((public / 'source-pins.json').read_text()).items():
    assert sha((root / name).read_bytes()) == digest, name
git = lambda *args: subprocess.check_output(['git', *args], cwd=root)
assert git('rev-parse', '--abbrev-ref', 'HEAD').decode().strip() == 'formalize'
assert git('rev-parse', 'HEAD').decode().strip() == prior
assert not git('diff', '--cached', '--name-only')
selection = json.loads((public / 'selection.json').read_text())
guard, owner = selection['guard'], selection['owner']
audit_name = 'lean/MicroCFTA/Audit.lean'
assert set(git('diff', '--name-only').decode().splitlines()) == {owner['source_path'], audit_name}
names = [guard['source_path'], owner['source_path'], audit_name]
for spec in [guard, owner]:
    assert sha((root / spec['source_path']).read_bytes()) == spec['public_sha256']
assert (root / audit_name).read_bytes().split(b'\n', 1)[1].startswith(git('show', 'HEAD:' + audit_name))
preserved = 0
for name, digest in json.loads((work / 'baseline-source-pins.json').read_text()).items():
    if name not in {audit_name, owner['source_path']}:
        assert sha((root / name).read_bytes()) == digest, name
        preserved += 1
assert preserved == 6236
old_owner = git('show', 'HEAD:' + owner['source_path'])
assert len(old_owner) == owner['old_owner_bytes'] == 2222363
assert sha(old_owner) == owner['old_owner_sha256']
offset = owner['old_owner_offset']
assert (root / owner['source_path']).read_bytes()[offset:offset + len(old_owner)] == old_owner
subprocess.run(['git', 'add', '-f', '--', *names], cwd=root, check=True)
assert set(git('diff', '--cached', '--name-only').decode().splitlines()) == set(names)
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=root, check=True)
subprocess.run(['git', 'commit', '--quiet', '-m',
                'Protect nested operation entries in actual captured invocations'], cwd=root, check=True)
head = git('rev-parse', 'HEAD').decode().strip()
record = {'source_commit': head, 'parent': prior, 'files': names,
    'all_five_public_gates_passed': True, 'old_non_audit_non_owner_sources_byte_exact': preserved,
    'old_owner_bytes_preserved_contiguously': len(old_owner), 'old_owner_offset': offset,
    'all_old_proof_bodies_and_limits_unchanged': True,
    'old_audit_bytes_after_one_normal_import': True,
    'new_modules': 1, 'new_public_theorem_reports': 2, 'new_private_component_reports': 10,
    'original_c316_theorem_declaration_byte_exact': True,
    'original_fca_theorem_declaration_byte_exact': True,
    'new_phase_predicate_unused_binder_alpha_renames': 3,
    'same_original_runtime_fuels': True,
    'actual_captured_invocation_nested_input_protection_proved': True,
    'whole_worker_joint_nested_protection_proved': False,
    'joint_finite_completion_proved': False, 'haskell_changed': False}
(work / 'SOURCE-COMMIT.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record))
