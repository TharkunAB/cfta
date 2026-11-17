from pathlib import Path
import hashlib
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
public = work.parent / '20261117-intermediate-semantics-publication'
prior = 'd0629b512854f8c1da558890668c85fb387d737e'
report = json.loads((public / 'checked.json').read_text())
assert len(report['checks']) == 5
assert all(item['exit'] == 0 and not item['nonstandard_axioms'] and not item['diagnostics']
           and not item['sorryAx'] for item in report['checks'])
sha = lambda data: hashlib.sha256(data).hexdigest()
for name, digest in json.loads((public / 'source-pins.json').read_text()).items():
    assert sha((root / name).read_bytes()) == digest, name
git = lambda *args: subprocess.check_output(['git', *args], cwd=root)
assert git('rev-parse', '--abbrev-ref', 'HEAD').decode().strip() == 'formalize'
assert git('rev-parse', 'HEAD').decode().strip() == prior
assert not git('diff', '--cached', '--name-only')
owner_name = 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
audit_name = 'lean/MicroCFTA/Audit.lean'
assert set(git('diff', '--name-only').decode().splitlines()) == {owner_name, audit_name}
specs = json.loads((public / 'selection.json').read_text())
names = ['lean/MicroCFTA/' + row[0] + '.lean' for row in specs] + [owner_name, audit_name]
assert (root / audit_name).read_bytes().split(b'\n', len(specs))[len(specs)].startswith(git('show', 'HEAD:' + audit_name))
for row in json.loads((public / 'source-transformations.json').read_text()):
    assert sha((root / 'lean/MicroCFTA' / (row['module'] + '.lean')).read_bytes()) == row['public_sha256'] == row['checked_raw_sha256']
owner = json.loads((work / 'OWNER-EXPORT-NORMAL-STAGING.json').read_text())
old_owner = git('show', 'HEAD:' + owner_name)
new_owner = (root / owner_name).read_bytes()
offset = owner.get('old_owner_offset', 0)
assert sha(old_owner) == owner['old_owner_sha256']
assert sha(new_owner) == owner['assembled_sha256']
assert new_owner[offset:offset + len(old_owner)] == old_owner
preserved = 0
for name, digest in json.loads((work / 'baseline-source-pins.json').read_text()).items():
    if name not in {owner_name, audit_name}:
        assert sha((root / name).read_bytes()) == digest, name
        preserved += 1
assert preserved == 6228
subprocess.run(['git', 'add', '-f', '--', *names], cwd=root, check=True)
assert set(git('diff', '--cached', '--name-only').decode().splitlines()) == set(names)
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=root, check=True)
subprocess.run(['git', 'commit', '--quiet', '-m',
    'Derive source marker demands and exact captured callback cuts'], cwd=root, check=True)
head = git('rev-parse', 'HEAD').decode().strip()
receipt = {'source_commit': head, 'parent': prior, 'files': names,
    'all_five_public_gates_passed': True, 'old_non_audit_non_owner_sources_byte_exact': preserved,
    'old_owner_bytes_preserved_contiguously': len(old_owner), 'old_owner_offset': offset,
    'all_old_owner_proof_bodies_and_limits_unchanged': True,
    'old_audit_bytes_after_normal_imports': True, 'new_modules': len(specs),
    'new_public_theorem_reports': report['new_public_theorems'],
    'new_private_component_reports': report.get('new_private_component_reports', 0),
    'new_declaration_reports': report['new_relation_declaration_reports'],
    'source_marker_restriction_proved': True, 'source_row_guard_and_arrow_input_proved': True,
    'same_guarded_eager_invocation_transport_proved': True,
    'selected_finalized_callback_packets_from_tuple_receipt_proved': True,
    'literal_current_cut_proved': report.get('literal_callback_current_cut_proved', False),
    'literal_held_cut_proved': report.get('literal_callback_held_cut_proved', False),
    'all_history9374_proved': False, 'joint_finite_completion_proved': False, 'haskell_changed': False}
(work / 'SOURCE-COMMIT.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt))
