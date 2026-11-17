from pathlib import Path
import hashlib
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
public = work.parent / '20261117-whole-branch-nested-held-publication'
prior = 'e1890271fbe038249a89fc193d66b567c44b4489'
report = json.loads((public / 'checked.json').read_text())
assert len(report['checks']) == 5
assert report['all_visible_operation_entries_held_proved']
assert report['source_terminal_marker_native_restriction_proved']
assert all(c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics']
           and not c['sorryAx'] for c in report['checks'])
sha = lambda data: hashlib.sha256(data).hexdigest()
for name, digest in json.loads((public / 'source-pins.json').read_text()).items():
    assert sha((root / name).read_bytes()) == digest, name
git = lambda *args: subprocess.check_output(['git', *args], cwd=root)
assert git('rev-parse', '--abbrev-ref', 'HEAD').decode().strip() == 'formalize'
assert git('rev-parse', 'HEAD').decode().strip() == prior
assert not git('diff', '--cached', '--name-only')
stage = json.loads((work / 'SOURCE-NORMAL-STAGING.json').read_text())
owner_name = stage['owner_source_path']
audit_name = 'lean/MicroCFTA/Audit.lean'
predicate_name = 'lean/MicroCFTA/SourcePruningEnumerationWholeEventEntryProtection.lean'
names = [owner_name, audit_name, predicate_name, stage['marker_source_path']]
assert set(git('diff', '--name-only').decode().splitlines()) == {owner_name, audit_name}
assert sha((root / owner_name).read_bytes()) == stage['owner_public_sha256']
assert sha((root / stage['marker_source_path']).read_bytes()) == stage['marker_public_sha256']
old_audit = git('show', 'HEAD:' + audit_name)
assert (root / audit_name).read_bytes().split(b'\n', 2)[2].startswith(old_audit)
preserved = 0
for name, digest in json.loads((work / 'baseline-source-pins.json').read_text()).items():
    if name not in {audit_name, owner_name}:
        assert sha((root / name).read_bytes()) == digest, name
        preserved += 1
assert preserved == 6237
old_owner = git('show', 'HEAD:' + owner_name)
assert len(old_owner) == stage['old_owner_bytes'] == 2320102
assert sha(old_owner) == stage['old_owner_sha256']
offset = stage['old_owner_offset']
assert (root / owner_name).read_bytes()[offset:offset + len(old_owner)] == old_owner
subprocess.run(['git', 'add', '-f', '--', *names], cwd=root, check=True)
assert set(git('diff', '--cached', '--name-only').decode().splitlines()) == set(names)
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=root, check=True)
subprocess.run(['git', 'commit', '--quiet', '-m',
                'Protect every visible branch input and restrict terminal Marker domains'], cwd=root, check=True)
head = git('rev-parse', 'HEAD').decode().strip()
record = {'source_commit': head, 'parent': prior, 'files': names,
    'all_five_public_gates_passed': True, 'old_non_audit_non_owner_sources_byte_exact': preserved,
    'old_owner_bytes_preserved_contiguously': len(old_owner), 'old_owner_offset': offset,
    'all_old_proof_bodies_and_limits_unchanged': True,
    'old_audit_bytes_after_two_normal_imports': True,
    'new_modules': 2, 'new_public_theorem_reports': 3, 'new_private_component_reports': 14,
    'same_original_runtime_fuels': True, 'all_visible_operation_entries_held_proved': True,
    'source_terminal_marker_native_restriction_proved': True,
    'source_type_marker_class_consistency_proved': False,
    'joint_finite_completion_proved': False, 'haskell_changed': False}
(work / 'SOURCE-COMMIT.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record))
