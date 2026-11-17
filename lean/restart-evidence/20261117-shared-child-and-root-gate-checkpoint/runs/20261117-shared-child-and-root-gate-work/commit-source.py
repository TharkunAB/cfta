from pathlib import Path
import datetime
import hashlib
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
public = work.parent / '20261117-shared-child-and-root-gate-publication'
prior = '3400a25f3f1d302f631af6c9561bcbcb20277d85'
report = json.loads((public / 'checked.json').read_text())
assert len(report['checks']) == 5
assert all(c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics']
           and not c['sorryAx'] for c in report['checks'])
assert report['fresh_resource_component_reports'] == 3
assert report['inherited_resource_component_reports'] == 374
assert report['actual_shared_program_child_fresh_mark_birth_proved']
assert report['actual_original_raw_root_outer_empty_gate_false_proved']
sha = lambda data: hashlib.sha256(data).hexdigest()
for name, digest in json.loads((public / 'source-pins.json').read_text()).items():
    assert sha((root / name).read_bytes()) == digest, name
git = lambda *args: subprocess.check_output(['git', *args], cwd=root)
assert git('rev-parse', '--abbrev-ref', 'HEAD').decode().strip() == 'formalize'
assert git('rev-parse', 'HEAD').decode().strip() == prior
assert not git('diff', '--cached', '--name-only')
stage = json.loads((work / 'SOURCES-NORMAL-STAGING.json').read_text())
audit = 'lean/MicroCFTA/Audit.lean'
names = [c['source_path'] for c in stage['components']] + [audit]
assert set(git('diff', '--name-only').decode().splitlines()) == {audit}
for component in stage['components']:
    assert sha((root / component['source_path']).read_bytes()) == component['raw_sha256']
old_audit = git('show', 'HEAD:' + audit)
assert (root / audit).read_bytes().split(b'\n', 2)[2].startswith(old_audit)
baseline = json.loads((work / 'baseline-source-pins.json').read_text())
assert len(baseline) == 6244
assert {str(p.relative_to(root)) for p in (root / 'lean/MicroCFTA').glob('*.lean')} == set(baseline) | set(names[:-1])
preserved = 0
for name, digest in baseline.items():
    if name != audit:
        assert sha((root / name).read_bytes()) == digest, name
        preserved += 1
assert preserved == 6243
subprocess.run(['git', 'add', '-f', '--', *names], cwd=root, check=True)
assert set(git('diff', '--cached', '--name-only').decode().splitlines()) == set(names)
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=root, check=True)
subprocess.run(['git', 'commit', '--quiet', '-m',
                'Derive shared child marks and the original source emptiness gate'], cwd=root, check=True)
head = git('rev-parse', 'HEAD').decode().strip()
record = {'at': datetime.datetime.now().astimezone().isoformat(),
    'source_commit': head, 'parent': prior, 'files': names,
    'all_five_publication_gates_passed': True, 'fresh_strict_component_reports': 3,
    'inherited_strict_component_reports_bound_to_unchanged_inputs': 374,
    'old_non_audit_sources_byte_exact': preserved, 'entire_old_owner_byte_exact': True,
    'all_old_proof_bodies_and_limits_unchanged': True,
    'old_audit_bytes_after_two_normal_imports': True,
    'new_modules': 2, 'new_public_theorem_reports': 2, 'new_private_component_reports': 1,
    'first_81e3_header_exact': True, 'first_34a_to_7e1c_header_whitespace_only': True, 'same_original_five_child_runtime_fuels': True,
    'future_prefix_validity_supplier_required': False,
    'whole_history_program_mark_production_proved': False,
    'joint_finite_completion_proved': False, 'haskell_changed': False}
(work / 'SOURCE-COMMIT.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record))
