from pathlib import Path
import hashlib
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
public = work.parent / '20261117-application-class-birth-publication'
prior = '2855a1f7b2664fc1677bf50a43a50d35f9442136'
report = json.loads((public / 'checked.json').read_text())
assert len(report['checks']) == 5 and report['application_class_birth_proved']
assert all(c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics']
           and not c['sorryAx'] for c in report['checks'])
assert report['fresh_resource_component_reports'] == 1
assert report['inherited_resource_component_reports'] == 365
sha = lambda data: hashlib.sha256(data).hexdigest()
for name, digest in json.loads((public / 'source-pins.json').read_text()).items():
    assert sha((root / name).read_bytes()) == digest, name
git = lambda *args: subprocess.check_output(['git', *args], cwd=root)
assert git('rev-parse', '--abbrev-ref', 'HEAD').decode().strip() == 'formalize'
assert git('rev-parse', 'HEAD').decode().strip() == prior
assert not git('diff', '--cached', '--name-only')
stage = json.loads((work / 'SOURCE-NORMAL-STAGING.json').read_text())
audit_name = 'lean/MicroCFTA/Audit.lean'
names = [stage['source_path'], audit_name]
assert set(git('diff', '--name-only').decode().splitlines()) == {audit_name}
assert sha((root / stage['source_path']).read_bytes()) == stage['public_sha256']
old_audit = git('show', 'HEAD:' + audit_name)
assert (root / audit_name).read_bytes().split(b'\n', 1)[1].startswith(old_audit)
baseline = json.loads((work / 'baseline-source-pins.json').read_text())
assert len(baseline) == 6241
assert {str(p.relative_to(root)) for p in (root / 'lean/MicroCFTA').glob('*.lean')} == set(baseline) | {stage['source_path']}
preserved = 0
for name, digest in baseline.items():
    if name != audit_name:
        assert sha((root / name).read_bytes()) == digest, name
        preserved += 1
assert preserved == 6240
subprocess.run(['git', 'add', '-f', '--', *names], cwd=root, check=True)
assert set(git('diff', '--cached', '--name-only').decode().splitlines()) == set(names)
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=root, check=True)
subprocess.run(['git', 'commit', '--quiet', '-m',
                'Derive exact equality-class births from actual source applications'], cwd=root, check=True)
head = git('rev-parse', 'HEAD').decode().strip()
record = {'source_commit': head, 'parent': prior, 'files': names,
    'all_five_publication_gates_passed': True, 'fresh_strict_component_reports': 1,
    'inherited_strict_component_reports_bound_to_unchanged_inputs': 365,
    'old_non_audit_sources_byte_exact': preserved, 'entire_old_owner_byte_exact': True,
    'all_old_proof_bodies_and_limits_unchanged': True,
    'old_audit_bytes_after_one_normal_import': True,
    'new_modules': 1, 'new_public_theorem_reports': 1, 'new_private_component_reports': 0,
    'first_0976_header_exact': True, 'same_actual_own_preparation': True,
    'same_original_runtime_fuels': True,
    'later_type_marker_compatibility_proved': False,
    'joint_finite_completion_proved': False, 'haskell_changed': False}
(work / 'SOURCE-COMMIT.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record))
