from pathlib import Path
import datetime
import hashlib
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
public = work.parent / '20261117-actual-eager-role-producer-publication'
prior = '1cd951d8db17fb030f1f382dff7177ce4ef5369b'
report = json.loads((public / 'checked.json').read_text())
assert len(report['checks']) == 5
assert all(c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics']
           and not c['sorryAx'] for c in report['checks'])
assert report['fresh_resource_component_reports'] == 265
assert report['fresh_owner_preflight_reports'] == 252
assert report['actual_publication_strict_reports'] == 13
assert report['inherited_resource_component_reports'] == 127
assert report['source_frame_joint_actual_eager_return_program_roles_proved']
assert report['actual_eager_fragment_roles_at_supplied_fuels_proved']
sha = lambda data: hashlib.sha256(data).hexdigest()
for name, digest in json.loads((public / 'source-pins.json').read_text()).items():
    assert sha((root / name).read_bytes()) == digest, name
git = lambda *args: subprocess.check_output(['git', *args], cwd=root)
assert git('rev-parse', '--abbrev-ref', 'HEAD').decode().strip() == 'formalize'
assert git('rev-parse', 'HEAD').decode().strip() == prior
assert not git('diff', '--cached', '--name-only')
stage = json.loads((work / 'SOURCES-NORMAL-STAGING.json').read_text())
owner_name = 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
audit_name = 'lean/MicroCFTA/Audit.lean'
names = [c['source_path'] for c in stage['components']] + [owner_name, audit_name]
assert set(git('diff', '--name-only').decode().splitlines()) == {owner_name, audit_name}
for component in stage['components']:
    assert sha((root / component['source_path']).read_bytes()) == component['raw_sha256']
old_owner = git('show', 'HEAD:' + owner_name)
assert old_owner == (work / 'OWNER-BEFORE.lean.txt').read_bytes()
owner = (root / owner_name).read_bytes()
assert sha(owner) == stage['owner_public_sha256']
assert owner[stage['owner_old_offset']:stage['owner_old_offset'] + len(old_owner)] == old_owner
assert len(old_owner) == 2432670
old_audit = git('show', 'HEAD:' + audit_name)
assert old_audit == (work / 'AUDIT-BEFORE.lean.txt').read_bytes()
assert (root / audit_name).read_bytes().split(b'\n', 2)[2].startswith(old_audit)
baseline = json.loads((work / 'baseline-source-pins.json').read_text())
assert len(baseline) == 6246
assert {str(p.relative_to(root)) for p in (root / 'lean/MicroCFTA').glob('*.lean')} == set(baseline) | set(names[:2])
preserved = 0
for name, digest in baseline.items():
    if name not in {audit_name, owner_name}:
        assert sha((root / name).read_bytes()) == digest, name
        preserved += 1
assert preserved == 6244
subprocess.run(['git', 'add', '-f', '--', *names], cwd=root, check=True)
assert set(git('diff', '--cached', '--name-only').decode().splitlines()) == set(names)
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=root, check=True)
subprocess.run(['git', 'commit', '--quiet', '-m',
                'Preserve Program roles at actual eager child returns'], cwd=root, check=True)
head = git('rev-parse', 'HEAD').decode().strip()
record = {'at': datetime.datetime.now().astimezone().isoformat(),
    'source_commit': head, 'parent': prior, 'files': names,
    'all_five_publication_gates_passed': True,
    'fresh_strict_component_reports_this_batch': 265,
    'fresh_owner_preflight_reports': 252, 'actual_publication_strict_reports': 13,
    'inherited_bound_component_reports': 127,
    'old_non_audit_non_owner_sources_byte_exact': preserved,
    'old_owner_contiguous_exact_bytes': len(old_owner),
    'old_owner_offset': stage['owner_old_offset'],
    'all_old_proof_bodies_and_limits_unchanged': True,
    'new_modules': 2, 'new_public_theorems': 2, 'new_private_theorems': 13,
    'same_actual_return_fragment_endpoint_indices_marks': True,
    'first_74b9_2d3_79e_d079_headers_exact': True,
    'whole_history_program_mark_production_proved': False,
    'generic_packet_only_2c6_closed': False,
    'joint_finite_completion_proved': False, 'haskell_changed': False}
(work / 'SOURCE-COMMIT.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record))
