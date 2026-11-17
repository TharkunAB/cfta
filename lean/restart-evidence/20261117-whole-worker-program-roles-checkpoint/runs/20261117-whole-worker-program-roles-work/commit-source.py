from pathlib import Path
import datetime
import hashlib
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
public = work.parent / '20261117-whole-worker-program-roles-publication'
prior = 'a0e968a176e23825baaeb4f2180d470d8c7c1c33'
report = json.loads((public / 'checked.json').read_text())
assert len(report['checks']) == 5
assert all(c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics']
           and not c['sorryAx'] for c in report['checks'])
assert report['whole_worker_program_slots_fixed_marks_proved']
assert report['fresh_resource_component_reports'] == 278
assert report['fresh_owner_preflight_reports'] == 264
assert report['actual_publication_strict_reports'] == 14
assert report['inherited_resource_component_reports'] == 127
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
fragment_name = 'lean/MicroCFTA/SourceSynthesisActualEagerProgramFragmentRoles.lean'
names = [owner_name, fragment_name, audit_name]
assert set(git('diff', '--name-only').decode().splitlines()) == set(names)
old_owner = git('show', 'HEAD:' + owner_name)
old_fragment = git('show', 'HEAD:' + fragment_name)
old_audit = git('show', 'HEAD:' + audit_name)
assert old_owner == (work / 'OWNER-BEFORE.lean.txt').read_bytes()
assert old_fragment == (work / 'SourceSynthesisActualEagerProgramFragmentRoles-BEFORE.lean.txt').read_bytes()
assert old_audit == (work / 'Audit-BEFORE.lean.txt').read_bytes()
owner = (root / owner_name).read_bytes()
fragment = (root / fragment_name).read_bytes()
audit = (root / audit_name).read_bytes()
assert sha(owner) == stage['owner_raw_sha256']
offset = stage['owner_base_offset']
assert offset == 113 and len(old_owner) == 2446450
assert owner[offset:offset + len(old_owner)] == old_owner
assert fragment.startswith(old_fragment) and len(old_fragment) == 32048
assert audit.startswith(old_audit) and audit.count(b'#print axioms ') == 656
assert (work.parent / '20261117-whole-real-eager-program-slots-outer-assembly-draft/PUBLIC-HEADER.lean.txt').read_bytes() in owner
assert (work.parent / '20261117-selected-eager-program-fragment-roles-draft/PUBLIC-HEADER.lean.txt').read_bytes() in fragment
baseline = json.loads((work / 'baseline-source-pins.json').read_text())
assert len(baseline) == 6248
assert {str(p.relative_to(root)) for p in (root / 'lean/MicroCFTA').glob('*.lean')} == set(baseline)
preserved = 0
for name, digest in baseline.items():
    if name not in set(names):
        assert sha((root / name).read_bytes()) == digest, name
        preserved += 1
assert preserved == 6245
subprocess.run(['git', 'add', '-f', '--', *names], cwd=root, check=True)
assert set(git('diff', '--cached', '--name-only').decode().splitlines()) == set(names)
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=root, check=True)
subprocess.run(['git', 'commit', '--quiet', '-m',
                'Preserve Program marks through every real worker output'], cwd=root, check=True)
head = git('rev-parse', 'HEAD').decode().strip()
record = {'at': datetime.datetime.now().astimezone().isoformat(),
    'source_commit': head, 'parent': prior, 'files': names,
    'all_five_publication_gates_passed': True,
    'fresh_component_reports_this_batch': 278, 'fresh_owner_preflight_reports': 264,
    'actual_publication_strict_reports': 14, 'inherited_bound_component_reports': 127,
    'old_non_audit_non_owner_non_fragment_sources_byte_exact': preserved,
    'old_owner_contiguous_exact_bytes': len(old_owner), 'old_owner_offset': offset,
    'old_fragment_exact_prefix_bytes': len(old_fragment),
    'all_old_proof_bodies_and_limits_unchanged': True,
    'new_modules': 0, 'new_public_theorems': 2, 'new_private_theorems': 11,
    'new_private_predicates': 1, 'original_02a2_and_681a_declarations_exact': True,
    'whole_worker_fixed_program_marks_preserved': True,
    'every_emitted_output_before_later_stops_covered': True,
    'same_original_fuels_and_marks': True, 'external_future_history_or_role_supplier': False,
    'native363_and_reader_export_staged': False, 'generic_packet_only_2c6_closed': False,
    'joint_finite_completion_proved': False, 'haskell_changed': False}
(work / 'SOURCE-COMMIT.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record))
