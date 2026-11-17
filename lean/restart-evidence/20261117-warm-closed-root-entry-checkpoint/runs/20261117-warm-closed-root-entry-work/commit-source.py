from pathlib import Path
import datetime
import hashlib
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
public = work.parent / '20261117-warm-closed-root-entry-publication'
prior = '890d2ac6484b1516bfa78190673dbe1991cbef26'
sha = lambda data: hashlib.sha256(data).hexdigest()
git = lambda *args: subprocess.check_output(['git', *args], cwd=root)
report = json.loads((public / 'checked.json').read_text())
assert len(report['checks']) == 5
assert all(c['exit'] == 0 and not c['diagnostics'] and not c['nonstandard_axioms']
           and not c['sorryAx'] for c in report['checks'])
assert [c['total_axiom_reports'] for c in report['checks']] == [668, 9, 263, 668, 668]
assert report['fresh_resource_component_reports'] == 9
assert report['inherited_resource_component_reports'] == 452
assert report['fresh_owner_preflight_reports'] == 0
assert report['closed_root_physical_entry_chain_proved']
assert report['original_source_cold_closed_boundary_atoms_proved']
assert not report['joint_finite_completion_proved'] and not report['haskell_changed']
for name, digest in json.loads((public / 'source-pins.json').read_text()).items():
    assert sha((root / name).read_bytes()) == digest, name
assert git('branch', '--show-current').decode().strip() == 'formalize'
assert git('rev-parse', 'HEAD').decode().strip() == prior
assert not git('diff', '--cached', '--name-only')
stage = json.loads((work / 'SOURCES-NORMAL-STAGING.json').read_text())
components = stage['components']
assert len(components) == 7
new_name = 'lean/MicroCFTA/SourceSynthesisCurrentUniverseColdBoundaryAtoms.lean'
audit = 'lean/MicroCFTA/Audit.lean'
assert components[-1]['source_path'] == new_name
old_names = {item['source_path'] for item in components[:-1]}
assert len(old_names) == 6
names = [item['source_path'] for item in components] + [audit]
assert set(git('diff', '--name-only').decode().splitlines()) == old_names | {audit}
assert not git('ls-files', '--', new_name)
prefix_bytes = {}
for item in components:
    path = root / item['source_path']
    assert sha(path.read_bytes()) == item['raw_sha256']
    if item['source_path'] != new_name:
        old = git('show', 'HEAD:' + item['source_path'])
        assert old == (work / (item['module'] + '-BEFORE.lean.txt')).read_bytes()
        assert path.read_bytes().startswith(old)
        prefix_bytes[item['source_path']] = len(old)
old_audit = git('show', 'HEAD:' + audit)
assert old_audit == (work / 'Audit-BEFORE.lean.txt').read_bytes()
assert old_audit.count(b'#print axioms ') == 660
assert (root / audit).read_bytes() == (
    b'import MicroCFTA.SourceSynthesisCurrentUniverseColdBoundaryAtoms\n'
    + old_audit + b'\n' + (work / 'PUBLIC-PROBES.lean.txt').read_bytes())
assert (root / audit).read_bytes().count(b'#print axioms ') == 668
baseline = json.loads((work / 'baseline-source-pins.json').read_text())
assert len(baseline) == 6250
assert {str(p.relative_to(root)) for p in (root / 'lean/MicroCFTA').glob('*.lean')} == set(baseline) | {new_name}
preserved = 0
for name, digest in baseline.items():
    if name not in old_names | {audit}:
        assert sha((root / name).read_bytes()) == digest, name
        preserved += 1
assert preserved == 6243
subprocess.run(['git', 'add', '-f', '--', *names], cwd=root, check=True)
assert set(git('diff', '--cached', '--name-only').decode().splitlines()) == set(names)
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=root, check=True)
subprocess.run(['git', 'commit', '--quiet', '-m',
                'Derive warm entry facts and original source boundary atoms'], cwd=root, check=True)
record = {
    'at': datetime.datetime.now().astimezone().isoformat(),
    'source_commit': git('rev-parse', 'HEAD').decode().strip(), 'parent': prior, 'files': names,
    'all_five_publication_gates_passed': True,
    'source_files': 6251, 'audit_imports': 5251, 'audit_reports': 668,
    'independent_reports': 263, 'fresh_component_reports_this_batch': 9,
    'inherited_bound_component_reports': 452, 'combined_component_reports': 461,
    'old_reports_replaced': 0, 'fresh_owner_preflight_reports': 0,
    'inherited_owner_reports': 264,
    'old_non_audit_non_changed_owner_source_files_byte_exact': preserved,
    'six_old_owner_exact_prefix_bytes': prefix_bytes,
    'old_audit_exact_after_one_import': True,
    'all_old_proof_bodies_and_limits_unchanged': True,
    'new_modules': 1, 'new_private_theorems': 1, 'new_private_predicates': 0,
    'new_public_theorems': 8, 'original_first_header_content_preserved': True,
    'closed_root_physical_warm_entry_chain_proved': True,
    'authentic_source_cold_boundary_atoms_proved': True,
    'authentic_initial_source_heap_equality_required': True,
    'actual_execute_and_every_bounded_prefix_proved': True,
    'same_original_runtime_fuels': True, 'initial_Ready_derived_from_source_build': True,
    'external_future_OnlyU_Profile_Result_or_model_supplier': False,
    'inherited_cell_semantic_chronology_proved': False,
    'joint_finite_completion_proved': False, 'haskell_changed': False,
}
(work / 'SOURCE-COMMIT.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record))
