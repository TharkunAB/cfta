from pathlib import Path
import datetime
import hashlib
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
public = work.parent / '20261117-original-optional-no-new-mu-publication'
prior = 'b8f734b528e7fadee83e47bb90625bcd9519553a'
sha = lambda data: hashlib.sha256(data).hexdigest()
git = lambda *args: subprocess.check_output(['git', *args], cwd=root)
report = json.loads((public / 'checked.json').read_text())
assert len(report['checks']) == 5
assert all(c['exit'] == 0 and not c['diagnostics'] and not c['nonstandard_axioms']
           and not c['sorryAx'] for c in report['checks'])
assert [c['total_axiom_reports'] for c in report['checks']] == [660, 46, 255, 660, 660]
assert report['fresh_resource_component_reports'] == 46
assert report['inherited_resource_component_reports'] == 406
assert report['fresh_owner_preflight_reports'] == 0
assert report['optional441e_proved'] and report['cold_whole_query_no_new_mu_proved']
assert report['cold_every_bounded_trace_prefix_no_new_mu_proved']
assert not report['joint_finite_completion_proved'] and not report['haskell_changed']
for name, digest in json.loads((public / 'source-pins.json').read_text()).items():
    assert sha((root / name).read_bytes()) == digest, name
assert git('branch', '--show-current').decode().strip() == 'formalize'
assert git('rev-parse', 'HEAD').decode().strip() == prior
assert not git('diff', '--cached', '--name-only')
stage = json.loads((work / 'SOURCES-NORMAL-STAGING.json').read_text())
native = 'lean/MicroCFTA/SourceSynthesisCurrentUniverseNativeAllocation.lean'
cold = 'lean/MicroCFTA/SourceSynthesisCurrentUniverseColdNoNewMu.lean'
audit = 'lean/MicroCFTA/Audit.lean'
names = [native, cold, audit]
assert set(git('diff', '--name-only').decode().splitlines()) == {native, audit}
assert not git('ls-files', '--', cold)
old_native = git('show', 'HEAD:' + native)
old_audit = git('show', 'HEAD:' + audit)
assert old_native == (work / 'NATIVE-OWNER-BEFORE.lean.txt').read_bytes()
assert old_audit == (work / 'AUDIT-BEFORE.lean.txt').read_bytes()
assert len(old_native) == 126437
assert (root / native).read_bytes()[55:55 + len(old_native)] == old_native
prefix = b'import MicroCFTA.SourceSynthesisCurrentUniverseColdNoNewMu\n'
assert (root / audit).read_bytes() == prefix + old_audit + b'\n' + (work / 'PUBLIC-PROBES.lean.txt').read_bytes()
assert (root / audit).read_bytes().count(b'#print axioms ') == 660
for component in stage['components']:
    assert sha((root / component['source_path']).read_bytes()) == component['raw_sha256']
baseline = json.loads((work / 'baseline-source-pins.json').read_text())
assert len(baseline) == 6249
assert {str(p.relative_to(root)) for p in (root / 'lean/MicroCFTA').glob('*.lean')} == set(baseline) | {cold}
preserved = 0
for name, digest in baseline.items():
    if name not in {native, audit}:
        assert sha((root / name).read_bytes()) == digest, name
        preserved += 1
assert preserved == 6247
subprocess.run(['git', 'add', '-f', '--', *names], cwd=root, check=True)
assert set(git('diff', '--cached', '--name-only').decode().splitlines()) == set(names)
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=root, check=True)
subprocess.run(['git', 'commit', '--quiet', '-m',
                'Preserve recursive type records through original cold queries'], cwd=root, check=True)
record = {
    'at': datetime.datetime.now().astimezone().isoformat(),
    'source_commit': git('rev-parse', 'HEAD').decode().strip(), 'parent': prior, 'files': names,
    'all_five_publication_gates_passed': True,
    'source_files': 6250, 'audit_imports': 5250, 'audit_reports': 660,
    'independent_reports': 255, 'fresh_component_reports_this_batch': 46,
    'inherited_bound_component_reports': 406, 'combined_component_reports': 452,
    'old_native_reports_replaced': 37, 'new_theorem_declarations': 9,
    'fresh_owner_preflight_reports': 0, 'inherited_owner_reports': 264,
    'old_non_audit_non_native_source_files_byte_exact': preserved,
    'old_native_exact_contiguous_bytes': 126437, 'old_native_offset': 55,
    'old_audit_exact_after_one_import': True,
    'all_old_proof_bodies_and_limits_unchanged': True,
    'new_modules': 1, 'new_private_theorems': 7, 'new_private_predicates': 0,
    'new_public_theorems': 2, 'original441e_and_f041_declarations_exact': True,
    'optional441e_proved': True, 'cold_whole_query_no_new_mu_proved': True,
    'every_bounded_trace_prefix_proved': True, 'terminal_and_pending_effects_retained': True,
    'source_admission_cold_root_scope': True, 'same_original_runtime_fuels': True,
    'external_future_OnlyU_body_result_or_model_supplier': False,
    'independent_query_warm_tables_proved': False,
    'joint_finite_completion_proved': False, 'haskell_changed': False,
}
(work / 'SOURCE-COMMIT.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record))
