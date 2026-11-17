from pathlib import Path
import datetime
import hashlib
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
public = work.parent / '20261117-native-source-admission-publication'
prior = '69bd8299c9e5e604c991e8327d385cf64b0facd0'
sha = lambda data: hashlib.sha256(data).hexdigest()
git = lambda *args: subprocess.check_output(['git', *args], cwd=root)
report = json.loads((public / 'checked.json').read_text())
assert len(report['checks']) == 5
assert all(c['exit'] == 0 and not c['diagnostics'] and not c['nonstandard_axioms']
           and not c['sorryAx'] for c in report['checks'])
assert report['fresh_resource_component_reports'] == 38
assert report['inherited_resource_component_reports'] == 405
assert report['fresh_owner_preflight_reports'] == 0
assert report['native_source_admission_proved'] and report['reader_actual_control_api_export_proved']
assert not report['optional441e_proved'] and not report['joint_finite_completion_proved']
for name, digest in json.loads((public / 'source-pins.json').read_text()).items():
    assert sha((root / name).read_bytes()) == digest, name
assert git('branch', '--show-current').decode().strip() == 'formalize'
assert git('rev-parse', 'HEAD').decode().strip() == prior
assert not git('diff', '--cached', '--name-only')
stage = json.loads((work / 'SOURCES-NORMAL-STAGING.json').read_text())
native = 'lean/MicroCFTA/SourceSynthesisCurrentUniverseNativeAllocation.lean'
reader = 'lean/MicroCFTA/SourceCurrentAllocatedNativeSamePrefixKeyedChildResult.lean'
audit = 'lean/MicroCFTA/Audit.lean'
names = [native, reader, audit]
assert set(git('diff', '--name-only').decode().splitlines()) == {reader, audit}
assert not git('ls-files', '--', native)
old_reader = git('show', 'HEAD:' + reader)
old_audit = git('show', 'HEAD:' + audit)
assert old_reader == (work / 'KEYED-READER-OWNER-BEFORE.lean.txt').read_bytes()
assert old_audit == (work / 'AUDIT-BEFORE.lean.txt').read_bytes()
assert len(old_reader) == 14650
assert (root / reader).read_bytes().startswith(old_reader)
prefix = b'import MicroCFTA.SourceSynthesisCurrentUniverseNativeAllocation\n'
audit_raw = (root / audit).read_bytes()
assert audit_raw.startswith(prefix + old_audit)
assert audit_raw.count(b'#print axioms ') == 658
for component in stage['components']:
    assert sha((root / component['source_path']).read_bytes()) == component['raw_sha256']
baseline = json.loads((work / 'baseline-source-pins.json').read_text())
assert len(baseline) == 6248
assert {str(p.relative_to(root)) for p in (root / 'lean/MicroCFTA').glob('*.lean')} == set(baseline) | {native}
preserved = 0
for name, digest in baseline.items():
    if name not in {reader, audit}:
        assert sha((root / name).read_bytes()) == digest, name
        preserved += 1
assert preserved == 6246
subprocess.run(['git', 'add', '-f', '--', *names], cwd=root, check=True)
assert set(git('diff', '--cached', '--name-only').decode().splitlines()) == set(names)
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=root, check=True)
subprocess.run(['git', 'commit', '--quiet', '-m',
                'Classify native Mu requests from original source prefixes'], cwd=root, check=True)
record = {
    'at': datetime.datetime.now().astimezone().isoformat(),
    'source_commit': git('rev-parse', 'HEAD').decode().strip(), 'parent': prior, 'files': names,
    'all_five_publication_gates_passed': True,
    'source_files': 6249, 'audit_imports': 5249, 'audit_reports': 658,
    'independent_reports': 253, 'fresh_component_reports_this_batch': 38,
    'inherited_bound_component_reports': 405, 'combined_component_reports': 443,
    'fresh_owner_preflight_reports': 0, 'inherited_owner_reports': 264,
    'old_non_audit_non_reader_source_files_byte_exact': preserved,
    'old_reader_exact_prefix_bytes': 14650, 'old_audit_exact_after_one_import': True,
    'all_old_proof_bodies_and_limits_unchanged': True,
    'new_modules': 1, 'new_private_theorems': 36, 'new_private_predicates': 4,
    'new_public_theorems': 2, 'original363_declaration_exact': True,
    'native_admission_cold_root_scope': True, 'reader_export_api_only': True,
    'same_original_runtime_fuels': True, 'external_future_result_law_supplier': False,
    'optional441e_proved': False, 'independent_query_warm_tables_proved': False,
    'joint_finite_completion_proved': False, 'haskell_changed': False,
}
(work / 'SOURCE-COMMIT.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record))
