from pathlib import Path
import gzip
import hashlib
import json
import re
import subprocess

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT / 'lean/restart-evidence'
WORK = Path(__file__).resolve().parent
assert WORK == BASE / '20261117-native-source-admission-work'
PUBLIC = BASE / '20261117-native-source-admission-publication'
ARCHIVE = '20261117-native-source-admission-checkpoint'
BOARD_PREFIX = 'current-board-native-source-admission-'
SHA = lambda data: hashlib.sha256(data).hexdigest()
GIT = lambda *args: subprocess.check_output(['git', *args], cwd=ROOT)
read = lambda path: json.loads(path.read_text())
bindings = read(WORK / 'prior-bindings.json')
prior = bindings['prior_checkpoint']
commit = read(WORK / 'SOURCE-COMMIT.json')
code = commit['source_commit']
assert re.fullmatch(r'[0-9a-f]{40}', code)
assert commit['parent'] == prior
assert GIT('rev-parse', 'HEAD').decode().strip() == code
assert GIT('rev-parse', code + '^').decode().strip() == prior
assert GIT('branch', '--show-current').decode().strip() == 'formalize'
assert not GIT('status', '--porcelain', '--untracked-files=no')
report = read(PUBLIC / 'checked.json')
verified = read(WORK / 'PUBLICATION-VERIFIED.json')
assert verified['actual_terminal'] and verified['pins_unchanged']
assert verified['checks'] == report['checks']
assert len(report['checks']) == 5
assert [item['total_axiom_reports'] for item in report['checks']] == [658, 38, 253, 658, 658]
assert all(item['exit'] == 0 and not item['diagnostics'] and not item['nonstandard_axioms']
           and not item['sorryAx'] for item in report['checks'])
for key, expected in {'source_files': 6249, 'direct_audit_imports': 5249,
                      'individual_reports': 658, 'independent_reports': 253,
                      'fresh_resource_component_reports': 38,
                      'inherited_resource_component_reports': 405,
                      'resource_and_component_probes': 443,
                      'fresh_owner_preflight_reports': 0,
                      'actual_publication_strict_reports': 38,
                      'new_modules': 1, 'new_public_theorems': 2,
                      'new_private_component_reports': 36, 'new_private_predicates': 4}.items():
    assert report[key] == expected, key
assert not report['owner_recompiled_in_publication_strict_gate']
assert report['fresh_owner_preflight_evidence'] is None
assert report['inherited_owner_preflight_evidence']['reports'] == 264
assert not report['inherited_owner_preflight_evidence']['fresh_this_batch']
assert report['inherited_owner_preflight_evidence']['included_in_inherited_405']
for key in ['native_source_admission_proved', 'source_admission_cold_root_scope',
            'reader_actual_control_api_export_proved', 'original363_public_declaration_exact',
            'whole_worker_program_slots_fixed_marks_proved']:
    assert report[key], key
for key in ['optional441e_proved', 'independent_query_inherited_warm_tables_proved',
            'warm_across_independent_queries_proved', 'all_native_inhabitance_proved',
            'source_type_marker_class_consistency_proved', 'joint_finite_completion_proved',
            'compiled_haskell_correspondence_proved', 'haskell_changed']:
    assert not report[key], key
pins = read(PUBLIC / 'source-pins.json')
for name, digest in pins.items():
    assert SHA((ROOT / name).read_bytes()) == digest, name
source_pins = {name: digest for name, digest in pins.items()
               if name.startswith('lean/MicroCFTA/') and name.endswith('.lean')}
actual = {str(path.relative_to(ROOT)) for path in (ROOT / 'lean/MicroCFTA').glob('*.lean')}
assert len(source_pins) == 6249 and actual == set(source_pins)
assert verified['reverified_pins'] == len(pins)
for name in commit['files']:
    assert GIT('show', code + ':' + name) == (ROOT / name).read_bytes(), name
native = 'lean/MicroCFTA/SourceSynthesisCurrentUniverseNativeAllocation.lean'
reader = 'lean/MicroCFTA/SourceCurrentAllocatedNativeSamePrefixKeyedChildResult.lean'
audit = 'lean/MicroCFTA/Audit.lean'
assert set(commit['files']) == {native, reader, audit}
assert set(GIT('diff', '--name-only', prior, code).decode().splitlines()) == {native, reader, audit}
baseline = read(WORK / 'baseline-source-pins.json')
assert len(baseline) == 6248 and actual == set(baseline) | {native}
for name, digest in baseline.items():
    if name not in {reader, audit}:
        assert source_pins[name] == digest, name
assert len(set(baseline) - {reader, audit}) == 6246
old_reader = (WORK / 'KEYED-READER-OWNER-BEFORE.lean.txt').read_bytes()
old_audit = (WORK / 'AUDIT-BEFORE.lean.txt').read_bytes()
assert len(old_reader) == 14650 and GIT('show', prior + ':' + reader) == old_reader
assert GIT('show', prior + ':' + audit) == old_audit
assert (ROOT / reader).read_bytes().startswith(old_reader)
assert old_audit.count(b'#print axioms ') == 656
prefix = b'import MicroCFTA.SourceSynthesisCurrentUniverseNativeAllocation\n'
assert (ROOT / audit).read_bytes() == prefix + old_audit + b'\n' + (WORK / 'PUBLIC-PROBES.lean.txt').read_bytes()
stage = read(WORK / 'SOURCES-NORMAL-STAGING.json')
for item in stage['components']:
    assert source_pins[item['source_path']] == item['raw_sha256']
owner = 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
assert source_pins[owner] == baseline[owner] == report['old_resource_owner_sha256']
prior_archive = BASE / bindings['prior_archive']
for name, key in [('manifest.json', 'prior_manifest_sha256'),
                  ('checkpoint.json', 'prior_checkpoint_json_sha256')]:
    data = (prior_archive / name).read_bytes()
    assert SHA(data) == bindings[key]
    assert GIT('show', prior + ':' + str((prior_archive / name).relative_to(ROOT))) == data
old_checkpoint = read(prior_archive / 'checkpoint.json')
assert old_checkpoint['resource_and_component_probes'] == 405
assert old_checkpoint['checked_code'] == GIT('rev-parse', prior + '^').decode().strip()
prior_files = {item['path']: item for item in read(prior_archive / 'manifest.json')['files']}
for name in ['source-pins.json.gz', 'verification.json', 'archived-inputs.json']:
    data = (prior_archive / name).read_bytes()
    assert len(data) == prior_files[name]['bytes']
    assert SHA(data) == prior_files[name]['sha256']
    assert GIT('show', prior + ':' + str((prior_archive / name).relative_to(ROOT))) == data
old_verification = read(prior_archive / 'verification.json')
assert old_verification['checked_code'] == old_checkpoint['checked_code']
assert old_verification['source_tree_sha256'] == old_checkpoint['source_tree_sha256']
assert old_verification['prior_document_bytes_preserved']
old_pins = json.loads(gzip.decompress((prior_archive / 'source-pins.json.gz').read_bytes()))
for name in ['shell.nix', 'lean/lean-toolchain', 'lean/lakefile.toml', 'lean/lake-manifest.json']:
    assert old_pins[name] == pins[name], name
assert baseline == {name: digest for name, digest in old_pins.items()
                    if name.startswith('lean/MicroCFTA/') and name.endswith('.lean')}
request = read(WORK / (BOARD_PREFIX + 'request.json'))
canonical = read(WORK / (BOARD_PREFIX + 'canonical.json'))
assert canonical['verified']
post = canonical['post']
assert post['id'] == request['request_id']
assert type(post['sequence']) is int and post['sequence'] > 0
for key, expected in [('author', request['username']), ('thread_id', request['thread_id']),
                      ('post_type', request['post_type']), ('content', request['content']),
                      ('metadata', request['metadata'])]:
    assert post[key] == expected, key
assert post['metadata']['source'] == code
optional_receipt = read(WORK / 'OPTIONAL441E-FIRST-VERIFIED.json')
assert optional_receipt['actual_terminal_exit'] == 0
assert optional_receipt['exact441e_public_declaration']
assert optional_receipt['optional441e_checked_outside_normal_source']
assert not optional_receipt['normal_source_optional441e_staged']
assert not optional_receipt['future_OnlyU_or_body_law_suppliers']
assert optional_receipt['pending_outcomes_retained']
assert optional_receipt['same_original_fuels_and_default_limits']
optional_run = BASE / optional_receipt['run']
optional_result = read(optional_run / 'checked.json')
assert optional_receipt['checks'] == optional_result['checks']
assert optional_result['normal_module_checked'] and optional_result['source_pins_unchanged']
assert optional_result['checks'][-1]['total_axiom_reports'] == 43
assert all(item['exit'] == 0 and not item['diagnostics'] and not item['nonstandard_axioms']
           and not item['sorryAx'] for item in optional_result['checks'])
cleanup = read(WORK / 'terminal-cleanup-result.json')
assert cleanup['all_targets_absent']
assert cleanup['sources_logs_live_jobs_normal_lake_unknown_entries_preserved']
assert cleanup['removed_bytes'] == sum(item['bytes'] for item in cleanup['targets'])
assert cleanup['cumulative_removed_bytes'] >= cleanup['removed_bytes']
assert all(item['terminal_exit'] in [0, 1] for item in cleanup['targets'])
usage = read(WORK / 'USAGE.json')
assert 0 <= usage['rate_limits']['primary']['used_percent'] <= 80
roots = read(WORK / 'selection-roots.json')
assert len(roots) == len(set(roots))
assert all((BASE / name).is_dir() and not (BASE / name).is_symlink() for name in roots)
# A stale running.json is not a terminal receipt. Require completed results.
for name in roots:
    run = BASE / name
    if (run / 'check.py').exists():
        result = read(run / ('checked.json' if (run / 'checked.json').exists() else 'results.json'))
        assert result['checks'] and all(type(item['exit']) is int for item in result['checks']), name
for item in read(WORK / 'original-header-files.json'):
    assert SHA((ROOT / item['path']).read_bytes()) == item['sha256'], item['path']
selected = sorted(str((BASE / name).relative_to(ROOT)) for name in roots)
assert not (BASE / ARCHIVE).exists()
config = dict(report)
tree = hashlib.sha256()
for name, digest in sorted(source_pins.items()):
    tree.update(name.encode() + b'\0' + digest.encode() + b'\n')
config.update(checked_code=code, prior_checkpoint=prior, public_run=str(PUBLIC), public_gates=5,
    explicit_reports=report['individual_reports'], board_prefix=BOARD_PREFIX,
    board_post_id=post['id'], board_sequence=post['sequence'],
    source_tree_sha256=tree.hexdigest(),
    old_non_audit_non_reader_source_files_byte_exact=6246,
    old_reader_exact_prefix_bytes=14650, old_audit_bytes_preserved_after_one_import=True,
    old_owner_proof_bodies_unchanged=True, old_owner_proof_limits_unchanged=True,
    known_cumulative_tmp_removed_bytes=cleanup['cumulative_removed_bytes'],
    primary_usage_percent=usage['rate_limits']['primary']['used_percent'],
    primary_usage_checked_at=usage['event_timestamp'],
    prior_immutable_archive=bindings['prior_archive'],
    prior_manifest_sha256=bindings['prior_manifest_sha256'],
    optional441e_proved=False, optional441e_checked_outside_normal_source=True,
    normal_source_optional441e_staged=False, optional_private_check_reports=43,
    optional_private_check_counted_in_fresh_38=False, joint_finite_completion_proved=False,
    compiled_haskell_correspondence_proved=False, haskell_changed=False, goal_active=True)
skipped = sorted(str(path.relative_to(ROOT)) for path in BASE.iterdir()
    if path.is_dir() and path.name.startswith('20261117-') and str(path.relative_to(ROOT)) not in selected)
review = {
    'prior_checkpoint': prior, 'prior_immutable_archive': bindings['prior_archive'],
    'prior_manifest_sha256': bindings['prior_manifest_sha256'], 'selected_roots': len(selected),
    'policy': 'Keep every new native repair and failed check, the normal publication, all optional first/layout/owner-helper attempts and exact original441e headers. Older first native failures and reader export inputs remain lossless in the committed prior archive.',
    'new_public_theorem_reports': 2, 'new_private_component_reports': 36,
    'new_private_predicates': 4, 'fresh_owner_preflight_reports': 0,
    'actual_publication_strict_reports': 38, 'fresh_reports_this_batch': 38,
    'inherited_bound_reports': 405, 'inherited_owner_reports_included': 264,
    'optional441e_proved': False, 'optional441e_checked_outside_normal_source': True,
    'normal_source_optional441e_staged': False, 'optional_private_check_reports': 43,
    'optional_private_checks_counted_in_fresh_38': False,
    'warm_across_independent_queries_proved': False,
    'joint_finite_completion_proved': False, 'no_axiom_string_replay': True,
    'no_compiled_objects_or_import_overlays': True,
}
note = (WORK / 'checkpoint-note.md').read_text()
for key, value in {'THEOREMS': report['audited_theorems'], 'REMOVED': cleanup['removed_bytes'],
                   'CLEANUP': cleanup['cumulative_removed_bytes'],
                   'USAGE': config['primary_usage_percent']}.items():
    note = note.replace('{{' + key + '}}', str(value))
assert set(re.findall(r'\{\{(.*?)\}\}', note)) == {'TIME', 'TREE', 'CODE'}
outputs = {'checkpoint-config.json': config, 'archive-roots.json': selected,
           'skipped-published-roots.json': skipped, 'selection-review.json': review}
assert all(not (WORK / name).exists() for name in outputs)
for name, value in outputs.items():
    (WORK / name).write_text(json.dumps(value, indent=2) + '\n')
(WORK / 'checkpoint-note.md').write_text(note)
print(json.dumps({'checked_code': code, 'packet': ARCHIVE,
                  'roots': len(selected), 'board_sequence': post['sequence'],
                  'fresh_strict_reports': 38, 'inherited_reports': 405}))
