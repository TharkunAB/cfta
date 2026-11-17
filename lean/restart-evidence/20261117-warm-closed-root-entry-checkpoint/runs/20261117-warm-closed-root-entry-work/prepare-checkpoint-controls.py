from pathlib import Path
import gzip
import hashlib
import json
import re
import subprocess

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT / 'lean/restart-evidence'
WORK = Path(__file__).resolve().parent
assert WORK == BASE / '20261117-warm-closed-root-entry-work'
PUBLIC = BASE / '20261117-warm-closed-root-entry-publication'
ARCHIVE = '20261117-warm-closed-root-entry-checkpoint'
BOARD_PREFIX = 'current-board-warm-closed-root-entry-'
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
assert [item['total_axiom_reports'] for item in report['checks']] == [668, 9, 263, 668, 668]
assert all(item['exit'] == 0 and not item['diagnostics'] and not item['nonstandard_axioms']
           and not item['sorryAx'] for item in report['checks'])
for key, expected in {'source_files': 6251, 'direct_audit_imports': 5251,
                      'individual_reports': 668, 'independent_reports': 263,
                      'fresh_resource_component_reports': 9,
                      'inherited_resource_component_reports': 452,
                      'resource_and_component_probes': 461,
                      'fresh_owner_preflight_reports': 0,
                      'actual_publication_strict_reports': 9,
                      'new_modules': 1, 'new_public_theorems': 8,
                      'new_private_component_reports': 1, 'new_private_predicates': 0,
                      'new_theorem_reports': 9, 'replaced_old_reports': 0}.items():
    assert report[key] == expected, key
assert [(item['axiom_groups'], item['axiom_free_reports']) for item in report['checks']] == [
    (662, 6), (9, 0), (260, 3), (662, 6), (662, 6)]
assert not report['owner_recompiled_in_publication_strict_gate']
assert report['fresh_owner_preflight_evidence'] is None
assert report['inherited_owner_preflight_evidence']['reports'] == 264
assert not report['inherited_owner_preflight_evidence']['fresh_this_batch']
assert report['inherited_owner_preflight_evidence']['included_in_inherited_452']
for key in ['closed_root_physical_entry_factor_proved', 'closed_root_physical_entry_chain_proved',
            'authentic_warm_entry_at_from_actual_closed_root_proved',
            'source_inventory_no_new_mu_closed_boundary_transport_proved',
            'original_source_cold_closed_boundary_atoms_proved',
            'authentic_initial_source_heap_equality_required',
            'source_initial_ready_and_no_new_mu_derived_internally',
            'whole_worker_program_slots_fixed_marks_proved']:
    assert report[key], key
for key in ['arbitrary_initial_mu_inventory_coverage_proved',
            'mixed_qualified_profile_height_orientation_derived', 'inherited_cell_semantic_chronology_proved',
            'independent_query_inherited_warm_tables_proved', 'warm_across_independent_queries_proved',
            'all_native_inhabitance_proved', 'source_type_marker_class_consistency_proved',
            'joint_finite_completion_proved', 'compiled_haskell_correspondence_proved', 'haskell_changed']:
    assert not report[key], key
assert not commit['external_future_OnlyU_Profile_Result_or_model_supplier']
pins = read(PUBLIC / 'source-pins.json')
for name, digest in pins.items():
    assert SHA((ROOT / name).read_bytes()) == digest, name
source_pins = {name: digest for name, digest in pins.items()
               if name.startswith('lean/MicroCFTA/') and name.endswith('.lean')}
actual = {str(path.relative_to(ROOT)) for path in (ROOT / 'lean/MicroCFTA').glob('*.lean')}
assert len(source_pins) == 6251 and actual == set(source_pins)
assert verified['reverified_pins'] == len(pins)
for name in commit['files']:
    assert GIT('show', code + ':' + name) == (ROOT / name).read_bytes(), name
cold = 'lean/MicroCFTA/SourceSynthesisCurrentUniverseColdBoundaryAtoms.lean'
audit = 'lean/MicroCFTA/Audit.lean'
stage = read(WORK / 'SOURCES-NORMAL-STAGING.json')
assert len(stage['components']) == 7
changed = {item['source_path'] for item in stage['components'][:-1]}
assert len(changed) == 6
assert set(commit['files']) == changed | {cold, audit}
assert set(GIT('diff', '--name-only', prior, code).decode().splitlines()) == changed | {cold, audit}
baseline = read(WORK / 'baseline-source-pins.json')
assert len(baseline) == 6250 and actual == set(baseline) | {cold}
for name, digest in baseline.items():
    if name not in changed | {audit}:
        assert source_pins[name] == digest, name
assert len(set(baseline) - changed - {audit}) == 6243
prefix_bytes = {}
for item in stage['components'][:-1]:
    name = item['source_path']
    old = (WORK / (item['module'] + '-BEFORE.lean.txt')).read_bytes()
    assert GIT('show', prior + ':' + name) == old
    assert SHA(old) == baseline[name]
    current = (ROOT / name).read_bytes()
    assert current.startswith(old), name
    assert [line for line in current.splitlines() if line.startswith(b'import ')] == [
        line for line in old.splitlines() if line.startswith(b'import ')], name
    prefix_bytes[name] = len(old)
assert prefix_bytes == commit['six_old_owner_exact_prefix_bytes']
old_audit = (WORK / 'Audit-BEFORE.lean.txt').read_bytes()
assert GIT('show', prior + ':' + audit) == old_audit
assert old_audit.count(b'#print axioms ') == 660
prefix = b'import MicroCFTA.SourceSynthesisCurrentUniverseColdBoundaryAtoms\n'
assert (ROOT / audit).read_bytes() == prefix + old_audit + b'\n' + (WORK / 'PUBLIC-PROBES.lean.txt').read_bytes()
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
assert old_checkpoint['resource_and_component_probes'] == 452
assert report['inherited_resource_component_reports'] == old_checkpoint['resource_and_component_probes']
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
boundary_receipt = read(WORK / 'COLD-BOUNDARY-FIRST-VERIFIED.json')
assert boundary_receipt['actual_terminal_exit'] == 0
assert boundary_receipt['authentic_initial_source_heap_equality_required']
assert boundary_receipt['actual_execute_and_every_bounded_prefix_proved']
assert boundary_receipt['initial_Ready_derived_from_source_build']
assert not boundary_receipt['future_OnlyU_Profile_or_Result_supplier']
boundary_result = read(BASE / boundary_receipt['run'] / 'checked.json')
assert boundary_receipt['checks'] == boundary_result['checks']
assert boundary_result['normal_module_checked'] and boundary_result['source_pins_unchanged']
assert boundary_result['checks'][-1]['total_axiom_reports'] == 2
assert all(item['exit'] == 0 and not item['diagnostics'] and not item['nonstandard_axioms']
           and not item['sorryAx'] for item in boundary_result['checks'])
cleanup = read(WORK / 'terminal-cleanup-result.json')
assert cleanup['all_targets_absent']
assert cleanup['sources_logs_live_jobs_normal_lake_unknown_entries_preserved']
assert cleanup['removed_bytes'] == sum(item['bytes'] for item in cleanup['targets'])
assert cleanup['cumulative_removed_bytes'] >= cleanup['removed_bytes']
assert all(item['terminal_exit'] in [0, 1] for item in cleanup['targets'])
usage = read(WORK / 'USAGE.json')
assert 0 <= usage['rate_limits']['primary']['used_percent'] <= 80
roots = read(WORK / 'selection-roots.json')
additional_path = WORK / 'archive-additional-roots.json'
additional = read(additional_path) if additional_path.exists() else []
for item in additional:
    assert re.fullmatch(r'20261117-[a-z0-9-]+', item['root'])
    assert item['manifest'] in ['MANIFEST.json', 'manifest.json', 'MANIFEST.sha256']
    assert SHA((BASE / item['root'] / item['manifest']).read_bytes()) == item['sha256']
    roots.append(item['root'])
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
    assert SHA((ROOT / item['original']).read_bytes()) == item['sha256'], item['original']
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
    old_non_audit_non_changed_owner_source_files_byte_exact=6243,
    six_old_owner_exact_prefix_bytes=prefix_bytes, no_new_imports_to_old_owners=True,
    old_audit_bytes_preserved_after_one_import=True,
    old_owner_proof_bodies_unchanged=True, old_owner_proof_limits_unchanged=True,
    known_cumulative_tmp_removed_bytes=cleanup['cumulative_removed_bytes'],
    primary_usage_percent=usage['rate_limits']['primary']['used_percent'],
    primary_usage_checked_at=usage['event_timestamp'],
    prior_immutable_archive=bindings['prior_archive'],
    prior_manifest_sha256=bindings['prior_manifest_sha256'],
    new_theorem_declarations=9, fresh_strict_reports=9,
    inherited_component_reports=452, replaced_old_reports=0,
    all_new_component_checks_first_pass=True, no_failed_proof_credit_in_this_batch=True,
    additional_frozen_roots=additional,
    joint_finite_completion_proved=False,
    compiled_haskell_correspondence_proved=False, haskell_changed=False, goal_active=True)
skipped = sorted(str(path.relative_to(ROOT)) for path in BASE.iterdir()
    if path.is_dir() and path.name.startswith('20261117-') and str(path.relative_to(ROOT)) not in selected)
review = {
    'prior_checkpoint': prior, 'prior_immutable_archive': bindings['prior_archive'],
    'prior_manifest_sha256': bindings['prior_manifest_sha256'], 'selected_roots': len(selected),
    'base_roots': len(read(WORK / 'selection-roots.json')), 'additional_frozen_roots': additional,
    'policy': 'Keep both first chain packets and the metadata-only correction, all five first-pass chain check-input/check pairs, the inventory first freeze and actual transport/boundary checks, publication and reviewed controls. The original physical factor packet/check remain lossless in the committed prior archive. Nine exact first-header copies are included in the selected controls.',
    'new_public_theorem_reports': 8, 'new_private_component_reports': 1,
    'new_private_predicates': 0, 'new_theorem_declarations': 9,
    'fresh_owner_preflight_reports': 0, 'actual_publication_strict_reports': 9,
    'fresh_reports_this_batch': 9, 'inherited_bound_reports': 452,
    'prior_component_reports': 452, 'replaced_old_reports': 0,
    'inherited_owner_reports_included': 264,
    'all_new_component_checks_first_pass': True, 'failed_proof_credit_this_batch': False,
    'initial_authentic_source_heap_equality_required': True,
    'closed_available_boundary_atoms_only': True, 'physical_warm_entry_interface_only': True,
    'mixed_qualified_profile_height_orientation_derived': False,
    'inherited_cell_semantic_chronology_proved': False,
    'arbitrary_initial_inventory_coverage_proved': False,
    'warm_across_independent_queries_proved': False, 'all_native_inhabitance_proved': False,
    'type_marker_class_consistency_proved': False, 'joint_finite_completion_proved': False,
    'haskell_changed': False, 'no_axiom_string_replay': True,
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
                  'new_theorem_declarations': 9, 'fresh_strict_reports': 9, 'inherited_reports': 452}))
