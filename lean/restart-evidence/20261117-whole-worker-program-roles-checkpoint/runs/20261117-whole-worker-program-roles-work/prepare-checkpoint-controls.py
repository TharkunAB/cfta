from pathlib import Path
import datetime
import json
import re
import subprocess

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
work = Path(__file__).parent
old_work = base / '20261117-actual-eager-role-producer-work'
old_packet = '20261117-actual-eager-role-producer-checkpoint'
new_packet = '20261117-whole-worker-program-roles-checkpoint'
prior = 'a0e968a176e23825baaeb4f2180d470d8c7c1c33'
old_prior = '1cd951d8db17fb030f1f382dff7177ce4ef5369b'
public = base / '20261117-whole-worker-program-roles-publication'
report = json.loads((public / 'checked.json').read_text())
commit = json.loads((work / 'SOURCE-COMMIT.json').read_text())
code = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip()
assert code == commit['source_commit'] and commit['parent'] == prior
assert len(report['checks']) == 5
assert all(c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics']
           and not c['sorryAx'] for c in report['checks'])
assert report['source_files'] == 6248 and report['individual_reports'] == 656
assert report['fresh_resource_component_reports'] == 278
assert report['inherited_resource_component_reports'] == 127
assert report['owner_resource_probes'] == 264
assert report['checks'][1]['total_axiom_reports'] == 14
assert report['whole_worker_program_slots_fixed_marks_proved']
for name in commit['files']:
    assert subprocess.check_output(['git', 'show', code + ':' + name], cwd=root) == (root / name).read_bytes()
request = json.loads((work / 'current-board-whole-worker-roles-request.json').read_text())
canonical = json.loads((work / 'current-board-whole-worker-roles-canonical.json').read_text())
assert canonical['verified']
post = canonical['post']
assert post['id'] == request['request_id'] and post['sequence'] == 1477
for name, expected in [('author', request['username']), ('thread_id', request['thread_id']),
                       ('post_type', request['post_type']), ('content', request['content']),
                       ('metadata', request['metadata'])]:
    assert post[name] == expected, name
cleanup = json.loads((work / 'terminal-cleanup-result.json').read_text())
usage = json.loads((work / 'USAGE.json').read_text())
assert usage['rate_limits']['primary']['used_percent'] <= 80
config = dict(report)
config.update(checked_code=code, prior_checkpoint=prior, public_run=str(public), public_gates=5,
    explicit_reports=report['individual_reports'], board_prefix='current-board-whole-worker-roles-',
    old_non_audit_non_owner_non_fragment_source_files_byte_exact=6245,
    old_owner_proof_bodies_unchanged=True, old_owner_proof_limits_unchanged=True,
    old_audit_bytes_preserved_as_prefix=True,
    known_cumulative_tmp_removed_bytes=cleanup['cumulative_removed_bytes'],
    primary_usage_percent=usage['rate_limits']['primary']['used_percent'],
    primary_usage_checked_at=usage['event_timestamp'],
    source_raw_target_compatibility_producer_proved=False,
    all_historical_same_output_semantic_attachment_proved=False,
    retained_core_obligations_guardsHold_proved=False,
    source_pending_Profile_closure_proved=False, compiled_haskell_correspondence_proved=False,
    source_active_mu_admission_proved=False, whole_worker_roles_proved=True,
    whole_worker_program_slots_fixed_marks_proved=True,
    output_equality_alone_does_not_identify_invocation=True, goal_active=True,
    prior_immutable_archive=old_packet)
(work / 'checkpoint-config.json').write_text(json.dumps(config, indent=2) + '\n')
roots = [
    '20261117-whole-worker-program-roles-work',
    '20261117-selected-eager-program-fragment-roles-draft',
    '20261117-selected-eager-program-fragment-roles-check-input',
    '20261117-selected-eager-program-fragment-roles-check',
    '20261117-whole-real-eager-captured-component-check-input',
    '20261117-whole-real-eager-captured-component-check',
    '20261117-whole-real-eager-program-slots-captured-proof-draft',
    '20261117-whole-real-eager-program-slots-captured-cache-projection-repair',
    '20261117-whole-real-eager-program-slots-opaque-draft',
    '20261117-whole-real-eager-program-slots-outer-assembly-draft',
    '20261117-whole-real-eager-program-slots-prepared-admission-repair',
    '20261117-whole-real-eager-program-slots-integration-review',
    '20261117-whole-real-eager-program-slots-combined-draft',
    '20261117-whole-real-eager-program-slots-combined-check',
    '20261117-whole-real-eager-program-slots-captured-cache-equality-transport-repair',
    '20261117-whole-real-eager-program-slots-cache-equality-repair',
    '20261117-whole-real-eager-program-slots-cache-equality-check',
    '20261117-whole-worker-role-publication-control-draft',
    '20261117-whole-worker-program-roles-publication',
    '20261117-source-active-mu-source-cuts-draft',
    '20261117-source-active-mu-source-cuts-check-input',
    '20261117-source-active-mu-source-cuts-check',
    '20261117-source-active-mu-source-cuts-validity-repair',
    '20261117-source-active-mu-source-cuts-validity-check-input',
    '20261117-source-active-mu-source-cuts-validity-check',
    '20261117-source-active-mu-full-prefix-admission-draft',
    '20261117-source-active-mu-full-prefix-admission-preparation-failure',
    '20261117-source-active-mu-full-prefix-admission-check-input',
    '20261117-source-active-mu-full-prefix-admission-check',
    '20261117-source-active-mu-full-prefix-elaboration-repair',
    '20261117-source-active-mu-full-prefix-elaboration-check-input',
    '20261117-source-active-mu-full-prefix-elaboration-check',
    '20261117-source-active-mu-exact-branch-repair',
    '20261117-native-reference-self-code-proof-repair',
    '20261117-keyed-child-actual-reader-export-draft',
    '20261117-keyed-child-actual-reader-export-check',
    '20261117-optional-prefix-no-new-mu-discharge-plan',
]
selected = sorted(str((base / name).relative_to(root)) for name in roots)
assert all((root / name).is_dir() for name in selected)
(work / 'archive-roots.json').write_text(json.dumps(selected, indent=2) + '\n')
skipped = sorted(str(p.relative_to(root)) for p in base.iterdir()
    if p.is_dir() and p.name.startswith('20261117-') and str(p.relative_to(root)) not in selected)
(work / 'skipped-published-roots.json').write_text(json.dumps(skipped, indent=2) + '\n')
(work / 'selection-review.json').write_text(json.dumps({
    'prior_checkpoint': prior, 'selected_roots': len(selected),
    'policy': 'Preserve the completed selected-row and whole-worker role batch, every first header, failed check, repair, exact publication control and frozen next native proofs. Distinguish checked API-only exports and private native cuts from the unproved full source producer.',
    'prior_push_receipt_copied_to_new_work': True,
    'new_public_theorem_reports': 2, 'new_private_component_reports': 11,
    'new_private_predicates': 1, 'fresh_owner_preflight_reports': 264,
    'actual_publication_strict_reports': 14, 'fresh_reports_this_batch': 278,
    'inherited_bound_reports': 127,
    'native_source_cuts_reports_outside_normal_source': 12,
    'reader_export_report_outside_normal_source': 1,
    'native_full88486_failed': True, 'native_cf68_failed_at_error_cap': True,
    'native_fb14_uncompiled': True, 'optional441e_unimplemented': True,
    'current_tree_source_path_set_check_inherited_unchanged': True,
    'no_compiled_objects_or_import_overlays': True}, indent=2) + '\n')
for name in ['assemble.py', 'finalize.py', 'verify.py', 'commit-checkpoint.py']:
    text = (old_work / name).read_text().replace(old_packet, new_packet).replace(old_prior, prior)
    if name == 'finalize.py':
        text = text.replace('# Actual eager child return Program roles',
                            '# Program marks at every actual worker output')
    if name == 'commit-checkpoint.py':
        text = text.replace('Record actual eager roles and remaining source admissions',
                            'Record whole-worker Program roles and native proof gaps')
    assert old_packet not in text and old_prior not in text
    assert not (work / name).exists(), name
    (work / name).write_text(text)
fields = {'THEOREMS': report['audited_theorems'], 'REMOVED': cleanup['removed_bytes'],
          'CLEANUP': cleanup['cumulative_removed_bytes'],
          'USAGE': config['primary_usage_percent']}
note = (work / 'checkpoint-note.md').read_text()
for key, value in fields.items():
    note = note.replace('{{' + key + '}}', str(value))
assert set(re.findall(r'\{\{(.*?)\}\}', note)) == {'TIME', 'TREE', 'CODE'}
(work / 'checkpoint-note.md').write_text(note)
assert config['prior_immutable_archive'] == old_packet
print(json.dumps({'checked_code': code, 'packet': new_packet,
                  'roots': len(selected), 'board_sequence': post['sequence']}))
