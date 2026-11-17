from pathlib import Path
import datetime
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
work = Path(__file__).parent
old_work = base / '20261117-shared-child-and-root-gate-work'
old_packet = '20261117-shared-child-and-root-gate-checkpoint'
new_packet = '20261117-actual-eager-role-producer-checkpoint'
prior = '1cd951d8db17fb030f1f382dff7177ce4ef5369b'
old_prior = '3400a25f3f1d302f631af6c9561bcbcb20277d85'
public = base / '20261117-actual-eager-role-producer-publication'
report = json.loads((public / 'checked.json').read_text())
commit = json.loads((work / 'SOURCE-COMMIT.json').read_text())
code = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip()
assert code == commit['source_commit'] and commit['parent'] == prior
assert len(report['checks']) == 5
assert all(c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics']
           and not c['sorryAx'] for c in report['checks'])
assert report['source_files'] == 6248 and report['individual_reports'] == 654
assert report['fresh_resource_component_reports'] == 265
assert report['inherited_resource_component_reports'] == 127
assert report['owner_resource_probes'] == 252
assert report['checks'][1]['total_axiom_reports'] == 13
for name in commit['files']:
    assert subprocess.check_output(['git', 'show', code + ':' + name], cwd=root) == (root / name).read_bytes()

request = json.loads((work / 'current-board-eager-roles-request.json').read_text())
canonical_path = work / 'current-board-eager-roles-canonical.json'
canonical = json.loads(canonical_path.read_text())
post = canonical.get('post', canonical)
assert post['id'] == request['request_id'] and post['sequence'] == 1473
for name, expected in [('author', request['username']), ('thread_id', request['thread_id']),
                       ('post_type', request['post_type']), ('content', request['content']),
                       ('metadata', request['metadata'])]:
    assert post[name] == expected, name
canonical_path.write_text(json.dumps({'verified': True,
    'checked_at': datetime.datetime.now().astimezone().isoformat(),
    'post': post}, indent=2) + '\n')

cleanup = json.loads((work / 'terminal-cleanup-result.json').read_text())
usage = json.loads((work / 'USAGE.json').read_text())
assert usage['rate_limits']['primary']['used_percent'] <= 80
config = dict(report)
config.update(checked_code=code, prior_checkpoint=prior, public_run=str(public), public_gates=5,
    explicit_reports=report['individual_reports'], board_prefix='current-board-eager-roles-',
    old_non_audit_non_owner_source_files_byte_exact=6244,
    old_owner_proof_bodies_unchanged=True, old_owner_proof_limits_unchanged=True,
    old_audit_bytes_after_new_ordinary_imports=True,
    known_cumulative_tmp_removed_bytes=cleanup['cumulative_removed_bytes'],
    primary_usage_percent=usage['rate_limits']['primary']['used_percent'],
    primary_usage_checked_at=usage['event_timestamp'],
    source_raw_target_compatibility_producer_proved=False,
    all_historical_same_output_semantic_attachment_proved=False,
    retained_core_obligations_guardsHold_proved=False,
    source_pending_Profile_closure_proved=False, compiled_haskell_correspondence_proved=False,
    source_active_mu_admission_proved=False, whole_worker_roles_proved=False,
    output_equality_alone_does_not_identify_invocation=True, goal_active=True,
    prior_immutable_archive=old_packet)
(work / 'checkpoint-config.json').write_text(json.dumps(config, indent=2) + '\n')

roots = [
    '20261117-actual-eager-role-producer-work',
    '20261117-observed-child-program-slots-draft',
    '20261117-observed-child-program-slots-check',
    '20261117-actual-eager-return-program-slots-draft',
    '20261117-actual-eager-return-program-slots-check',
    '20261117-actual-eager-program-fragment-roles-draft',
    '20261117-actual-eager-program-fragment-roles-check',
    '20261117-actual-eager-program-fragment-roles-projection-repair',
    '20261117-actual-eager-program-fragment-roles-projection-check',
    '20261117-actual-eager-return-joint-program-roles-draft',
    '20261117-actual-eager-return-joint-program-roles-check',
    '20261117-actual-eager-role-publication-control-draft',
    '20261117-actual-eager-role-producer-publication',
    '20261117-source-only-universe-native-allocation-audit',
    '20261117-source-optional-owner-admission-gap',
    '20261117-source-active-mu-carrier-core-check-input',
    '20261117-source-active-mu-carrier-core-check',
    '20261117-source-active-mu-carrier-width-repair',
    '20261117-source-active-mu-carrier-width-check-input',
    '20261117-source-active-mu-carrier-width-check',
    '20261117-source-active-mu-carrier-let-repair',
    '20261117-source-active-mu-carrier-let-check-input',
    '20261117-source-active-mu-carrier-let-check',
    '20261117-source-active-mu-source-cuts-draft',
    '20261117-source-active-mu-closed-compiler-draft',
    '20261117-whole-real-eager-program-slots-draft',
    '20261117-whole-real-eager-program-slots-prepared-admission-repair',
    '20261117-whole-real-eager-program-slots-captured-proof-draft',
    '20261117-whole-real-eager-program-slots-outer-assembly-draft',
    '20261117-selected-eager-program-fragment-roles-draft',
]
selected = sorted(str((base / name).relative_to(root)) for name in roots)
assert all((root / name).is_dir() for name in selected)
(work / 'archive-roots.json').write_text(json.dumps(selected, indent=2) + '\n')
skipped = sorted(str(p.relative_to(root)) for p in base.iterdir()
    if p.is_dir() and p.name.startswith('20261117-') and str(p.relative_to(root)) not in selected)
(work / 'skipped-published-roots.json').write_text(json.dumps(skipped, indent=2) + '\n')
(work / 'selection-review.json').write_text(json.dumps({
    'prior_checkpoint': prior, 'selected_roots': len(selected),
    'policy': 'Preserve this completed eager-role batch, first headers, failed checks, repairs, exact publication control and frozen next-batch interfaces. Keep frozen uncompiled next proofs explicitly unproved.',
    'prior_push_receipt_copied_to_new_work': True,
    'new_public_theorem_reports': 2, 'new_private_component_reports': 13,
    'fresh_owner_preflight_reports': 252, 'actual_publication_strict_reports': 13,
    'fresh_reports_this_batch': 265, 'inherited_bound_reports': 127,
    'native_private_core_reports_outside_normal_source': 5,
    'native_source_cuts_and_closed_compiler_uncompiled': True,
    'whole_worker_selected_leaf_captured_and_outer_assembly_uncompiled': True,
    'captured_manifest_clock_caveat': 'Frozen manifest estimated11:41; actual reported freeze11:32 CET. No proof bytes changed.',
    'in_progress_native_prefix_packet_retained_in_live_workspace': True,
    'current_tree_source_path_set_check_inherited_unchanged': True,
    'no_compiled_objects_or_import_overlays': True}, indent=2) + '\n')

for name in ['assemble.py', 'finalize.py', 'verify.py', 'commit-checkpoint.py']:
    text = (old_work / name).read_text().replace(old_packet, new_packet).replace(old_prior, prior)
    if name == 'finalize.py':
        text = text.replace('# Shared child marks and the raw original-root gate',
                            '# Actual eager child return Program roles')
    if name == 'commit-checkpoint.py':
        text = text.replace('Record child marks and raw-root caller boundaries',
                            'Record actual eager roles and remaining source admissions')
    assert old_packet not in text and old_prior not in text
    assert not (work / name).exists(), name
    (work / name).write_text(text)
assert config['prior_immutable_archive'] == old_packet
print(json.dumps({'checked_code': code, 'packet': new_packet,
                  'roots': len(selected), 'board_sequence': post['sequence']}))
