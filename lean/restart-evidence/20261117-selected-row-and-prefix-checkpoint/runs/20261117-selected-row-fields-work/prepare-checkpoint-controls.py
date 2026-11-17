from pathlib import Path
import json
import re
import subprocess

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
work = Path(__file__).parent
prior = '96ffd9f62a894fa135343c1b94c6f09bc10b2f6e'
public = base / '20261117-selected-row-and-prefix-publication'
report = json.loads((public / 'checked.json').read_text())
assert len(report['checks']) == 5
assert all(item['exit'] == 0 and not item['nonstandard_axioms'] and not item['diagnostics']
           and not item['sorryAx'] for item in report['checks'])
commit = json.loads((work / 'SOURCE-COMMIT.json').read_text())
code = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip()
assert code == commit['source_commit'] and commit['parent'] == prior
for name in commit['files']:
    assert subprocess.check_output(['git', 'show', code + ':' + name], cwd=root) == (root / name).read_bytes()
cleanup = json.loads((work / 'terminal-cleanup-result.json').read_text())
usage = json.loads((work / 'USAGE.json').read_text())
assert usage['rate_limits']['primary']['used_percent'] <= 80
config = dict(report)
config.update(checked_code=code, prior_checkpoint=prior, public_run=str(public), public_gates=5,
    explicit_reports=report['individual_reports'], board_prefix='current-board-real-prefix-',
    old_non_audit_non_owner_source_files_byte_exact=6240,
    old_owner_proof_bodies_unchanged=True, old_owner_proof_limits_unchanged=True,
    old_audit_bytes_after_new_ordinary_imports=True,
    known_cumulative_tmp_removed_bytes=cleanup['cumulative_removed_bytes'],
    primary_usage_percent=usage['rate_limits']['primary']['used_percent'],
    primary_usage_checked_at=usage['event_timestamp'],
    source_raw_target_compatibility_producer_proved=False,
    all_historical_same_output_semantic_attachment_proved=False,
    retained_core_obligations_guardsHold_proved=False,
    source_pending_Profile_closure_proved=False, compiled_haskell_correspondence_proved=False,
    output_equality_alone_does_not_identify_invocation=True, goal_active=True,
    prior_immutable_archive='20261117-application-class-birth-checkpoint')
(work / 'checkpoint-config.json').write_text(json.dumps(config, indent=2) + '\n')
roots = ['20261117-selected-row-fields-work',
    '20261117-current-source-selected-row-fields-draft',
    '20261117-selected-row-fields-check',
    '20261117-real-prefix-program-slots-transport-draft',
    '20261117-real-prefix-program-slots-check',
    '20261117-real-prefix-program-slots-import-repair',
    '20261117-real-prefix-program-slots-import-check',
    '20261117-selected-row-and-prefix-publication',
    '20261117-source-empty-check-caller-correspondence-audit']
selected = sorted(str((base / name).relative_to(root)) for name in roots)
assert all((root / name).is_dir() for name in selected)
skipped = sorted(str(p.relative_to(root)) for p in base.iterdir()
                 if p.is_dir() and p.name.startswith('20261117-') and str(p.relative_to(root)) not in selected)
(work / 'archive-roots.json').write_text(json.dumps(selected, indent=2) + '\n')
(work / 'skipped-published-roots.json').write_text(json.dumps(skipped, indent=2) + '\n')
(work / 'selection-review.json').write_text(json.dumps({
    'prior_checkpoint': prior, 'selected_roots': len(selected),
    'policy': 'Preserve every first packet, frozen header, failed check, import repair, selected-row and prefix proof, caller audit and publication control of this completed batch.',
    'prior_push_receipt_copied_to_new_work': True,
    'new_public_theorem_reports': 2, 'new_private_component_reports': 6,
    'fresh_strict_reports': 8, 'inherited_bound_strict_reports': 366,
    'in_progress_next_batch_packets_retained_in_live_workspace': True,
    'current_tree_source_path_set_check_inherited_unchanged': True,
    'no_compiled_objects_or_import_overlays': True}, indent=2) + '\n')
fields = {'SOURCE_FILES': report['source_files'], 'AUDIT_IMPORTS': report['direct_audit_imports'],
    'AUDIT_REPORTS': report['individual_reports'], 'STANDARD_REPORTS': report['checks'][-1]['axiom_groups'],
    'FREE_REPORTS': report['checks'][-1]['axiom_free_reports'], 'INDEPENDENT_REPORTS': report['independent_reports'],
    'RESOURCE_REPORTS': report['resource_and_component_probes'], 'OWNER_REPORTS': report['owner_resource_probes'],
    'THEOREMS': report['audited_theorems'], 'CLEANUP': cleanup['cumulative_removed_bytes'],
    'USAGE': config['primary_usage_percent']}
note = (work / 'checkpoint-note.md').read_text()
for key, value in fields.items():
    note = note.replace('{{' + key + '}}', str(value))
assert set(re.findall(r'\{\{(.*?)\}\}', note)) == {'TIME', 'TREE', 'CODE'}
(work / 'checkpoint-note.md').write_text(note)
print(json.dumps({'checked_code': code, 'packet': '20261117-selected-row-and-prefix-checkpoint',
                  'roots': len(selected)}))
