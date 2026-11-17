from pathlib import Path
import datetime
import json
import re
import subprocess

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
work = Path(__file__).parent
prior = '2855a1f7b2664fc1677bf50a43a50d35f9442136'
public = base / '20261117-application-class-birth-publication'
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
    explicit_reports=report['individual_reports'], board_prefix='current-board-app-birth-',
    old_non_audit_non_owner_source_files_byte_exact=6239,
    old_owner_bytes_preserved_contiguously=report['old_owner_bytes_preserved_contiguously'], old_owner_offset=0,
    old_owner_proof_bodies_unchanged=True, old_owner_proof_limits_unchanged=True,
    old_audit_bytes_after_new_ordinary_imports=True,
    known_cumulative_tmp_removed_bytes=cleanup['cumulative_removed_bytes'],
    primary_usage_percent=usage['rate_limits']['primary']['used_percent'],
    primary_usage_checked_at=usage['event_timestamp'],
    source_raw_target_compatibility_producer_proved=False,
    all_historical_same_output_semantic_attachment_proved=False,
    retained_core_obligations_guardsHold_proved=False,
    source_pending_Profile_closure_proved=False, compiled_haskell_correspondence_proved=False,
    all_history9374_proved=True, full9374_candidate_frozen_uncompiled=False,
    output_equality_alone_does_not_identify_invocation=True, goal_active=True,
    prior_immutable_archive='20261117-whole-branch-nested-held-checkpoint')
(work / 'checkpoint-config.json').write_text(json.dumps(config, indent=2) + '\n')
cut = datetime.datetime.fromisoformat(json.loads((work / 'START.json').read_text())['at']).timestamp() - 1
selected, skipped = [], []
for path in base.iterdir():
    if not path.is_dir() or not path.name.startswith('20261117-'):
        continue
    relative = str(path.relative_to(root))
    if ('checkpoint' in path.name or path.name in {'20261117-nested-held-entry-work', '20261117-whole-branch-nested-held-work'}
            or path.stat().st_mtime < cut):
        skipped.append(relative)
    else:
        selected.append(relative)
assert len(selected) >= 8
assert str(work.relative_to(root)) in selected and str(public.relative_to(root)) in selected
for name in ['20261117-application-class-birth-check',
             '20261117-current-source-application-class-birth-readback-repair',
             '20261117-application-class-birth-readback-check',
             '20261117-application-class-birth-beta-index-repair',
             '20261117-application-class-birth-beta-index-check',
             '20261117-current-source-selected-row-fields-draft',
             '20261117-application-marker-invocation-lineage-audit']:
    assert str((base / name).relative_to(root)) in selected, name
(work / 'archive-roots.json').write_text(json.dumps(sorted(selected), indent=2) + '\n')
(work / 'skipped-published-roots.json').write_text(json.dumps(sorted(skipped), indent=2) + '\n')
(work / 'selection-review.json').write_text(json.dumps({
    'prior_checkpoint': prior, 'selected_roots': len(selected),
    'policy': 'Preserve every new source packet, first header, failed check, repair, marked open target, publication control and prior immutable archive.',
    'prior_push_receipt_copied_to_new_work': True,
    'new_public_theorem_reports': 1, 'new_private_component_reports': 0,
    'new_relation_declaration_reports': 0, 'new_declaration_checks': 0,
    'compiler_running_markers_are_not_liveness_evidence': True,
    'fresh_strict_reports': 1, 'inherited_bound_strict_reports': 365,
    'new_current_tree_verifier_rejects_extra_source_paths': True,
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
print(json.dumps({'checked_code': code, 'packet': '20261117-application-class-birth-checkpoint',
                  'roots': len(selected)}))
