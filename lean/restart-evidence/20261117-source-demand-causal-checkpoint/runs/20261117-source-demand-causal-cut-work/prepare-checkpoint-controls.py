from pathlib import Path
import datetime
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
work = Path(__file__).parent
prior = '91f7d0eb8ba0743fce7ae6dcf9ead3fc74526aa3'
public = base / '20261117-source-demand-causal-publication'
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
    explicit_reports=report['individual_reports'], board_prefix='current-board-causal-',
    old_non_audit_source_files_byte_exact=6225, entire_previous_resource_owner_byte_exact=True,
    old_audit_bytes_after_new_ordinary_imports=True,
    known_cumulative_tmp_removed_bytes=cleanup['cumulative_removed_bytes'],
    primary_usage_percent=usage['rate_limits']['primary']['used_percent'],
    primary_usage_checked_at=usage['event_timestamp'],
    actual_parked_suffix_same_original_output_kept_proved=True,
    same_snapshot_one_arrow_bucket_conditional_recompletion_proved=True,
    source_raw_target_compatibility_producer_proved=False,
    all_historical_same_output_semantic_attachment_proved=False,
    retained_core_obligations_guardsHold_proved=False,
    source_pending_Profile_closure_proved=False, compiled_haskell_correspondence_proved=False,
    every_staged_child_position_incidence_proved=True,
    output_equality_alone_does_not_identify_invocation=True, goal_active=True,
    prior_immutable_archive='20261117-qualified-history-checkpoint')
(work / 'checkpoint-config.json').write_text(json.dumps(config, indent=2) + '\n')
cut = datetime.datetime.fromisoformat(json.loads((work / 'START.json').read_text())['at']).timestamp() - 1
selected, skipped = [], []
for path in base.iterdir():
    if not path.is_dir() or not path.name.startswith('20261117-'):
        continue
    relative = str(path.relative_to(root))
    if 'checkpoint' in path.name or path.name == '20261117-qualified-history-work' or path.stat().st_mtime < cut:
        skipped.append(relative)
    else:
        selected.append(relative)
assert len(selected) >= 15
assert str(work.relative_to(root)) in selected and str(public.relative_to(root)) in selected
(work / 'archive-roots.json').write_text(json.dumps(sorted(selected), indent=2) + '\n')
(work / 'skipped-published-roots.json').write_text(json.dumps(sorted(skipped), indent=2) + '\n')
(work / 'selection-review.json').write_text(json.dumps({
    'prior_checkpoint': prior, 'selected_roots': len(selected),
    'policy': 'Preserve new source packets, first headers, all failed checks and repairs, marked open targets, and all publication controls. Preserve every prior immutable archive.',
    'prior_push_receipt_copied_to_new_work': True,
    'new_theorem_reports': report['new_public_theorems'],
    'new_declaration_checks': report['new_relation_declaration_checks'],
    'compiler_running_markers_are_not_liveness_evidence': True,
    'no_compiled_objects_or_import_overlays': True}, indent=2) + '\n')
fields = {'SOURCE_FILES': report['source_files'], 'AUDIT_IMPORTS': report['direct_audit_imports'],
    'AUDIT_REPORTS': report['individual_reports'], 'STANDARD_REPORTS': report['checks'][-1]['axiom_groups'],
    'FREE_REPORTS': report['checks'][-1]['axiom_free_reports'], 'INDEPENDENT_REPORTS': report['independent_reports'],
    'RESOURCE_REPORTS': report['resource_and_component_probes'], 'OWNER_REPORTS': report['owner_resource_probes'],
    'RESOURCE_STANDARD': report['checks'][1]['axiom_groups'], 'RESOURCE_FREE': report['checks'][1]['axiom_free_reports'],
    'THEOREMS': report['audited_theorems'], 'OLD_SOURCES': 6225,
    'NEW_REPORTS': report['new_component_reports'], 'NEW_THEOREMS': report['new_public_theorems'],
    'NEW_MODULES': report['new_modules'], 'NEW_DECLARATION_CHECKS': report['new_relation_declaration_checks'],
    'CLEANUP': cleanup['cumulative_removed_bytes'], 'USAGE': config['primary_usage_percent']}
note = (work / 'checkpoint-note.md').read_text()
for key, value in fields.items():
    note = note.replace('{{' + key + '}}', str(value))
(work / 'checkpoint-note.md').write_text(note)
print(json.dumps({'checked_code': code, 'packet': '20261117-source-demand-causal-checkpoint',
                  'roots': len(selected)}))
