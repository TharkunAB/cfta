from pathlib import Path
import datetime
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
work = Path(__file__).parent
old = base / '20261116-indexed-invocation-work'
prior = '2cc2ff8cd1bb7a78c293476b3f9f79d1ff77efa8'
packet_name = '20261116-staged-child-incidence-checkpoint'
public = base / '20261116-staged-child-incidence-publication'
report = json.loads((public / 'checked.json').read_text())
assert len(report['checks']) == 5
assert all(x['exit'] == 0 and not x['nonstandard_axioms'] and not x['diagnostics'] and not x['sorryAx'] for x in report['checks'])
code = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip()
commit = json.loads((work / 'SOURCE-COMMIT.json').read_text())
assert code == commit['source_commit'] and code != prior
for relative in commit['files']:
    assert subprocess.check_output(['git', 'show', code + ':' + relative], cwd=root) == (root / relative).read_bytes()
cleanup = json.loads((work / 'terminal-cleanup-result.json').read_text())
usage = json.loads((work / 'USAGE.json').read_text())
config = dict(report)
config.update(checked_code=code, prior_checkpoint=prior, public_run=str(public), public_gates=5,
    explicit_reports=report['individual_reports'], board_prefix='current-board-staged-child-',
    old_non_audit_source_files_byte_exact=6194, entire_previous_resource_owner_byte_exact=True,
    old_audit_bytes_after_four_ordinary_imports=True,
    known_cumulative_tmp_removed_bytes=cleanup['cumulative_removed_bytes'],
    primary_usage_percent=usage['rate_limits']['primary']['used_percent'], primary_usage_checked_at=usage['timestamp'],
    whole_worker_expanded_birth_history_proved=True, original_906_statement_and_every_old_proof_preserved=True,
    actual_parked_suffix_same_original_output_kept_proved=True,
    same_snapshot_one_arrow_bucket_conditional_recompletion_proved=True,
    source_raw_target_compatibility_producer_proved=False, all_historical_same_output_attachment_proved=False,
    retained_core_obligations_guardsHold_proved=False, source_pending_Profile_closure_proved=False,
    compiled_haskell_correspondence_proved=False, indexed_captured_invocation_relation_and_producer_proved=True, every_staged_child_position_incidence_proved=True,
    output_equality_alone_does_not_identify_invocation=True, goal_active=True,
    prior_immutable_archive='20261116-indexed-invocation-checkpoint')
(work / 'checkpoint-config.json').write_text(json.dumps(config, indent=2) + '\n')
cut = datetime.datetime(2026, 11, 16, 22, 14, 0,
                        tzinfo=datetime.timezone(datetime.timedelta(hours=1))).timestamp()
selected, skipped = [], []
for path in base.iterdir():
    if not path.is_dir() or not path.name.startswith('20261116-'):
        continue
    relative = str(path.relative_to(root))
    if 'checkpoint' in path.name or path.stat().st_mtime < cut or path.name == old.name:
        skipped.append(relative)
    else:
        selected.append(relative)
assert len(selected) == 17, selected
assert str(work.relative_to(root)) in selected and str(public.relative_to(root)) in selected
(work / 'archive-roots.json').write_text(json.dumps(sorted(selected), indent=2) + '\n')
(work / 'skipped-published-roots.json').write_text(json.dumps(sorted(skipped), indent=2) + '\n')
(work / 'selection-review.json').write_text(json.dumps({'prior_checkpoint': prior, 'selected_roots': len(selected),
    'policy': 'Lossless new proof inputs, all failed checks, exact repairs, prospective headers, full publication drivers and marked invocation/alias targets. Earlier immutable archives remain unchanged.',
    'prior_push_receipt_copied_to_new_work': True, 'nine_new_reports_are_theorem_reports': True,
    'compiler_running_markers_are_not_liveness_evidence': True, 'no_compiled_objects_or_import_overlays': True}, indent=2) + '\n')
fields = {'SOURCE_FILES': report['source_files'], 'AUDIT_IMPORTS': report['direct_audit_imports'],
          'AUDIT_REPORTS': report['individual_reports'], 'STANDARD_REPORTS': report['checks'][-1]['axiom_groups'],
          'FREE_REPORTS': report['checks'][-1]['axiom_free_reports'], 'INDEPENDENT_REPORTS': report['independent_reports'],
          'RESOURCE_REPORTS': report['resource_and_component_probes'], 'OWNER_REPORTS': report['owner_resource_probes'],
          'RESOURCE_STANDARD': report['checks'][1]['axiom_groups'], 'RESOURCE_FREE': report['checks'][1]['axiom_free_reports'],
          'THEOREMS': report['audited_theorems'], 'OLD_SOURCES': 6194,
          'CLEANUP': cleanup['cumulative_removed_bytes'], 'USAGE': config['primary_usage_percent']}
note = (work / 'checkpoint-note.md').read_text()
for key, value in fields.items():
    note = note.replace('{{' + key + '}}', str(value))
(work / 'checkpoint-note.md').write_text(note)
for name in ['assemble.py', 'finalize.py', 'verify.py']:
    text = (old / name).read_text().replace('20261116-indexed-invocation-checkpoint', packet_name)
    text = text.replace('eb1b0554f93b01bc067458e7c5bff6c9aea5caca', prior)
    text = text.replace('# Concrete indexed eager callback invocations', '# Specified staged child incidence and raw alias growth')
    (work / name).write_text(text)
print(json.dumps({'checked_code': code, 'packet': packet_name, 'roots': len(selected)}))
