from pathlib import Path
import datetime
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
work = Path(__file__).parent
old = base / '20261116-same-snapshot-recompletion-work'
prior = '201a254faee6436e9172581d526f5b1e0ce44889'
packet_name = '20261116-expanded-birth-and-dependency-checkpoint'
public = base / '20261116-expanded-birth-and-actual-kept-publication'
report = json.loads((public / 'checked.json').read_text())
assert len(report['checks']) == 5
assert all(x['exit'] == 0 and not x['nonstandard_axioms'] and not x['diagnostics'] and not x['sorryAx'] for x in report['checks'])
code = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root).decode().strip()
assert code != prior, 'Commit the checked Source before the archive.'
for name in ['SourcePruningEnumerationSharedEagerReservation.lean', 'Audit.lean', 'EnumerationExpandedBirthHistory.lean', 'SourcePruningEnumerationParkedRemovedBucketInputs.lean']:
    relative = 'lean/MicroCFTA/' + name
    assert subprocess.check_output(['git', 'show', code + ':' + relative], cwd=root) == (root / relative).read_bytes()
cleanup = json.loads((work / 'terminal-cleanup-result.json').read_text())
usage = json.loads((work / 'USAGE.json').read_text())
config = dict(report)
config.update(
    checked_code=code, prior_checkpoint=prior, public_run=str(public), public_gates=5,
    explicit_reports=report['individual_reports'], board_prefix='current-board-expanded-birth-',
    old_non_audit_sources_byte_exact=6179,
    old_owner_entire_bytes_after_three_ordinary_imports=1,
    known_cumulative_tmp_removed_bytes=cleanup['cumulative_removed_bytes'],
    primary_usage_percent=usage['rate_limits']['primary']['used_percent'],
    primary_usage_checked_at=usage['timestamp'],
    full_worker_906_avoidance_proved=True, every_old_header_and_proof_preserved=True,
    same_snapshot_one_arrow_bucket_conditional_recompletion_proved=True,
    source_raw_target_compatibility_producer_proved=False,
    all_historical_same_output_attachment_proved=False,
    retained_core_obligations_guardsHold_proved=False,
    whole_warm_source_history_proved=False, source_pending_Profile_closure_proved=False,
    compiled_haskell_correspondence_proved=False, goal_active=True,
    new_private_source_components=27,
    prior_immutable_archive='20261116-same-snapshot-recompletion-checkpoint')
(work / 'checkpoint-config.json').write_text(json.dumps(config, indent=2) + '\n')
cut = datetime.datetime(2026, 11, 16, 19, 9,
                        tzinfo=datetime.timezone(datetime.timedelta(hours=1))).timestamp()
selected = []
skipped = []
for p in base.iterdir():
    if not p.is_dir() or not p.name.startswith('20261116-'):
        continue
    relative = str(p.relative_to(root))
    if 'checkpoint' in p.name or p.stat().st_mtime < cut:
        skipped.append(relative)
    else:
        selected.append(relative)
assert str(work.relative_to(root)) in selected
assert str(public.relative_to(root)) in selected
(work / 'archive-roots.json').write_text(json.dumps(sorted(selected), indent=2) + '\n')
(work / 'skipped-published-roots.json').write_text(json.dumps(sorted(skipped), indent=2) + '\n')
(work / 'selection-review.json').write_text(json.dumps({
    'prior_checkpoint': prior, 'selected_roots': len(selected),
    'policy': 'Lossless new inputs, marked drafts, failed checks, repairs, complete inner/outer drivers, clear-event export and controls. Preserve earlier immutable archives.',
    'active_draft_snapshots_are_not_proof_credit': True,
    'compiler_running_markers_are_not_liveness_evidence': True,
    'only_raw_inputs_and_small_derived_logs_no_compiled_objects': True,
    'prior_push_receipt_copied_to_new_work': True,
}, indent=2) + '\n')
note = (work / 'checkpoint-note.md').read_text()
fields = {
    '{{SOURCE_FILES}}': report['source_files'], '{{AUDIT_IMPORTS}}': report['direct_audit_imports'],
    '{{AUDIT_REPORTS}}': report['individual_reports'], '{{STANDARD_REPORTS}}': report['checks'][-1]['axiom_groups'],
    '{{INDEPENDENT_REPORTS}}': report['independent_reports'], '{{THEOREMS}}': report['audited_theorems'],
    '{{CLEANUP}}': cleanup['cumulative_removed_bytes'], '{{USAGE}}': config['primary_usage_percent'],
    '{{CLEAR_STATUS}}': 'The immediate removed-bucket pending/separation/isolation export and REAL eager restart are proved. Attaching EVERY such event to the same final output remains open.',
}
for key, value in fields.items():
    note = note.replace(key, str(value))
(work / 'checkpoint-note.md').write_text(note)
for name in ['assemble.py', 'finalize.py', 'verify.py']:
    text = (old / name).read_text().replace('20261116-same-snapshot-recompletion-checkpoint', packet_name)
    text = text.replace('21a2175fc27a8015504094f901d3dd81f23b49d5', prior)
    text = text.replace('# Same-snapshot recompletion and actual finalizer levels', '# Whole-worker birth history and actual dependency closure')
    (work / name).write_text(text)
print(json.dumps({'checked_code': code, 'packet': packet_name, 'roots': len(selected)}))
