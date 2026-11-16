from pathlib import Path
import datetime
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
work = Path(__file__).parent
old = base / '20261116-outer-held-history-integration-work'
prior = '21a2175fc27a8015504094f901d3dd81f23b49d5'
packet_name = '20261116-same-snapshot-recompletion-checkpoint'
public = base / '20261116-same-snapshot-recompletion-publication'
report = json.loads((public / 'checked.json').read_text())
assert len(report['checks']) == 5
assert all(x['exit'] == 0 and not x['nonstandard_axioms'] and not x['diagnostics'] and not x['sorryAx'] for x in report['checks'])
code = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root).decode().strip()
assert code != prior, 'Commit the checked Source before the archive.'
for name in ['SourcePruningEnumerationSharedEagerReservation.lean', 'Audit.lean', 'SourcePruningEnumerationArrowBucketRecompletion.lean']:
    relative = 'lean/MicroCFTA/' + name
    assert subprocess.check_output(['git', 'show', code + ':' + relative], cwd=root) == (root / relative).read_bytes()
cleanup = json.loads((work / 'terminal-cleanup-result.json').read_text())
usage = json.loads((work / 'USAGE.json').read_text())
config = dict(report)
config.update(
    checked_code=code, prior_checkpoint=prior, public_run=str(public), public_gates=5,
    explicit_reports=report['individual_reports'], board_prefix='current-board-recompletion-',
    old_non_audit_sources_byte_exact=6171,
    old_owner_entire_bytes_after_two_ordinary_imports=1,
    known_cumulative_tmp_removed_bytes=cleanup['cumulative_removed_bytes'],
    primary_usage_percent=usage['rate_limits']['primary']['used_percent'],
    primary_usage_checked_at=usage['timestamp'],
    full_worker_906_avoidance_proved=True, every_old_header_and_proof_preserved=True,
    current_native_domains_and_guards_preserved_by_recompletion=False,
    same_snapshot_one_arrow_bucket_conditional_recompletion_proved=True,
    source_raw_target_compatibility_producer_proved=False,
    retained_core_obligations_guardsHold_proved=False,
    whole_warm_source_history_proved=False, source_pending_Profile_closure_proved=False,
    compiled_haskell_correspondence_proved=False, goal_active=True,
    benchmark_pause_message_received_after_deadline=True,
    prior_immutable_archive='20261116-outer-history-and-child-avoidance-checkpoint')
(work / 'checkpoint-config.json').write_text(json.dumps(config, indent=2) + '\n')
cut = datetime.datetime(2026, 11, 16, 18, 20,
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
    'policy': 'Lossless new frozen inputs, marked drafts, failed checks, repairs, public gates and controls. Preserve all earlier immutable archives.',
    'active_draft_snapshots_are_not_proof_credit': True,
    'compiler_running_markers_are_not_liveness_evidence': True,
    'only_raw_inputs_and_small_derived_logs_no_compiled_objects': True,
}, indent=2) + '\n')
note = (work / 'checkpoint-note.md').read_text()
note = note.replace('{{THEOREMS}}', str(report['audited_theorems']))
note = note.replace('{{CLEANUP}}', str(cleanup['cumulative_removed_bytes']))
note = note.replace('{{USAGE}}', str(config['primary_usage_percent']))
(work / 'checkpoint-note.md').write_text(note)
for name in ['assemble.py', 'finalize.py', 'verify.py']:
    text = (old / name).read_text().replace('20261116-outer-history-and-child-avoidance-checkpoint', packet_name)
    text = text.replace('2411688c163ea293794617fc447b8518b8b04377', prior)
    text = text.replace('# Outer history and actual child avoidance', '# Same-snapshot recompletion and actual finalizer levels')
    (work / name).write_text(text)
print(json.dumps({'checked_code': code, 'packet': packet_name, 'roots': len(selected)}))
