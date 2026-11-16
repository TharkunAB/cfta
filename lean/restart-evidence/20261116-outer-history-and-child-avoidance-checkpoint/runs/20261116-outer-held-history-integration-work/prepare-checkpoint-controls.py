from pathlib import Path
import datetime
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
work = Path(__file__).parent
old = base / '20261116-genuine-worker-fragment-induction-work'
packet_name = '20261116-outer-history-and-child-avoidance-checkpoint'
prior = '2411688c163ea293794617fc447b8518b8b04377'
public = base / '20261116-full-outer-and-fragment-producer-publication'
report = json.loads((public / 'checked.json').read_text())
assert len(report['checks']) == 5
assert all(x['exit'] == 0 and not x['nonstandard_axioms'] and not x['diagnostics'] and not x['sorryAx'] for x in report['checks'])
code = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root).decode().strip()
assert code != prior, 'Commit the checked Source before the archive.'
owner_name = 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
assert subprocess.check_output(['git', 'show', code + ':' + owner_name], cwd=root) == (root / owner_name).read_bytes()
config = json.loads((old / 'checkpoint-config.json').read_text())
config.update(report)
cleanup = json.loads((work / 'terminal-cleanup-public-result.json').read_text())
config.update(
    checked_code=code, prior_checkpoint=prior, public_run=str(public), public_gates=5,
    explicit_reports=520, source_files=6173, direct_audit_imports=5173,
    board_prefix='current-board-outer-history-', new_modules=2, new_public_theorems=3,
    old_non_audit_sources_byte_exact=6169, old_owner_exact_prefixes=0,
    old_owner_entire_bytes_after_one_ordinary_import_each=0,
    old_owner_entire_bytes_after_two_ordinary_imports=1,
    known_cumulative_tmp_removed_bytes=cleanup['cumulative_removed_bytes'],
    primary_usage_percent=53, primary_usage_checked_at='2026-11-16T16:53:24.655Z',
    outer_recursive_depth_history_proved=True, outer_source_companions_unverified=False,
    full_worker_906_avoidance_proved=True, whole906_proved=True,
    captured_entry_receipt_still_needs_actual_branch_retention=False,
    pending_fragment_old_expanded_avoidance_proved=True,
    actual_child_old_expanded_avoidance_producer_proved=True,
    total_private_resource_probes=39, additional_resource_probes=40,
    new_resource_public_probe_count=1, new_private_source_components=10,
    joint_finite_completion_proved=False, all_removed_history_joint_proved=False,
    whole_warm_source_history_proved=False, source_pending_Profile_closure_proved=False,
    retained_core_obligations_guardsHold_proved=False, compiled_haskell_correspondence_proved=False,
    same_final_snapshot_recompletion_still_open=True,
    prior_immutable_archive='20261116-scoped-history-checkpoint',
    every_old_header_and_proof_preserved=True, goal_active=True)
(work / 'checkpoint-config.json').write_text(json.dumps(config, indent=2) + '\n')
old_roots = set(json.loads((old / 'archive-roots.json').read_text()))
cut = datetime.datetime(2026, 11, 16, 13, 10,
                        tzinfo=datetime.timezone(datetime.timedelta(hours=1))).timestamp()
selected = []
for p in base.iterdir():
    relative = str(p.relative_to(root))
    if not p.is_dir() or not p.name.startswith('20261116-') or relative in old_roots or 'checkpoint' in p.name:
        continue
    if p.stat().st_mtime >= cut:
        selected.append(relative)
assert str(work.relative_to(root)) in selected
(work / 'archive-roots.json').write_text(json.dumps(sorted(selected), indent=2) + '\n')
(work / 'skipped-published-roots.json').write_text(json.dumps(sorted(old_roots), indent=2) + '\n')
(work / 'selection-review.json').write_text(json.dumps({
    'prior_checkpoint': prior, 'selected_roots': len(selected),
    'policy': 'Lossless snapshot of new frozen inputs, marked drafts, failed checks, repairs, pause/resume records, public gates and controls. Preserve every earlier published archive.',
    'active_draft_snapshots_are_not_proof_credit': True,
    'compiler_running_markers_are_not_liveness_evidence': True,
    'only_raw_inputs_and_small_derived_logs_no_compiled_objects': True,
}, indent=2) + '\n')
for name in ['assemble.py', 'finalize.py', 'verify.py']:
    text = (old / name).read_text().replace('20261116-scoped-history-checkpoint', packet_name)
    text = text.replace('cae9462bd33f3f9b187b6d1b42c3b79866e0ac2c', prior)
    text = text.replace('# Actual scoped task history', '# Outer history and actual child avoidance')
    (work / name).write_text(text)
print(json.dumps({'checked_code': code, 'packet': packet_name, 'roots': len(selected)}))
