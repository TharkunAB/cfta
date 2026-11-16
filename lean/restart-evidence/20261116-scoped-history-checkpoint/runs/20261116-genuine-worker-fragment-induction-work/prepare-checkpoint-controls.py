from pathlib import Path
import datetime
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
work = Path(__file__).parent
old = base / '20261116-actual-frame-and-incoming-history-work'
packet_name = '20261116-scoped-history-checkpoint'
prior = 'cae9462bd33f3f9b187b6d1b42c3b79866e0ac2c'
public = base / '20261116-scoped-history-publication'
report = json.loads((public / 'checked.json').read_text())
assert len(report['checks']) == 5
assert all(x['exit'] == 0 and not x['nonstandard_axioms'] for x in report['checks'])
code = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root).decode().strip()
config = json.loads((old / 'checkpoint-config.json').read_text())
config.update(report)
config.update(checked_code=code, prior_checkpoint=prior, public_run=str(public),
              explicit_reports=517, source_files=6171, direct_audit_imports=5171,
              board_prefix='current-board-scoped-history-', new_modules=0,
              new_public_theorems=3, old_non_audit_sources_byte_exact=6168,
              old_owner_exact_prefixes=0,
              old_owner_entire_bytes_after_one_ordinary_import_each=2,
              known_cumulative_tmp_removed_bytes=2385715912,
              primary_usage_percent=40,
              primary_usage_checked_at='2026-11-16T11:31:58.396Z',
              inner_scoped_task_induction_proved=True,
              actual_scope_entry_and_nested_returns_proved=True,
              rendered_stable_full_history_proved=True,
              outer_recursive_depth_history_proved=False,
              outer_source_companions_unverified=True,
              whole906_proved=False, joint_finite_completion_proved=False,
              captured_entry_receipt_still_needs_actual_branch_retention=True)
(work / 'checkpoint-config.json').write_text(json.dumps(config, indent=2) + '\n')
old_roots = set(json.loads((old / 'archive-roots.json').read_text()))
cut = datetime.datetime(2026, 11, 16, 11, 15,
                        tzinfo=datetime.timezone(datetime.timedelta(hours=1))).timestamp()
selected = []
for p in base.iterdir():
    relative = str(p.relative_to(root))
    if not p.is_dir() or not p.name.startswith('20261116-'):
        continue
    if relative in old_roots or 'checkpoint' in p.name:
        continue
    if p.stat().st_mtime >= cut:
        selected.append(relative)
assert str(work.relative_to(root)) in selected
(work / 'archive-roots.json').write_text(json.dumps(sorted(selected), indent=2) + '\n')
(work / 'skipped-published-roots.json').write_text(json.dumps(sorted(old_roots), indent=2) + '\n')
(work / 'selection-review.json').write_text(json.dumps({
    'prior_checkpoint': prior, 'selected_roots': len(selected),
    'policy': 'Lossless snapshot of new frozen inputs, marked drafts, failed checks, repairs, public gates and controls. Preserve every prior published archive.',
    'active_draft_snapshots_are_not_proof_credit': True,
    'compiler_running_markers_are_not_liveness_evidence': True,
    'only_raw_inputs_and_small_derived_logs_no_compiled_objects': True,
}, indent=2) + '\n')
for name in ['assemble.py', 'finalize.py', 'verify.py']:
    text = (old / name).read_text().replace('20261116-actual-incoming-and-fragment-history-checkpoint', packet_name)
    text = text.replace('50fc53f75647f2b141cdddc578e75756e675dccc', prior)
    if name == 'finalize.py':
        text = text.replace('# Actual incoming and structural fragment history', '# Actual scoped task history')
    (work / name).write_text(text)
print(json.dumps({'checked_code': code, 'packet': packet_name, 'roots': len(selected)}))
