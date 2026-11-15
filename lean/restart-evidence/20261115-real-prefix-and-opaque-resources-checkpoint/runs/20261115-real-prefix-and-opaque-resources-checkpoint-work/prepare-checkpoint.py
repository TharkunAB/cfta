from pathlib import Path
import datetime
import json
import subprocess

work = Path(__file__).parent
evidence = Path('lean/restart-evidence')
packet = '20261115-real-prefix-and-opaque-resources-checkpoint'
prior_packet = '20261115-actual-source-task-scan-checkpoint'
prior_work = evidence / '20261115-actual-source-resource-induction-checkpoint-work'
base = '8f71f92d7e99b361ae664b4bcee721afd4e334d3'
code = '6efb9f31a15df30731fe1849b8db5b31cf0fc0d4'
assert subprocess.check_output(['git', 'rev-parse', 'HEAD']).decode().strip() == code
public = evidence / '20261115-real-prefix-and-opaque-publication'
result = json.loads((public / 'checked.json').read_text())
assert len(result['checks']) == 5
assert all(x['exit'] == 0 and not x['nonstandard_axioms'] for x in result['checks'])
config = dict(result, checked_code=code, prior_checkpoint=base,
    public_run=str(public.resolve()), public_gates=5, explicit_reports=409,
    source_files=6120, direct_audit_imports=5120, board_prefix='current-board-public-',
    original_real_prefix_header='9485965762b92593e8453286d6eb67c2fe1541e832f0cf74b0687477b91ccbc2',
    old_owner_body_preserved_byte_exact=True, other_old_source_files_byte_exact=6117,
    native_CM_memo_history_all_actual_prefixes_proved=True,
    native_query_scope='One literal initial node query; both complete memo families initially empty; qualified C/M results.',
    full_scope='One finite accepted completion of each original emitted partial root under one compatible assignment, with actual domains, paths, UF aliases, residuals, readback, parked recompletion and removed historical obligations on that output branch; original fuels, budgets and emissions before later stops.')
(work / 'checkpoint-config.json').write_text(json.dumps(config, indent=2) + '\n')
previous = {Path(p).name for p in json.loads((evidence / prior_packet / 'archive-roots.json').read_text())}
prefixes = ('20261115-current-actual-source-', '20261115-current-actual-prepared-scan-',
    '20261115-current-any-budget-identity-', '20261115-native-actual-source-',
    '20261115-current-real-narrowed-prefix-', '20261115-native-real-prefix-',
    '20261115-current-opaque-receipt-shape-', '20261115-native-opaque-gate-')
roots = [str(p) for p in sorted(evidence.iterdir()) if p.is_dir()
    and p.name.startswith(prefixes) and p.name not in previous]
roots += [str(work), str(public)]
assert len(roots) == len(set(roots))
(work / 'archive-roots.json').write_text(json.dumps(roots, indent=2) + '\n')
(work / 'skipped-published-roots.json').write_text(json.dumps({
    'earlier_roots_retained_in_immutable_checkpoint': prior_packet,
    'earlier_root_count': len(previous), 'live_checker_excluded': [],
    'latest_identity_checker': 83468, 'latest_identity_checker_terminal_exit': 1,
    'latest_identity_checker_failure': 'Original 2M heartbeat normalization timeouts; no worker proof credit.'
}, indent=2) + '\n')
(work / 'selection-review.json').write_text(json.dumps({
    'selected_roots': len(roots), 'new_promoted_components_and_repair_parents_included': True,
    'prior_immutable_checkpoints_preserved': True, 'compiled_objects_excluded': True,
    'all_selected_checkers_terminal': True, 'new_agent_work_not_selected': True
}, indent=2) + '\n')
for name in ['assemble.py', 'finalize.py']:
    text = (prior_work / name).read_text().replace(prior_packet, packet)
    text = text.replace("BASE = '0e8d6e24714bca42cd96c93fa4cb33020e065006'", "BASE = '" + base + "'")
    text = text.replace('# Actual source task and prepared-scan resource checkpoint',
        '# Real-prefix and opaque-expansion resource checkpoint')
    (work / name).write_text(text)
text = (evidence / prior_packet / 'verify.py').read_text().replace(prior_packet, packet)
(work / 'verify.py').write_text(text)
(work / 'WIP.json').write_text(json.dumps({
    'at': datetime.datetime.now().astimezone().isoformat(), 'goal': 'ACTIVE',
    'previous_goal_turn': 'progress: two new resource proofs checked by all five publication gates',
    'source_code': code, 'prior_remote_checkpoint': base, 'public_gates_passed': 5,
    'publication_session': 9111, 'identity433_session': 83468, 'identity433_terminal_exit': 1,
    'whole_identity_worker_at_any_budget_proved': False, 'whole_real_worker_at_any_budget_proved': False,
    'joint_finite_completion_proved': False, 'haskell_changed': False,
    'primary_usage_percent_last_observed': 30, 'terminal_tmp_bytes_already_removed': 227063896
}, indent=2) + '\n')
print(json.dumps({'checked_code': code, 'selected_roots': len(roots), 'public_gates': 5}))
