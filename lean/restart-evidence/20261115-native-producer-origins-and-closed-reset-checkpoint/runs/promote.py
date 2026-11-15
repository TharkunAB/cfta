from pathlib import Path
import datetime
import hashlib
import json
import shutil
import subprocess

work = Path(__file__).parent
base = 'f7c8de38c27fced37fe893a11d8aa645b866a328'
assert subprocess.check_output(['git', 'rev-parse', 'HEAD']).decode().strip() == base
specs = [
    ('20261115-current-node-return-finish-origin-true-normalization-repair', 'SourceCurrentAllocatedNativeNodeReturnOrigin',
     '2e5e14dbef201e24fa95fbcc0560fe7ddb378708d9d76940e36fd2cdae44678f', 'returned_node_cell_finish_prefix'),
    ('20261115-current-edge-return-finish-origin-draft', 'SourceCurrentAllocatedNativeEdgeReturnOrigin',
     '9d0d298f4576bcd3fd6b0dc04b4427e5f12de946084738a51bceb16e94a6bbfd', 'returned_edge_cell_finish_prefix'),
    ('20261115-general-closed-native-reset-proof-repair', 'SourceCurrentAllocatedNativeClosedResetProfile',
     '6d43d8f1e4911a91f8c973fb79c156884a22cda6da3015f936a26f8a99977a5b', 'closed_reset_query_profile_of_fuel_induction'),
    ('20261115-current-finite-prefix-reference-control-draft', 'SourceCurrentAllocatedNativeFinitePrefixReferenceControl',
     '86ac45b3789bc44d3d0465401d5d3f612bd5be1a307a0a2e2490df675de1f304', 'current_stored_universe_ref_control_at_finite_prefix'),
]
promotion = []
for folder, module, digest, statement in specs:
    raw = Path('lean/restart-evidence') / folder / (module + '.lean')
    assert hashlib.sha256(raw.read_bytes()).hexdigest() == digest
    public = Path('lean/MicroCFTA') / raw.name
    assert not public.exists()
    shutil.copyfile(raw, public)
    promotion.append({'module': module, 'raw': str(raw), 'sha256': digest, 'public_statements': [statement]})
status = {
    'at': datetime.datetime.now().astimezone().isoformat(), 'base': base, 'goal_active': True,
    'new_modules': 4, 'new_statements': 4, 'strict_private_passes': [60875, 74602],
    'public_gates_pending': True, 'dispatch_ancestry_repair_pending': True,
    'general_native_C_M_history_proved': False, 'joint_finite_completion_proved': False,
    'haskell_changed': False, 'root_sole_compiler': True,
    'initial_promotion_assembly_syntax_error_ran_no_code': True,
}
for name, value in [('promotion.json', promotion), ('WIP.json', status)]:
    (work / name).write_text(json.dumps(value, indent=2) + '\n')
shutil.copyfile('lean/restart-evidence/20261115-native-body-first-outer-history-checkpoint-work/prepare-private.py',
                work / 'prepare-private.py')
print(json.dumps({'promoted_exact_modules': len(promotion), 'work': str(work)}))
