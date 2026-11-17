from pathlib import Path
from datetime import datetime
import hashlib
import json

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
work = Path(__file__).parent
sha = lambda data: hashlib.sha256(data).hexdigest()
owner_run = base / '20261117-whole-event-held-elaboration-repair-check'
marker_run = base / '20261117-terminal-marker-native-restriction-explicit-raw-check'
predicate_run = base / '20261117-whole-event-entry-protection-check'
recovered = json.loads((owner_run / 'RECOVERED-VERIFICATION.json').read_text())
assert recovered['owner_append_checked'] and recovered['compiler_exit'] == 0
assert recovered['scope_observed_inactive'] and recovered['wrapper_exit'] == 143
assert not recovered['original_driver_completed']
for run in [owner_run, marker_run, predicate_run]:
    if run != owner_run:
        assert all(json.loads((run / 'checked.json').read_text())['passed'])
    for name, digest in json.loads((run / 'source-pins.json').read_text()).items():
        assert sha((root / name).read_bytes()) == digest, (run.name, name)
baseline = json.loads((work / 'baseline-source-pins.json').read_text())
assert len(baseline) == 6239
for name, digest in baseline.items():
    assert sha((root / name).read_bytes()) == digest, name
owner = root / 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
old = owner.read_bytes()
assert sha(old) == '25a69789eb205f5c0787902786114b3cead00f30ad8f8570b3e6d51a7f84f8fc'
selection = json.loads((owner_run / 'selection.json').read_text())
assert selection['reports'] == 250 and selection['previous_owner_reports'] == 235
checked = (owner_run / 'source/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean').read_bytes()
prefix = checked[:selection['old_owner_offset']]
assert sha(prefix) == selection['import_prefix_sha256']
append = b''.join(b'\n' + (base / name / 'APPEND.lean.txt').read_bytes()
                  for name in selection['packets'])
raw_owner = prefix + old + append
assert sha(raw_owner) == selection['assembled_sha256']
assert checked.startswith(raw_owner + b'\n')
comment = b'-- Prospective owner-local export. No proof is installed in normal Source.\n'
assert append.count(comment) == 1
normal_owner = prefix + old + append.replace(comment, b'', 1)
assert normal_owner[len(prefix):len(prefix) + len(old)] == old
owner_header = (base / '20261117-whole-event-parked-public-wrapper-draft/PUBLIC-HEADER.lean.txt').read_bytes()
assert sha(owner_header) == 'd0fb640c5a500da5992d505607fc5f15ee2030302d056c83dfc102f92f2f0d94'
assert owner_header.replace(comment, b'', 1).strip() in normal_owner
marker_packet = base / '20261117-terminal-marker-native-restriction-explicit-raw-repair'
module = 'SourceSynthesisCurrentUniverseTerminalMarkerNativeRestriction'
raw_marker = (marker_packet / (module + '.lean')).read_bytes()
assert sha(raw_marker) == '9393a9e5a2d322061985e63ce3fdbb6b03baf355ffa1f4d28e0936a9fa065369'
marker_header = (marker_packet / 'PUBLIC-HEADER.lean.txt').read_bytes()
assert sha(marker_header) == 'dfbf1278db9575126bcf3e64f8d85bb979a8ca07b1c2e0a90b64a8c053c18225'
assert raw_marker.startswith(marker_header.rstrip())
open_comment = raw_marker[:raw_marker.index(b'import MicroCFTA.')]
assert open_comment.startswith(b'/- OPEN HEADER ONLY.') and open_comment.rstrip().endswith(b'-/')
normal_marker = raw_marker[len(open_comment):]
marker = root / 'lean/MicroCFTA' / (module + '.lean')
assert not marker.exists()
assert len(list((root / 'lean/MicroCFTA').glob('*.lean'))) == 6240
owner.write_bytes(normal_owner)
marker.write_bytes(normal_marker)
assert len(list((root / 'lean/MicroCFTA').glob('*.lean'))) == 6241
report = {
    'at': datetime.now().astimezone().isoformat(),
    'owner_source_path': str(owner.relative_to(root)),
    'owner_normal_check': owner_run.name,
    'owner_check_receipt': 'RECOVERED-VERIFICATION.json',
    'owner_raw_packets': selection['packets'],
    'old_owner_sha256': sha(old), 'old_owner_bytes': len(old),
    'old_owner_offset': len(prefix), 'owner_raw_sha256': sha(raw_owner),
    'owner_public_sha256': sha(normal_owner),
    'old_owner_entire_exact_contiguous_block': True,
    'old_owner_proof_bodies_and_limits_unchanged': True,
    'owner_reports': 250, 'previous_owner_reports': 235,
    'new_owner_private_reports': 14, 'new_owner_public_reports': 1,
    'owner_first_public_header_sha256': sha(owner_header),
    'marker_module': module, 'marker_packet': marker_packet.name,
    'marker_source_path': str(marker.relative_to(root)),
    'marker_normal_check': marker_run.name,
    'marker_actual_terminal_session': 32579, 'marker_actual_terminal_exit': 0,
    'marker_raw_sha256': sha(raw_marker), 'marker_public_sha256': sha(normal_marker),
    'marker_first_header_sha256': sha(marker_header),
    'only_obsolete_open_comments_removed': True,
    'new_public_theorems_including_predicate': 3,
    'all_new_owner_proof_maxHeartbeats': 200000,
    'all_old_proof_limits_unchanged': True,
    'same_original_runtime_fuels': True,
    'all_visible_operation_entries_held_proved': True,
    'marker_native_restriction_proved': True,
    'marker_native_inhabitance_proved': False,
    'source_type_marker_class_consistency_proved': False,
    'joint_finite_completion_proved': False, 'haskell_changed': False,
}
(work / 'SOURCE-NORMAL-STAGING.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
