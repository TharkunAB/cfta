from pathlib import Path
from datetime import datetime
import hashlib
import json
import sys

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
work = Path(__file__).parent
run_name, session = sys.argv[1:]
run = base / run_name
sha = lambda data: hashlib.sha256(data).hexdigest()
result = json.loads((run / 'checked.json').read_text())
assert all(result['passed']) and result['owner_append_checked']
selection = json.loads((run / 'selection.json').read_text())
new_reports = selection.get('new_component_reports', selection['new_private_reports'])
assert selection['reports'] == 226 + new_reports
for name, digest in json.loads((run / 'source-pins.json').read_text()).items():
    assert sha((root / name).read_bytes()) == digest, name
owner = root / selection['owner']
old = owner.read_bytes()
assert sha(old) == selection['old_owner_sha256']
checked_source = run / 'source/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
prefix = checked_source.read_bytes()[:selection['old_owner_offset']]
assert all(line.startswith(b'import MicroCFTA.') for line in prefix.splitlines())
assert sha(prefix) == selection['import_prefix_sha256']
raw_append = b''
normal_append = b''
comment = b'-- OPEN target. No proof or declaration is installed.\n'
wrapper = '20261117-nested-held-original-budget-wrapper-draft'
public_name = b'real_captured_invocation_nested_entries_held_at_original_budget'
public_packets = [name for name in selection['packets']
                  if public_name in (base / name / 'PROBES.lean.txt').read_bytes()]
assert len(public_packets) <= 1
public_packet = public_packets[0] if public_packets else None
public_capture = public_packet is not None
for name in selection['packets']:
    data = (base / name / 'APPEND.lean.txt').read_bytes()
    raw_append += b'\n' + data
    if name == wrapper:
        assert data.count(comment) == 1
        data = data.replace(comment, b'', 1)
    if name == public_packet:
        public_comment = b'-- OPEN prospective owner-local public export. No proof is installed.\n'
        assert data.count(public_comment) == 1
        data = data.replace(public_comment, b'', 1)
    normal_append += b'\n' + data
raw = prefix + old + raw_append
assert sha(raw) == selection['assembled_sha256']
normal = prefix + old + normal_append
offset = len(prefix)
assert normal[offset:offset + len(old)] == old
header = (base / wrapper / 'PRIVATE-HEADER.lean.txt').read_bytes()
assert sha(header) == 'c316720e0d8545211e021e1efe47dc6a743d77fa31e5d71bfe7db8a0426eab72'
assert normal.count(header.replace(comment, b'', 1)) == 1
if public_capture:
    public_header = (base / '20261117-captured-nested-ledger-public-interface-audit'
                     / 'PROSPECTIVE-PUBLIC-HEADER-UNPROVED.lean.txt').read_bytes()
    assert sha(public_header) == 'fca9b5f797cf6f335a78bde97b9b9dbadda04da1e51e9cde04f81c1705b83261'
    assert normal.count(public_header.replace(public_comment, b'', 1)) == 1
owner.write_bytes(normal)
stage = {'at': datetime.now().astimezone().isoformat(),
    'source_path': selection['owner'], 'normal_check': run_name,
    'packets': selection['packets'], 'old_owner_sha256': sha(old),
    'old_owner_bytes': len(old), 'old_owner_offset': offset,
    'assembled_raw_sha256': sha(raw), 'public_sha256': sha(normal),
    'all_owner_components_verified': True, 'owner_reports': selection['reports'],
    'new_private_components': new_reports - int(public_capture),
    'new_public_theorems': int(public_capture),
    'public_capture_export_verified': public_capture,
    'actual_terminal_session': int(session), 'terminal_exit': 0,
    'closed_c316_original_budget_proved': True,
    'original_c316_theorem_declaration_byte_exact': True,
    'c316_historical_open_comment_removed': True,
    'old_owner_proof_bodies_and_limits_unchanged': True,
    'all_new_proofs_maxHeartbeats': 200000, 'same_original_runtime_fuels': True,
    'whole_worker_joint_nested_protection_proved': False,
    'joint_finite_completion_proved': False, 'haskell_changed': False}
(work / 'OWNER-NORMAL-STAGING.json').write_text(json.dumps(stage, indent=2) + '\n')
print(json.dumps(stage))
