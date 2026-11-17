from pathlib import Path
import datetime
import hashlib
import json

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
check = work.parent / '20261117-current-source-arrow-invocation-suspended-vars-scope-check'
result = json.loads((check / 'checked.json').read_text())
assert all(result['passed'])
assert len(result['checks']) == 2
assert all(c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics']
           and not c['sorryAx'] for c in result['checks'])
sha = lambda data: hashlib.sha256(data).hexdigest()
owner_name = 'lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
owner_receipt = json.loads((work / 'OWNER-NORMAL-STAGING.json').read_text())
for name, digest in json.loads((check / 'source-pins.json').read_text()).items():
    data = (root / name).read_bytes()
    if name == owner_name and digest == owner_receipt['old_owner_sha256']:
        assert sha(data) == owner_receipt['assembled_sha256']
    else:
        assert sha(data) == digest, name
selection = json.loads((check / 'selection.json').read_text())
assert selection['module'] == 'SourceSynthesisCurrentUniverseArrowInvocationProvenance'
packet = work.parent / selection['packet']
raw = (packet / (selection['module'] + '.lean')).read_bytes()
assert sha(raw) == selection['sha256']
assert b'set_option maxHeartbeats' not in raw
target = root / 'lean/MicroCFTA' / (selection['module'] + '.lean')
assert not target.exists()
target.write_bytes(raw)
receipt = dict(selection)
receipt.update(at=datetime.datetime.now().astimezone().isoformat(), normal_check=check.name,
    source_path=str(target.relative_to(root)), public_sha256=sha(raw),
    checked_raw_and_normal_bytes_identical=True, new_public_theorems=1,
    original_source_arrow_staged_provenance_proved=True,
    actual_type_marker_role_preservation_proved=False,
    same_original_runtime_fuels=True, joint_finite_completion_proved=False,
    haskell_changed=False)
(work / 'LEAF-NORMAL-STAGING.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt))
