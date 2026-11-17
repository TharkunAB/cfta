from pathlib import Path
import datetime
import hashlib
import json

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
run = json.loads((work / 'CHECK-TO-INSTALL.json').read_text())['run']
check = work.parent / run
result = json.loads((check / 'checked.json').read_text())
assert all(result['passed']) and result['all_history9374_proved']
assert len(result['checks']) == 2
assert all(c['exit'] == 0 and not c['nonstandard_axioms'] and not c['diagnostics']
           and not c['sorryAx'] for c in result['checks'])
sha = lambda data: hashlib.sha256(data).hexdigest()
for name, digest in json.loads((check / 'source-pins.json').read_text()).items():
    assert sha((root / name).read_bytes()) == digest, name
selection = json.loads((check / 'selection.json').read_text())
owner = root / selection['owner']
before = owner.read_bytes()
assert sha(before) == selection['old_owner_sha256']
prefix = (check / 'IMPORT-PREFIX.lean.txt').read_bytes()
append = (check / 'APPEND.lean.txt').read_bytes()
checked_after = prefix + before + b'\n' + append
assert sha(checked_after) == selection['assembled_sha256']
assert checked_after[len(prefix):len(prefix) + len(before)] == before
header = (work.parent / selection['packets'][-1] / 'PUBLIC-9374-HEADER.lean.txt').read_bytes()
assert sha(header) == '9374c81a8218909c2d86a7a2737bc0ac91396e1a850362aa835447341cfa47a8'
assert header.rstrip(b'\n') + b' := by\n' in append
historical_status = b'-- OPEN target. No proof, axiom or theorem declaration is installed.\n'
assert header.startswith(historical_status)
assert checked_after.count(historical_status) == 1
after = checked_after.replace(historical_status, b'', 1)
assert header[len(historical_status):].rstrip(b'\n') + b' := by\n' in after
all_probes = (check / 'NEW-PROBES.lean.txt').read_bytes()
public = (b'\n#check @MicroCFTA.SourcePruningEnumerationParkedOuterHeldHistory.'
          b'actual_parked_all_later_outer_entries_held_history\n'
          b'#print axioms MicroCFTA.SourcePruningEnumerationParkedOuterHeldHistory.'
          b'actual_parked_all_later_outer_entries_held_history\n')
boundary = b'namespace MicroCFTA.SourcePruningEnumerationParkedOuterHeldHistory\n'
assert all_probes.count(boundary) == 1
private = all_probes[:all_probes.index(boundary)]
assert private.count(b'#print axioms ') == 9
assert public.count(b'#print axioms ') == 1
(work / 'PUBLIC-PROBES.lean.txt').write_bytes(public)
(work / 'PRIVATE-PROBES.lean.txt').write_bytes(private)
owner.write_bytes(after)
receipt = dict(selection)
receipt.update(at=datetime.datetime.now().astimezone().isoformat(), normal_check=run,
    source_changed=True, public_reports=1, private_reports=9,
    checked_assembled_sha256=selection['assembled_sha256'], assembled_sha256=sha(after),
    historical_open_comment_removed=True, normal_source_otherwise_byte_exact=True,
    public9374_header_byte_exact=False, public9374_theorem_declaration_byte_exact=True,
    same_original_runtime_fuels=True,
    all_history9374_proved=True, joint_finite_completion_proved=False,
    haskell_changed=False)
(work / 'OWNER-NORMAL-STAGING.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt))
