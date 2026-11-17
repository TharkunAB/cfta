from pathlib import Path
import datetime
import hashlib
import json
import sys

root = Path('/home/tritlo/Code/mcfta')
base = root / 'lean/restart-evidence'
work = Path(__file__).parent
key, session = sys.argv[1:]
run = base / ('20261117-closed-root-chain-' + key + '-check')
input_dir = base / ('20261117-closed-root-chain-' + key + '-check-input')
sha = lambda data: hashlib.sha256(data).hexdigest()
pins = json.loads((run / 'source-pins.json').read_text())
for name, digest in pins.items():
    assert sha((root / name).read_bytes()) == digest, name
report = json.loads((run / 'checked.json').read_text())
assert report['normal_module_checked'] and all(report['passed'])
assert report['checks'][-1]['total_axiom_reports'] == 1
assert all(c['exit'] == 0 and not c['diagnostics'] and not c['sorryAx']
           and not c['nonstandard_axioms'] for c in report['checks'])
binding = json.loads((input_dir / 'ORIGINAL-PACKET-BINDING.json').read_text())
assert binding['key'] == key
owner = root / binding['owner']
old = owner.read_bytes()
assert sha(old) == binding['base_sha256']
raw = (input_dir / owner.name).read_bytes()
assert sha(raw) == binding['raw_sha256'] and raw.startswith(old)
snapshot = (work / (owner.stem + '-BEFORE.lean.txt')).read_bytes()
assert raw.startswith(snapshot)
receipt = work / ('CHAIN-' + key + '-VERIFIED.json')
assert not receipt.exists()
owner.write_bytes(raw)
out = {'at': datetime.datetime.now().astimezone().isoformat(),
       'key': key, 'run': run.name, 'actual_session': int(session),
       'actual_terminal_exit': 0, 'source_pins_reverified': len(pins),
       'checks': report['checks'], 'source_path': binding['owner'],
       'raw_sha256': sha(raw), 'immediate_old_prefix_bytes': len(old),
       'baseline_old_prefix_bytes': len(snapshot), 'baseline_old_prefix_exact': True,
       'original_header_file_sha256': binding['original_header_file_sha256'],
       'physical_interface_only': True, 'joint_finite_completion_proved': False,
       'haskell_changed': False}
receipt.write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps(out))
