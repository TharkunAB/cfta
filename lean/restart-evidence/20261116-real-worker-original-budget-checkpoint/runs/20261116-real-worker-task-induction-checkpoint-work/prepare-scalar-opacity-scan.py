from pathlib import Path
import hashlib
import json
import subprocess

root=Path('/home/tritlo/Code/mcfta')
base=root/'lean/restart-evidence'
packet=base/'20261116-current-real-worker-scan-target-scalar-opacity-repair'
raw=packet/'APPEND-SCAN.lean.txt'
assert hashlib.sha256(raw.read_bytes()).hexdigest()=='d9707d0ff7dcf8a6218e82bd865509daa7e61380ca57320db1eb287720398856'
probe=packet/'PROBES-125.lean.txt'
assert probe.read_bytes().count(b'#print axioms ')==125
run=base/'20261116-native-real-scan-scalar-opacity-check'
builder=base/'20261116-real-prefix-all-outcome-checkpoint-work/prepare-consumer-unique.py'
subprocess.run(['python3',str(builder),'--run',run.name,'--spec',
    packet.name+':'+raw.name+':'+probe.name],check=True)
pins=json.loads((run/'source-pins.json').read_text())
pins[str(Path(__file__).relative_to(root))]=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
(run/'source-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
