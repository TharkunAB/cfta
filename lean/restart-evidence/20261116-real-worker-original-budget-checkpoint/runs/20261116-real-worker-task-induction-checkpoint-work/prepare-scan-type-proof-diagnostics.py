from pathlib import Path
import hashlib
import json
import subprocess

root=Path('/home/tritlo/Code/mcfta')
base=root/'lean/restart-evidence'
packet=base/'20261116-current-real-worker-scan-statement-proof-diagnostics'
run=base/'20261116-native-real-scan-statement-versus-proof-check'
builder=base/'20261116-real-prefix-all-outcome-checkpoint-work/prepare-consumer-unique.py'
specs=[('APPEND-HEADER-TYPE-ONLY.lean.txt','PROBES-TYPE-ONLY.lean.txt',124),
    ('APPEND-SCAN-DIAGNOSTIC.lean.txt','PROBES-125.lean.txt',125)]
args=['python3',str(builder),'--run',run.name]
for raw,probe,count in specs:
    assert (packet/probe).read_bytes().count(b'#print axioms ')==count
    args += ['--spec',packet.name+':'+raw+':'+probe]
subprocess.run(args,check=True)
pins=json.loads((run/'source-pins.json').read_text())
pins[str(Path(__file__).relative_to(root))]=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
(run/'source-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
