from pathlib import Path
import hashlib
import json
import subprocess

root=Path('/home/tritlo/Code/mcfta')
base=root/'lean/restart-evidence'
work=Path(__file__).parent
nil=base/'20261116-current-real-actual-source-tuple-nil-fits-name-repair'
cons=base/'20261116-current-real-actual-source-tuple-cons-resources-draft'
assert hashlib.sha256((nil/'APPEND.lean.txt').read_bytes()).hexdigest()=='d1f496c20982c36afdf31bce5e6c3c4e9d126c27dd8ce8f6c0fbcda83ce76b3e'
assert hashlib.sha256((cons/'APPEND.lean.txt').read_bytes()).hexdigest()=='7bda5a53b542077f7a2f3cfe173d2c01fcff3dd65aa5b04e24a3f147edaea9e4'
(work/'TUPLE-APPEND.lean.txt').write_bytes((nil/'APPEND.lean.txt').read_bytes()+b'\n'+(cons/'APPEND.lean.txt').read_bytes())
probes=(base/'20261116-real-worker-assembly-publication/ResourceProbes.lean.txt').read_bytes()
assert probes.count(b'#print axioms ')==89
probes+=b'\n'+(nil/'PROBES.lean.txt').read_bytes()+b'\n'+(cons/'PROBES.lean.txt').read_bytes()
assert probes.count(b'#print axioms ')==101
(work/'Tuple101Probes.lean.txt').write_bytes(probes)
builder=base/'20261116-real-prefix-all-outcome-checkpoint-work/prepare-consumer-unique.py'
run=base/'20261116-native-real-source-tuple-nil-and-cons-check'
subprocess.run(['python3',str(builder),'--run',run.name,'--spec',
    work.name+':TUPLE-APPEND.lean.txt:Tuple101Probes.lean.txt'],check=True)
pins=json.loads((run/'source-pins.json').read_text())
for p in [Path(__file__),nil/'APPEND.lean.txt',nil/'PROBES.lean.txt',cons/'APPEND.lean.txt',cons/'PROBES.lean.txt']:
    pins[str(p.relative_to(root))]=hashlib.sha256(p.read_bytes()).hexdigest()
(run/'source-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
