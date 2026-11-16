from pathlib import Path
import hashlib
import json
import subprocess

root=Path('/home/tritlo/Code/mcfta')
base=root/'lean/restart-evidence'
work=Path(__file__).parent
nil=base/'20261116-current-real-actual-source-tuple-nil-instance-and-configuration-repair'
cons=base/'20261116-current-real-actual-source-tuple-cons-resources-draft'
assert hashlib.sha256((nil/'APPEND.lean.txt').read_bytes()).hexdigest()=='f44ba62cc3859b5b48bef5dab76dbc59931ce93c01efd353494bf76954acafdf'
assert hashlib.sha256((cons/'APPEND.lean.txt').read_bytes()).hexdigest()=='7bda5a53b542077f7a2f3cfe173d2c01fcff3dd65aa5b04e24a3f147edaea9e4'
(work/'TUPLE-REPAIR-APPEND.lean.txt').write_bytes((nil/'APPEND.lean.txt').read_bytes()+b'\n'+(cons/'APPEND.lean.txt').read_bytes())
probes=(base/'20261116-real-worker-assembly-publication/ResourceProbes.lean.txt').read_bytes()
assert probes.count(b'#print axioms ')==89
probes+=b'\n'+(nil/'PROBES.lean.txt').read_bytes()+b'\n'+(cons/'PROBES.lean.txt').read_bytes()
assert probes.count(b'#print axioms ')==101
(work/'TupleRepair101Probes.lean.txt').write_bytes(probes)
builder=base/'20261116-real-prefix-all-outcome-checkpoint-work/prepare-consumer-unique.py'
run=base/'20261116-native-real-source-tuple-instance-and-config-check'
subprocess.run(['python3',str(builder),'--run',run.name,'--spec',
    work.name+':TUPLE-REPAIR-APPEND.lean.txt:TupleRepair101Probes.lean.txt'],check=True)
pins=json.loads((run/'source-pins.json').read_text())
for p in [Path(__file__),nil/'APPEND.lean.txt',nil/'PROBES.lean.txt',cons/'APPEND.lean.txt',cons/'PROBES.lean.txt']:
    pins[str(p.relative_to(root))]=hashlib.sha256(p.read_bytes()).hexdigest()
(run/'source-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
