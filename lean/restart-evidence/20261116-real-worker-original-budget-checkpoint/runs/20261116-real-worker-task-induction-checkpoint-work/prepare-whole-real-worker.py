from pathlib import Path
import hashlib
import json
import subprocess

root=Path('/home/tritlo/Code/mcfta')
base=root/'lean/restart-evidence'
work=Path(__file__).parent
specs=[
 ('20261116-current-real-actual-source-rows-plan-and-helper-repair','APPEND.lean.txt','PROBES.lean.txt','fc4082c07aa96dfae5f1c879276f98d47830c2c1fd96a012b1847028a6098f5f'),
 ('20261116-current-real-worker-scan-head-opacity-repair','APPEND-CORE.lean.txt','PROBES-CORE.lean.txt','5710f83f812907c2ce2bf134e95c98046453736b17347dd15ea402faa0e8fda8'),
 ('20261116-current-real-opaque-prepared-typing-repair','APPEND.lean.txt','PROBES-APPEND.lean.txt','ba3c1b47e2c5186afde3af7b0d3bdab7196a4977d5dad09975472b48594b4917'),
 ('20261116-current-real-worker-depth-explicit-typing-draft','APPEND.lean.txt','PROBES.lean.txt','a0b24626f2d0463e9baaa733fe57f50ba0d64a773f0d836b08fd77de3852b5f8')]
raws=[];probes=[(work/'TaskRepair105Probes.lean.txt').read_bytes()];inputs=[]
for folder,raw,probe,digest in specs:
    p=base/folder;data=(p/raw).read_bytes()
    assert hashlib.sha256(data).hexdigest()==digest
    raws.append(data);probes.append((p/probe).read_bytes());inputs += [p/raw,p/probe]
(work/'WHOLE-REAL-APPEND.lean.txt').write_bytes(b'\n'.join(raws))
(work/'WholeReal135Probes.lean.txt').write_bytes(b'\n'.join(probes))
assert (work/'WholeReal135Probes.lean.txt').read_bytes().count(b'#print axioms ')==135
builder=base/'20261116-real-prefix-all-outcome-checkpoint-work/prepare-consumer-unique.py'
run=base/'20261116-native-whole-real-worker-original-budget-check'
subprocess.run(['python3',str(builder),'--run',run.name,'--spec',
    work.name+':WHOLE-REAL-APPEND.lean.txt:WholeReal135Probes.lean.txt'],check=True)
source=run/'candidate-0/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
imports=base/specs[-1][0]/'IMPORTS.lean.txt'
source.write_bytes(imports.read_bytes()+b'\n'+source.read_bytes())
assert json.loads((work/'DEPTH-IMPORT-DAG.json').read_text())['no_owner_cycle']
pins=json.loads((run/'source-pins.json').read_text())
for p in [Path(__file__),source,imports,work/'DEPTH-IMPORT-DAG.json',*inputs]:
    pins[str(p.relative_to(root))]=hashlib.sha256(p.read_bytes()).hexdigest()
(run/'source-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
