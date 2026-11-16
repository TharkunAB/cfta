from pathlib import Path
import hashlib
import json
import subprocess

root=Path('/home/tritlo/Code/mcfta')
base=root/'lean/restart-evidence'
work=Path(__file__).parent
specs=[
 ('20261116-current-real-actual-source-rows-plan-and-helper-repair','APPEND.lean.txt','PROBES.lean.txt','fc4082c07aa96dfae5f1c879276f98d47830c2c1fd96a012b1847028a6098f5f'),
 ('20261116-current-real-worker-task-core-local-opacity-repair','APPEND-CORE.lean.txt','PROBES-CORE.lean.txt','538b7c73fb38a9bea83745425db706d0cfccbbe9cfe9ffc680b73044865b5d8f'),
 ('20261116-current-real-opaque-prepared-typing-repair','APPEND.lean.txt','PROBES-APPEND.lean.txt','ba3c1b47e2c5186afde3af7b0d3bdab7196a4977d5dad09975472b48594b4917')]
raws=[];probes=[(work/'TaskRepair105Probes.lean.txt').read_bytes()];inputs=[]
for folder,raw,probe,digest in specs:
    p=base/folder;data=(p/raw).read_bytes()
    assert hashlib.sha256(data).hexdigest()==digest
    raws.append(data);probes.append((p/probe).read_bytes());inputs += [p/raw,p/probe]
(work/'ROWS-CORE-BRIDGES-REPAIR-APPEND.lean.txt').write_bytes(b'\n'.join(raws))
(work/'TaskRepair126Probes.lean.txt').write_bytes(b'\n'.join(probes))
assert (work/'TaskRepair126Probes.lean.txt').read_bytes().count(b'#print axioms ')==126
builder=base/'20261116-real-prefix-all-outcome-checkpoint-work/prepare-consumer-unique.py'
run=base/'20261116-native-real-rows-core-opacity-and-typing-check'
subprocess.run(['python3',str(builder),'--run',run.name,'--spec',
    work.name+':ROWS-CORE-BRIDGES-REPAIR-APPEND.lean.txt:TaskRepair126Probes.lean.txt'],check=True)
pins=json.loads((run/'source-pins.json').read_text())
for p in [Path(__file__),*inputs]:
    pins[str(p.relative_to(root))]=hashlib.sha256(p.read_bytes()).hexdigest()
(run/'source-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
