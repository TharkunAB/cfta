from pathlib import Path
import hashlib
import json
import subprocess

root=Path('/home/tritlo/Code/mcfta')
base=root/'lean/restart-evidence'
work=Path(__file__).parent
specs=[
 ('20261116-current-real-actual-source-rows-resources-draft','APPEND.lean.txt','PROBES.lean.txt','43080aca881ea214f396de31ca75591a5b622de8c0e5667a9cff751964f8c492'),
 ('20261116-current-real-worker-full-resources-configuration-repair','APPEND-CORE.lean.txt','PROBES-CORE.lean.txt','0692c269dce441fb799b46f65188d11b881e40371d95e881d5898ee527d958eb'),
 ('20261116-current-real-opaque-and-prepared-resources-draft','APPEND.lean.txt','PROBES-APPEND.lean.txt','caefccbd1c5d6d9c60524d8d99b3887414a67c5961a9a91d13750f32198665c2')]
raws=[];probes=[(work/'TaskRepair105Probes.lean.txt').read_bytes()];inputs=[]
for folder,raw,probe,digest in specs:
    p=base/folder;data=(p/raw).read_bytes()
    assert hashlib.sha256(data).hexdigest()==digest
    raws.append(data);probes.append((p/probe).read_bytes());inputs += [p/raw,p/probe]
(work/'ROWS-CORE-BRIDGES-APPEND.lean.txt').write_bytes(b'\n'.join(raws))
(work/'Task126Probes.lean.txt').write_bytes(b'\n'.join(probes))
assert (work/'Task126Probes.lean.txt').read_bytes().count(b'#print axioms ')==126
builder=base/'20261116-real-prefix-all-outcome-checkpoint-work/prepare-consumer-unique.py'
run=base/'20261116-native-real-rows-task-core-and-bridges-check'
subprocess.run(['python3',str(builder),'--run',run.name,'--spec',
    work.name+':ROWS-CORE-BRIDGES-APPEND.lean.txt:Task126Probes.lean.txt'],check=True)
pins=json.loads((run/'source-pins.json').read_text())
for p in [Path(__file__),*inputs]:
    pins[str(p.relative_to(root))]=hashlib.sha256(p.read_bytes()).hexdigest()
(run/'source-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
