from pathlib import Path
import hashlib
import json
import subprocess

root=Path('/home/tritlo/Code/mcfta')
base=root/'lean/restart-evidence'
work=Path(__file__).parent
scan=base/'20261116-current-real-worker-scan-row-factoring-draft'
bridges=base/'20261116-current-real-opaque-prepared-typing-repair'
depth=base/'20261116-current-real-worker-depth-fold-and-opacity-repair'
whole=(bridges/'APPEND.lean.txt').read_text()
at=whole.index('private theorem real_actual_successful_prepared_emitted_complete_at_any_budget')
doc=whole.rfind('/--',0,at)
if doc>=0 and whole[doc:at].count('-/')==1:at=doc
tail=whole[at:]
assert tail.count('private theorem ')==2
two=(bridges/'PREAMBLE.lean.txt').read_text()+tail
(work/'BRIDGES-TWO-APPEND.lean.txt').write_text(two)
bridge_probes=(bridges/'PROBES-APPEND.lean.txt').read_bytes().splitlines(keepends=True)
bridge_probes=b''.join(x for x in bridge_probes if b'real_actual_opaque_terminal_resources_at_any_budget' not in x)
(work/'BridgesTwoProbes.lean.txt').write_bytes(bridge_probes)
specs=[(scan/'APPEND-SCAN.lean.txt',scan/'PROBES-SCAN.lean.txt',
        'd4bd6271cd797ad6ff91ba8dc4e7eadaf2978f6debaeebf7a92e935c94ecf8bb'),
       (work/'BRIDGES-TWO-APPEND.lean.txt',work/'BridgesTwoProbes.lean.txt',None),
       (depth/'APPEND.lean.txt',depth/'PROBES.lean.txt',
        '16f3b5ee1c1068070d6a8f7278786f070d5da7d853c4fdda1c2034ba555f7565')]
raws=[];probes=[(work/'Task123Probes.lean.txt').read_bytes()];inputs=[]
for raw,probe,digest in specs:
    data=raw.read_bytes()
    if digest:assert hashlib.sha256(data).hexdigest()==digest
    raws.append(data);probes.append(probe.read_bytes());inputs += [raw,probe]
(work/'SCAN-BRIDGES-DEPTH-APPEND.lean.txt').write_bytes(b'\n'.join(raws))
(work/'WholeReal136Probes.lean.txt').write_bytes(b'\n'.join(probes))
assert (work/'WholeReal136Probes.lean.txt').read_bytes().count(b'#print axioms ')==136
builder=base/'20261116-real-prefix-all-outcome-checkpoint-work/prepare-consumer-unique.py'
run=base/'20261116-native-whole-real-worker-factored-scan-check'
subprocess.run(['python3',str(builder),'--run',run.name,'--spec',
    work.name+':SCAN-BRIDGES-DEPTH-APPEND.lean.txt:WholeReal136Probes.lean.txt'],check=True)
source=run/'candidate-0/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
imports=depth/'IMPORTS.lean.txt'
source.write_bytes(imports.read_bytes()+b'\n'+source.read_bytes())
assert json.loads((work/'DEPTH-IMPORT-DAG.json').read_text())['no_owner_cycle']
pins=json.loads((run/'source-pins.json').read_text())
for p in [Path(__file__),source,imports,bridges/'APPEND.lean.txt',bridges/'PREAMBLE.lean.txt',
    bridges/'PROBES-APPEND.lean.txt',work/'DEPTH-IMPORT-DAG.json',*inputs]:
    pins[str(p.relative_to(root))]=hashlib.sha256(p.read_bytes()).hexdigest()
(run/'source-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
