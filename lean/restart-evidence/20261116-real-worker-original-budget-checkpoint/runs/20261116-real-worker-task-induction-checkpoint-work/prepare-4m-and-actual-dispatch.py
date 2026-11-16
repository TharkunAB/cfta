from pathlib import Path
import hashlib
import json
import subprocess

root=Path('/home/tritlo/Code/mcfta')
base=root/'lean/restart-evidence'
work=Path(__file__).parent
scan=base/'20261116-current-real-worker-scan-checking-limit-4m'
bridges=base/'20261116-current-real-opaque-prepared-typing-repair'
depth=base/'20261116-current-real-worker-depth-actual-dispatch-repair'
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
        '6fa99803fbef35074851f6b42126670d7c946b76c75d3738515727f275188284'),
       (work/'BRIDGES-TWO-APPEND.lean.txt',work/'BridgesTwoProbes.lean.txt',None),
       (depth/'APPEND.lean.txt',depth/'PROBES.lean.txt',
        '613e5c88070d2b8402151ae625fe210068e78d30b3e7f70173e276611def315c')]
raws=[];probes=[(work/'Task123Probes.lean.txt').read_bytes()];inputs=[]
for raw,probe,digest in specs:
    data=raw.read_bytes()
    if digest:assert hashlib.sha256(data).hexdigest()==digest
    raws.append(data);probes.append(probe.read_bytes());inputs += [raw,probe]
(work/'SCAN-4M-ACTUAL-DISPATCH-APPEND.lean.txt').write_bytes(b'\n'.join(raws))
(work/'WholeReal4m136Probes.lean.txt').write_bytes(b'\n'.join(probes))
assert (work/'WholeReal4m136Probes.lean.txt').read_bytes().count(b'#print axioms ')==136
builder=base/'20261116-real-prefix-all-outcome-checkpoint-work/prepare-consumer-unique.py'
run=base/'20261116-native-whole-real-worker-4m-and-actual-dispatch-check'
subprocess.run(['python3',str(builder),'--run',run.name,'--spec',
    work.name+':SCAN-4M-ACTUAL-DISPATCH-APPEND.lean.txt:WholeReal4m136Probes.lean.txt'],check=True)
source=run/'candidate-0/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean'
imports=depth/'IMPORTS.lean.txt'
source.write_bytes(imports.read_bytes()+b'\n'+source.read_bytes())
assert json.loads((work/'DEPTH-IMPORT-DAG.json').read_text())['no_owner_cycle']
pins=json.loads((run/'source-pins.json').read_text())
for p in [Path(__file__),source,imports,bridges/'APPEND.lean.txt',bridges/'PREAMBLE.lean.txt',
    bridges/'PROBES-APPEND.lean.txt',work/'DEPTH-IMPORT-DAG.json',*inputs]:
    pins[str(p.relative_to(root))]=hashlib.sha256(p.read_bytes()).hexdigest()
(run/'source-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
