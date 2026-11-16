from pathlib import Path
import ast
import hashlib
import json
import shlex
import subprocess

root=Path('/home/tritlo/Code/mcfta')
base=root/'lean/restart-evidence'
work=Path(__file__).parent
previous=base/'20261116-real-worker-assembly-checkpoint-work'
fallback=base/'20261116-current-real-actual-source-fallback-resources-draft'
payload=base/'20261116-current-past-entry-inner-payload-transport-draft'
raw=fallback/'APPEND.lean.txt'
assert hashlib.sha256(raw.read_bytes()).hexdigest()=='e0290086f7cf9eed6a8a19f6f59e9dcde24dbb14c962669c039076ca2a4993c2'
(work/'TASK-APPEND.lean.txt').write_bytes((previous/'TUPLE-REPAIR-APPEND.lean.txt').read_bytes()+b'\n'+raw.read_bytes())
probes=(previous/'TupleRepair101Probes.lean.txt').read_bytes()+b'\n'+(fallback/'PROBES.lean.txt').read_bytes()
assert probes.count(b'#print axioms ')==105
(work/'Task105Probes.lean.txt').write_bytes(probes)
builder=base/'20261116-real-prefix-all-outcome-checkpoint-work/prepare-consumer-unique.py'
run=base/'20261116-native-real-fallback-and-past-payload-check'
subprocess.run(['python3',str(builder),'--run',run.name,'--spec',
    work.name+':TASK-APPEND.lean.txt:Task105Probes.lean.txt'],check=True)
driver=run/'check.py';text=driver.read_text()
a=text.index('jobs = ');b=text.index('\nfor name, command, count in jobs:',a)
jobs=ast.literal_eval(text[a+len('jobs = '):b])
args=shlex.split(jobs[1][1]);objects=Path(args[args.index('-o')+1]).parents[2]
name='SourceCurrentAllocatedNativePastEntryInnerPayloadTransport.lean'
assert hashlib.sha256((payload/name).read_bytes()).hexdigest()=='5a156dcc4db43f5a2ad58b626a88214c2f480872a8b14c2e5817155692bd278f'
source=run/'payload-source/MicroCFTA'/name
source.parent.mkdir(parents=True)
source.write_bytes((payload/name).read_bytes()+b'\n'+(payload/'PROBES.lean.txt').read_bytes())
imports=sorted({line.split()[1] for line in (payload/name).read_text().splitlines() if line.startswith('import ')})
jobs[0]=(jobs[0][0],jobs[0][1]+''.join(' '+shlex.quote(m) for m in imports),0)
command='exec lake env lean -j1 -DwarningAsError=true -R '+shlex.quote(str(source.parent.parent))
command+=' -o '+shlex.quote(str(objects/'PastPayload.olean'))+' '+shlex.quote(str(source))
jobs=[jobs[0],('past-entry-payload',command,1),*jobs[1:]]
assert len({n for n,_,_ in jobs})==len(jobs)
driver.write_text(text[:a]+'jobs = '+repr(jobs)+text[b:])
pins=json.loads((run/'source-pins.json').read_text())
for p in [Path(__file__),raw,fallback/'PROBES.lean.txt',payload/name,payload/'PROBES.lean.txt',source,driver]:
    pins[str(p.relative_to(root))]=hashlib.sha256(p.read_bytes()).hexdigest()
(run/'source-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
(run/'objects.json').write_text(json.dumps({'path':str(objects)},indent=2)+'\n')
print(json.dumps({'jobs':[(n,c) for n,_,c in jobs],'objects':str(objects)}))
