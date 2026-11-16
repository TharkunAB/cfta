from pathlib import Path
import ast
import hashlib
import json
import shlex
import subprocess

root=Path('/home/tritlo/Code/mcfta')
base=root/'lean/restart-evidence'
work=Path(__file__).parent
packet=base/'20261116-current-real-actual-task-runtime-foundation-typing-and-configuration-repair'
raw,probe=packet/'APPEND.lean.txt',packet/'PROBES.lean.txt'
assert hashlib.sha256(raw.read_bytes()).hexdigest()=='fd781a0c5ecbb57ac47f2558892b5a759fae7db5ac1861634170432c54197d8f'
(work/'FOUNDATION-APPEND.lean.txt').write_bytes(raw.read_bytes())
old=(base/'20261116-identity-any-budget-publication/ResourceProbes.lean.txt').read_bytes()
assert old.count(b'#print axioms ')==81
(work/'FoundationProbes.lean.txt').write_bytes(old+b'\n'+probe.read_bytes())
run=base/'20261116-native-real-task-runtime-and-nullary-check'
builder=base/'20261116-real-prefix-all-outcome-checkpoint-work/prepare-consumer-unique.py'
subprocess.run(['python3',str(builder),'--run',run.name,'--spec',
    work.name+':FOUNDATION-APPEND.lean.txt:FoundationProbes.lean.txt'],check=True)
driver=run/'check.py';text=driver.read_text()
a=text.index('jobs = ');b=text.index('\nfor name, command, count in jobs:',a)
jobs=ast.literal_eval(text[a+len('jobs = '):b])
args=shlex.split(jobs[1][1]);objects=Path(args[args.index('-o')+1]).parents[2]
nullary=base/'20261116-current-real-nullary-captured-frame-pattern-repair'
name='SourcePruningEnumerationRealNullaryCapturedFrameResources.lean'
assert hashlib.sha256((nullary/name).read_bytes()).hexdigest()=='a5e1fecbd88feddd98deef2a3344698d50ae0b4940f1b5d33d45ffd8ea6b996d'
source=run/'nullary-source/MicroCFTA'/name
source.parent.mkdir(parents=True)
source.write_bytes((nullary/name).read_bytes()+b'\n'+(nullary/'PROBES.lean.txt').read_bytes())
imports=sorted({line.split()[1] for line in (nullary/name).read_text().splitlines() if line.startswith('import ')})
jobs[0]=(jobs[0][0],jobs[0][1]+''.join(' '+shlex.quote(m) for m in imports),0)
cmd='exec lake env lean -j1 -DwarningAsError=true -R '+shlex.quote(str(source.parent.parent))
cmd+=' -o '+shlex.quote(str(objects/'Nullary.olean'))+' '+shlex.quote(str(source))
jobs=[jobs[0],('real-nullary-pattern',cmd,1),*jobs[1:]]
driver.write_text(text[:a]+'jobs = '+repr(jobs)+text[b:])
pins=json.loads((run/'source-pins.json').read_text())
for p in [raw,probe,source,nullary/name,nullary/'PROBES.lean.txt',driver,Path(__file__)]:
    pins[str(p.relative_to(root))]=hashlib.sha256(p.read_bytes()).hexdigest()
(run/'source-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
(run/'objects.json').write_text(json.dumps({'path':str(objects)},indent=2)+'\n')
print(json.dumps({'jobs':[(n,c) for n,_,c in jobs],'objects':str(objects)}))
