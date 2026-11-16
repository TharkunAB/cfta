from pathlib import Path
import ast
import hashlib
import json
import shlex
import subprocess

root=Path('/home/tritlo/Code/mcfta')
base=root/'lean/restart-evidence'
work=Path(__file__).parent
runtime=base/'20261116-current-real-actual-task-runtime-root-width-repair'
raw,probe=runtime/'APPEND.lean.txt',runtime/'PROBES.lean.txt'
assert hashlib.sha256(raw.read_bytes()).hexdigest()=='88f833fdc606da369f450a2b207354f15bd92f03927d0af9a6936681e13c0364'
(work/'RUNTIME-APPEND.lean.txt').write_bytes(raw.read_bytes())
old=(base/'20261116-identity-any-budget-publication/ResourceProbes.lean.txt').read_bytes()
assert old.count(b'#print axioms ')==81
(work/'Runtime89Probes.lean.txt').write_bytes(old+b'\n'+probe.read_bytes())
assert (work/'Runtime89Probes.lean.txt').read_bytes().count(b'#print axioms ')==89
run=base/'20261116-native-real-runtime-and-prefix-admission-check'
builder=base/'20261116-real-prefix-all-outcome-checkpoint-work/prepare-consumer-unique.py'
subprocess.run(['python3',str(builder),'--run',run.name,'--spec',
    work.name+':RUNTIME-APPEND.lean.txt:Runtime89Probes.lean.txt'],check=True)
driver=run/'check.py';text=driver.read_text()
a=text.index('jobs = ');b=text.index('\nfor name, command, count in jobs:',a)
jobs=ast.literal_eval(text[a+len('jobs = '):b])
args=shlex.split(jobs[1][1]);objects=Path(args[args.index('-o')+1]).parents[2]
packet=base/'20261116-current-real-prefix-admission-draft'
name='SourcePruningEnumerationObservedRealPrefixAdmission.lean'
assert hashlib.sha256((packet/name).read_bytes()).hexdigest()=='38c506e41fab073cd364fac16866ad8027bc4e7b5c0909a3e439f7317565087e'
source=run/'admission-source/MicroCFTA'/name
source.parent.mkdir(parents=True)
source.write_bytes((packet/name).read_bytes()+b'\n'+(packet/'PROBES.lean.txt').read_bytes())
imports=sorted({line.split()[1] for line in (packet/name).read_text().splitlines() if line.startswith('import ')})
jobs[0]=(jobs[0][0],jobs[0][1]+''.join(' '+shlex.quote(m) for m in imports),0)
visibility=packet/'VISIBILITY-PROBES.lean'
visible='exec lake env lean -j1 -DwarningAsError=true '+shlex.quote(str(visibility))
admission='exec lake env lean -j1 -DwarningAsError=true -R '+shlex.quote(str(source.parent.parent))
admission+=' -o '+shlex.quote(str(objects/'Admission.olean'))+' '+shlex.quote(str(source))
jobs=[jobs[0],('public-receipt-imports',visible,3),('real-prefix-admission',admission,1),*jobs[1:]]
assert len({n for n,_,_ in jobs})==len(jobs)
driver.write_text(text[:a]+'jobs = '+repr(jobs)+text[b:])
pins=json.loads((run/'source-pins.json').read_text())
for p in [raw,probe,source,packet/name,packet/'PROBES.lean.txt',visibility,driver,Path(__file__)]:
    pins[str(p.relative_to(root))]=hashlib.sha256(p.read_bytes()).hexdigest()
(run/'source-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
(run/'objects.json').write_text(json.dumps({'path':str(objects)},indent=2)+'\n')
print(json.dumps({'jobs':[(n,c) for n,_,c in jobs],'objects':str(objects)}))
