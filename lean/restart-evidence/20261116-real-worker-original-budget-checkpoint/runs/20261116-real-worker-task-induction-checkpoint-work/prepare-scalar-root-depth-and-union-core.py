from pathlib import Path
import ast
import hashlib
import json
import shlex
import subprocess

root=Path('/home/tritlo/Code/mcfta')
base=root/'lean/restart-evidence'
work=Path(__file__).parent
prior=(work/'prepare-4m-and-actual-dispatch.py').read_text()
replacements={
 '20261116-current-real-worker-scan-checking-limit-4m':'20261116-current-real-worker-scan-scalar-root-projection-repair',
 '6fa99803fbef35074851f6b42126670d7c946b76c75d3738515727f275188284':'f178ebea61122b099704652b164d0acf843a27ab579fd06a6fdc77f429c609a6',
 '20261116-current-real-worker-depth-actual-dispatch-repair':'20261116-current-real-worker-depth-prepared-result-normalization-repair',
 '613e5c88070d2b8402151ae625fe210068e78d30b3e7f70173e276611def315c':'d081620e3301bae0462ceeeb219b470bbf724aaf9334885adbc980b04ccb9e10',
 'SCAN-4M-ACTUAL-DISPATCH-APPEND':'SCALAR-ROOT-NORMALIZED-FULL-APPEND',
 'WholeReal4m136Probes':'WholeScalarRoot136Probes',
 '20261116-native-whole-real-worker-4m-and-actual-dispatch-check':'20261116-native-whole-real-scalar-root-and-union-normal-check'}
for a,b in replacements.items():
    assert a in prior
    prior=prior.replace(a,b)
helper=work/'prepare-scalar-root-depth-core.py';helper.write_text(prior)
subprocess.run(['python3',str(helper)],check=True)
run=base/'20261116-native-whole-real-scalar-root-and-union-normal-check'
driver=run/'check.py';text=driver.read_text();a=text.index('jobs = ');b=text.index('\nfor name, command, count in jobs:',a)
jobs=ast.literal_eval(text[a+len('jobs = '):b])
args=shlex.split(jobs[1][1]);objects=Path(args[args.index('-o')+1]).parents[2]
packet=base/'20261116-current-shared-incoming-union-normal-skipped-gate-repair'
name='SourcePruningEnumerationSharedIncomingUnionNormal.lean';raw=packet/name;probe=packet/'PROBES.lean.txt'
assert hashlib.sha256(raw.read_bytes()).hexdigest()=='646671cf186b2607543e1b28126b5ed612af9337d1584ce542c5e6b29d02aa6c'
source=run/'union-source/MicroCFTA'/name;source.parent.mkdir(parents=True)
source.write_bytes(raw.read_bytes()+b'\n'+probe.read_bytes())
imports=sorted({line.split()[1] for line in raw.read_text().splitlines() if line.startswith('import ')})
jobs[0]=(jobs[0][0],jobs[0][1]+''.join(' '+shlex.quote(x) for x in imports),0)
command='exec lake env lean -j1 -DwarningAsError=true -R '+shlex.quote(str(source.parent.parent))
command+=' -o '+shlex.quote(str(objects/'IncomingUnionNormal.olean'))+' '+shlex.quote(str(source))
jobs=[jobs[0],('shared-incoming-union-normal',command,1),*jobs[1:]]
driver.write_text(text[:a]+'jobs = '+repr(jobs)+text[b:])
pins=json.loads((run/'source-pins.json').read_text())
for p in [Path(__file__),helper,driver,raw,probe,source]:
    pins[str(p.relative_to(root))]=hashlib.sha256(p.read_bytes()).hexdigest()
(run/'source-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
(run/'objects.json').write_text(json.dumps({'path':str(objects)},indent=2)+'\n')
print(json.dumps({'jobs':[(n,c) for n,_,c in jobs],'objects':str(objects)}))
