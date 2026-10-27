from pathlib import Path
import json,hashlib,datetime
repo=Path('/home/tritlo/Code/mcfta');root=Path('/tmp/mcfta-recursive-composition-20261027');out=root/'output-history-review';sha=lambda b:hashlib.sha256(b).hexdigest()
def write(p,b):
 p=out/p;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
def js(p,obj):write(p,(json.dumps(obj,indent=2)+'\n').encode())
inputs=[
('SourcePruningEnumerationHookInvocation',[(26,33),(38,68),(71,79),(148,156)],'whole new module read'),
('SourcePruningEnumerationOrdinaryInvocation',[(27,36),(40,50),(86,98),(108,112)],'whole new module read'),
('SourcePruningEnumerationOutputHistory',[(27,70),(103,113),(174,186)],'whole new module read'),
('SourcePruningEnumerationNativeContinuations',[(47,81)],'whole runtime and source equations read; later identity proof read'),
('SourcePruningEnumerationNativeOrdinaryContinuations',[(20,34)],'whole runtime and entry equations read'),
('SourcePruningEnumerationRecursive',[(65,82),(89,127)],'whole recursive runtime read'),
('SourcePruningEnumerationNativeBranches',[(23,27)],'actual advance and sibling control flow read; unrelated trace proofs not reviewed')]
sources=[];cuts=[];evidence=[]
for name,parts,scope in inputs:
 path=repo/'lean/MicroCFTA'/(name+'.lean');b=path.read_bytes();dest=Path('inputs/lean/MicroCFTA')/(name+'.lean');write(dest,b)
 sources.append({'path':str(path),'source':str(path),'snapshot':str(dest),'bytes':len(b),'sha256':sha(b),'read_scope':scope});lines=b.splitlines(keepends=True)
 for start,end in parts:
  assert 1<=start<=end<=len(lines),(name,start,end,len(lines));data=b''.join(lines[start-1:end]);dest=Path('cuts')/(name+f'--{start}-{end}.lean');write(dest,data)
  cuts.append({'path':str(path),'source':str(path),'snapshot':str(dest),'start':start,'end':end,'source_sha256':sha(b),'bytes':len(data),'sha256':sha(data)})
for name,stem in [('SourcePruningEnumerationHookInvocation','hook-invocation'),('SourcePruningEnumerationOrdinaryInvocation','ordinary-invocation'),('SourcePruningEnumerationOutputHistory','output-history')]:
 current=(repo/'lean/MicroCFTA'/(name+'.lean')).read_bytes()
 for attempt in [1,2]:
  check='strict-'+stem+'-'+str(attempt);d=root/check;report=json.loads((d/'report.json').read_text());raw=(d/'raw.log').read_bytes();src=(d/'MicroCFTA'/(name+'.lean')).read_bytes()
  assert report['bytes']==len(raw) and report['sha256']==sha(raw) and report['source_sha256']==sha(src)
  if attempt==2:
   assert report['exit_code']==0 and raw==b'' and src==current
   assert '-DwarningAsError=true'in report['command'] and '-Dlinter.all=true'in report['command']
   assert report['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
  else:assert report['exit_code']!=0
  for rel in ['report.json','raw.log','MicroCFTA/'+name+'.lean']:
   if attempt==2 and rel.startswith('MicroCFTA/'):continue
   p=d/rel;b=p.read_bytes();dest=Path('evidence')/check/rel;write(dest,b);evidence.append({'path':str(p),'source':str(p),'snapshot':str(dest),'bytes':len(b),'sha256':sha(b),'role':'final actual strict evidence'if attempt==2 else'retained earlier failing strict provenance'})
index={'version':1,'status':'FINAL CLEAR SOURCE REVIEW','observed_at':datetime.datetime.now().astimezone().isoformat(),'sources':sources,'cuts':cuts,'evidence':evidence,'reviewed_new_modules':3,'reviewed_new_source_lines':465,'read_scope':'report.txt; whole three new modules plus actual recursive/sibling/entry runtime branches; no import-closure audit','limits':'Necessary actual output paths, not converse run membership or semantic acceptance. No Post/full-Memos certificate is added.'};js(Path('source-pins.json'),index)
for s in sources:assert (out/s['snapshot']).read_bytes()==Path(s['source']).read_bytes()
for c in cuts:assert (out/c['snapshot']).read_bytes()==b''.join(Path(c['source']).read_bytes().splitlines(keepends=True)[c['start']-1:c['end']])
files=[p for p in sorted(out.rglob('*'))if p.is_file()and p not in {out/'pins.json',out/'FROZEN.json'}];pins={'version':1,'pins':[{'path':str(p.relative_to(out)),'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())}for p in files]};js(Path('pins.json'),pins);pr=(out/'pins.json').read_bytes()
f={'status':'FROZEN FINAL CLEAR SOURCE REVIEW','pins_count':len(files),'pins_bytes':len(pr),'pins_sha256':sha(pr),'source_count':len(sources),'cut_count':len(cuts),'cut_lines':sum(x['end']-x['start']+1 for x in cuts),'evidence_count':len(evidence),'report_sha256':sha((out/'report.txt').read_bytes()),'source_pins_sha256':sha((out/'source-pins.json').read_bytes()),'new_checks_executed':False};js(Path('FROZEN.json'),f)
for x in pins['pins']:
 b=(out/x['path']).read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256']
assert len(files)+2==sum(p.is_file()for p in out.rglob('*'));print(json.dumps(f,indent=2));print('FROZEN SHA256',sha((out/'FROZEN.json').read_bytes()));print('Exact files',len(files)+2)
