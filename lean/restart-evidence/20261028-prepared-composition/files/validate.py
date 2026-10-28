from pathlib import Path
import hashlib,json,re
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-prepared-composition-20261028')
def sha(b):return hashlib.sha256(b).hexdigest()
retained={}
for name in ['prior-lean-sources.json','prior-strong-sources.json','prior-haskell-sources.json']:
 records=json.loads((area/name).read_text())
 for rec in records:assert sha((root/rec['path']).read_bytes())==rec['sha256'],rec['path']
 retained[name]=len(records)
modules=json.loads((area/'modules.json').read_text());checks=json.loads((area/'strict-checks.json').read_text())
assert set(checks)==set(modules+['Audit'])
for m,c in checks.items():
 report=json.loads((area/c/'report.json').read_text());src=area/c/'MicroCFTA'/(m+'.lean')
 assert report['exit_code']==0
 assert (area/c/'raw.log').read_bytes()==((f"Checked axiom dependencies of {json.loads((area/'audit-summary.json').read_text())['dependencies']} MicroCFTA theorems.\n".encode()) if m=='Audit' else b'')
 assert report['source_sha256']==sha(src.read_bytes())==sha((root/'lean/MicroCFTA'/(m+'.lean')).read_bytes())
 assert report['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
imports=''.join('import MicroCFTA.'+m+'\n' for m in modules).encode()
assert (root/'lean/MicroCFTA/Audit.lean').read_bytes()==imports+(area/'prior-Audit.lean').read_bytes()
commands=[]
for folder in area.iterdir():
 if folder.is_dir() and (folder/'report.json').exists():
  r=json.loads((folder/'report.json').read_text());raw=(folder/'raw.log').read_bytes()
  assert r['bytes']==len(raw) and r['sha256']==sha(raw)
  assert r['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
  commands.append(dict(folder=folder.name,exit_code=r['exit_code'],bytes=len(raw),sha256=sha(raw)))
for m in modules:
 text=(root/'lean/MicroCFTA'/(m+'.lean')).read_text()
 # Remove comments before checking Lean commands. English documentation is not proof code.
 code=[];depth=0;at=0
 while at<len(text):
  pair=text[at:at+2]
  if depth:
   if pair=='/-':depth+=1;at+=2
   elif pair=='-/':depth-=1;at+=2
   else:
    if text[at]=='\n':code.append('\n')
    at+=1
  elif pair=='/-':depth=1;at+=2
  elif pair=='--':
   stop=text.find('\n',at);at=len(text) if stop<0 else stop
  else:code.append(text[at]);at+=1
 assert depth==0,m
 assert not re.search(r'\b(sorry|admit|axiom|native_decide|set_option\s+(?:maxHeartbeats|maxRecDepth|linter))\b',''.join(code)),m
report=dict(status='pass',retained=retained,new_modules=len(modules),final_strict_checks=len(checks),commands=sorted(commands,key=lambda r:r['folder']),current_commands=sum(x['folder']!='prior-public-readback' for x in commands),inherited_commands=sum(x['folder']=='prior-public-readback' for x in commands),failures=sum(x['exit_code']!=0 for x in commands),precompiler_launch_failures=[str(x.relative_to(area)) for x in sorted(area.glob('*/launch-failure.json'))],source_hashes={m:sha((root/'lean/MicroCFTA'/(m+'.lean')).read_bytes()) for m in modules})
(area/'source-validation.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k not in ['commands','source_hashes']}))
