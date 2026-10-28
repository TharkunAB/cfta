from pathlib import Path
import hashlib,json,re,subprocess
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-prepared-recursive-20261028')
def digest(data):return hashlib.sha256(data).hexdigest()
modules=json.loads((area/'modules.json').read_text());checks=json.loads((area/'strict-checks.json').read_text());assert set(checks)==set(modules+['Audit'])
records=[]
for module,name in checks.items():
 folder=area/name;report=json.loads((folder/'report.json').read_text());relative=Path('lean/MicroCFTA')/(module+'.lean');data=(root/relative).read_bytes();raw=(folder/'raw.log').read_bytes()
 assert data==(folder/'MicroCFTA'/(module+'.lean')).read_bytes()
 assert digest(data)==report['source_sha256'] and digest(raw)==report['sha256'] and len(raw)==report['bytes'] and report['exit_code']==0
 assert report['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 if module!='Audit':
  assert not raw
  code=re.sub(rb'/-.*?-/',b'',data,flags=re.S);code=re.sub(rb'--[^\n]*',b'',code)
  assert not re.search(rb'\b(sorry|admit|axiom|native_decide)\b',code)
  assert b'maxHeartbeats' not in data and b'set_option linter' not in data
 records.append(dict(module=module,check=name,bytes=len(data),sha256=digest(data)))
base=(area/'published-base.txt').read_text().strip()
changed=[n.decode() for n in subprocess.check_output(['git','diff','--name-only','-z',base],cwd=root).split(b'\0') if n]
assert not any(n.endswith(('.hs','.cabal')) for n in changed)
allowed={'lean/MicroCFTA/'+m+'.lean' for m in modules+['Audit']}
assert all(not n.startswith('lean/MicroCFTA/') or n in allowed for n in changed)
old=(area/'prior-sources/Audit.lean').read_bytes();offset=json.loads((area/'audit-import-insertion.json').read_text())['insertion_offset'];extra=''.join('import MicroCFTA.'+m+'\n' for m in modules).encode()
assert (root/'lean/MicroCFTA/Audit.lean').read_bytes()==old[:offset]+extra+old[offset:]
counts={}
for name in ['prior-lean-sources.json','prior-haskell-sources.json','prior-strong-sources.json']:
 count=0
 for record in json.loads((area/name).read_text()):
  if record['path']=='lean/MicroCFTA/Audit.lean':continue
  data=(root/record['path']).read_bytes();assert len(data)==record['bytes'] and digest(data)==record['sha256'],record['path'];count+=1
 counts[name]=count
for module in modules+['Audit']+[r['module'] for r in json.loads((area/'prior-strong-sources.json').read_text())]:
 relative=Path('lean/MicroCFTA')/(module+'.lean');target=area/'installed-sources'/relative;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes((root/relative).read_bytes())
commands=[]
for p in sorted(area.glob('*/report.json')):
 if p.parent.name=='prior-public-readback':continue
 report=json.loads(p.read_text());raw=(p.parent/'raw.log').read_bytes();assert len(raw)==report['bytes'] and digest(raw)==report['sha256'];assert report['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 commands.append(dict(name=p.parent.name,report=report))
(area/'actual-commands.json').write_text(json.dumps(commands,indent=2)+'\n')
report=dict(status='pass',strict_checks=records,unchanged_prior_public_theorems=len(json.loads((area/'prior-public-declarations.json').read_text())),audit_only_adds_imports=True,no_haskell_changes=True,preserved_counts=counts,commands=len(commands),failures=sum(c['report']['exit_code']!=0 for c in commands))
(area/'source-validation.json').write_text(json.dumps(report,indent=2)+'\n');(area/'preservation-validation.json').write_text(json.dumps(dict(status='pass',**counts),indent=2)+'\n')
print(json.dumps(dict(status='pass',checks=len(checks),preserved=counts,commands=report['commands'],failures=report['failures'])))
