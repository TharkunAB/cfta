import hashlib,json,re,subprocess
from pathlib import Path
H=Path(__file__).resolve().parent;R=H.parents[2]
def read(n):return json.loads((H/n).read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(n,d):(H/n).write_text(json.dumps(d,indent=2)+'\n')
def checked(stem,empty=False):
 d=read(stem+'.json');assert d['exit_code']==0,stem
 assert read(stem+'.limits.json')=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 u=read(stem+'.usage.json');assert u['age_seconds']<=600 and u['remaining_percent']>1
 assert d['wrapper'][d['wrapper'].index('--mem')+1]=='4G' and d['wrapper'][d['wrapper'].index('--time')+1]=='5m'
 if 'source' in d:assert sha(H/d['source'])==d['sha256']
 if empty:assert not (H/(stem+'.log')).read_bytes()
 return d
sources=read('selected-sources.json')
for source,item in sources.items():assert sha(R/source)==item['sha256']
assert checked('owner-strict-1',True)['sha256']==sources['lean/MicroCFTA/SourceCurrentOuterPlainOwnerProgress.lean']['sha256']
fixture=H/'PlainOwnerFixture.lean';assert checked('fixture-strict-5',True)['sha256']==sha(fixture)
for stem,head in [('owner-public-1','MicroCFTA.SourceCurrentOuterPlainOwnerProgress.dispatch'),('fixture-public-2','MicroCFTA.PlainOwnerFixture.actual_warm_plain_dispatch')]:
 d=checked(stem);printer=(H/d['source']).read_text();log=(H/(stem+'.log')).read_text()
 for setting in ['pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:assert 'set_option '+setting in printer
 assert '-Dlinter.all=true' in d['command']
 for directive in ['#check @','#print ','#print axioms ']:assert printer.count(directive+head)==1
 assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.',log)
 assert 'theorem '+head in log and ':=' in log
 reports=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',log);assert len(reports)==1
 assert set(re.split(r',\s*',re.sub(r'\.\{[^}]*\}','',reports[0]).strip()))=={'propext','Classical.choice','Quot.sound'}
 if stem.startswith('fixture'):assert printer.startswith(fixture.read_text())
for stem in ['owner-canonical-1','audit-2']:
 checked(stem);log=(H/(stem+'.log')).read_text();assert 'Build completed successfully' in log
 assert not re.search(r'^error',log,re.M)
 assert all('InternedFreshOrdinaryClosedCompletion.lean' in x for x in re.findall(r'^warning:.*$',log,re.M))
audit=(H/'audit-2.log').read_text();assert '3546 jobs' in audit and '74380 MicroCFTA theorems' in audit
for item in read('components.json'):
 subprocess.run(['/usr/bin/python3',str(H/item['path']/item['verifier'])]+(['--live'] if item['live'] else []),check=True,cwd='/',stdout=subprocess.DEVNULL)
for name in ['mcfta-actual-branch-independent-review-source-pins.json','mcfta-outer-top-owner-assessment-source-pins.json']:
 p=H/name
 if p.exists():
  data=json.loads(p.read_text());entries=data['files'] if isinstance(data,dict) else data
  for item in entries:assert sha(R/item['path'])==item['sha256'],item['path']
preserved=json.loads(subprocess.check_output(['/usr/bin/python3',str(H/'verify-preservation.py')],text=True));dump('preservation-final.json',preserved)
unique={}
for p in H.rglob('*.json'):
 if 'previous-publication-support' in p.parts:continue
 try:d=json.loads(p.read_text())
 except ValueError:continue
 if isinstance(d,dict) and isinstance(d.get('command'),list) and d['command'] and Path(d['command'][0]).name in ['lean','lake'] and 'wrapper' in d and isinstance(d.get('exit_code'),int):
  unique.setdefault(json.dumps(d,sort_keys=True),[]).append(str(p.relative_to(H)))
account={'actual_lean_lake_jobs':len(unique),'nonzero_lean_jobs':sum(json.loads(k)['exit_code']!=0 for k in unique),'copies_add_jobs':False,'commands':[{'receipts':v,'exit_code':json.loads(k)['exit_code']} for k,v in unique.items()]};dump('attempt-accounting.json',account)
report={'status':'PASS','proof':(H/'proof-commit.txt').read_text().strip(),'goal_status':'active','new_public_theorems':6,'new_public_definitions':1,'constructed_consumers':1,'audit_jobs':3546,'audit_dependencies':74380,'baseline_files':preserved['baseline_files'],'unchanged_haskell_files':preserved['unchanged_haskell_files'],**{k:v for k,v in account.items() if k!='commands'},'completion_claimed':False};dump('verification.json',report);print(json.dumps(report))
