import argparse,hashlib,json,re
from pathlib import Path
h=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,default=Path('/home/tritlo/Code/mcfta'));a=p.parse_args()
m=json.loads((h/'manifest.json').read_text())
for base,items in [(h,m['files']),(a.root,m['sources'])]:
 for item in items:
  b=(base/item['path']).read_bytes();assert len(b)==item['bytes'] and hashlib.sha256(b).hexdigest()==item['sha256'],item['path']
e=a.root/'lean/restart-evidence/20261020-native-owner-capture-ancestry'
s=(h/'reviewed-source.lean').read_bytes()
assert hashlib.sha256(s).hexdigest()=='25db65fa96d236d93426e83eb757d112fff57d6c64c134474027e0dcd344d8be'
assert s==(a.root/'lean/MicroCFTA/SourceCurrentNativeRequestSourceScope.lean').read_bytes()
assert s==(e/'root-request-scope-strict-5.source.lean').read_bytes()
assert not (e/'root-request-scope-strict-5.log').read_bytes()
for stem in ['root-request-scope-strict-5','root-request-scope-canonical-1','root-request-scope-public-1']:
 meta=json.loads((e/(stem+'.json')).read_text());assert meta['exit_code']==0
 assert json.loads((e/meta['limits']).read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 assert meta['wrapper'][meta['wrapper'].index('--mem')+1]=='4G'
 assert meta['wrapper'][meta['wrapper'].index('--time')+1]=='5m'
 if 'source' in meta: assert hashlib.sha256((e/meta['source']).read_bytes()).hexdigest()==meta['sha256']
source=(e/'root-request-scope-public-1.source.lean').read_text()
for option in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:
 assert 'set_option '+option in source
heads=['MicroCFTA.SourceCurrentNativeRequestSourceScope.node_prefix','MicroCFTA.SourceCurrentNativeRequestSourceScope.optional']
for head in heads:
 for command in ['#check @','#print ','#print axioms ']:assert command+head in source
assert len(re.findall(r'^#check @',source,re.M))==2
assert len(re.findall(r'^#print (?!axioms )',source,re.M))==2
log=(e/'root-request-scope-public-1.log').read_text()
assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.',log)
reports=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',log)
assert len(reports)+len(re.findall(r'does not depend on any axioms',log))==2
for report in reports:
 assert set(re.split(r',\s*',re.sub(r'\.\{[^}]*\}','',report).strip()))<={'propext','Classical.choice','Quot.sound'}
print(json.dumps({'status':'PASS','pins':len(m['files'])+len(m['sources']),'lean_jobs':0,'owned_pairs':0,'reused_public_pairs':2,'constructed_pairs':0}))
