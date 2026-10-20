import argparse,hashlib,json,re
from pathlib import Path
h=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,default=Path('/home/tritlo/Code/mcfta'));a=p.parse_args()
m=json.loads((h/'manifest.json').read_text())
for base,items in [(h,m['files']),(a.root,m['sources'])]:
 for item in items:
  b=(base/item['path']).read_bytes();assert len(b)==item['bytes'] and hashlib.sha256(b).hexdigest()==item['sha256'],item['path']
e=a.root/'lean/restart-evidence/20261020-native-active-result-lineage';f=e/'compiled-terminal-generation-fixture'
for base,stem,snapshot in [(e,'root-captured-mu-strict-1','reviewed-capture.lean'),(f,'terminal-mu-kernels-direct-1','reviewed-fixture.lean')]:
 meta=json.loads((base/(stem+'.json')).read_text());assert meta['exit_code']==0
 assert not (base/meta['log']).read_bytes()
 assert (base/meta['source']).read_bytes()==(h/snapshot).read_bytes()
 assert hashlib.sha256((base/meta['source']).read_bytes()).hexdigest()==meta['sha256']
 assert json.loads((base/meta['limits']).read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
meta=json.loads((f/'terminal-mu-kernels-public-1.json').read_text());assert meta['exit_code']==0
source=(f/meta['source']).read_text();log=(f/meta['log']).read_text()
assert source.startswith((h/'reviewed-fixture.lean').read_text())
for option in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:
 assert 'set_option '+option in source
for pattern in [r'^#check @',r'^#print (?!axioms )',r'^#print axioms ']:assert len(re.findall(pattern,source,re.M))==1
assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.',log)
reports=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',log)
assert len(reports)+len(re.findall(r'does not depend on any axioms',log))==1
for report in reports:assert set(re.split(r',\s*',re.sub(r'\.\{[^}]*\}','',report).strip()))<={'propext','Classical.choice','Quot.sound'}
print(json.dumps({'status':'PASS','pins':len(m['files'])+len(m['sources']),'lean_jobs':0,'owned_pairs':0,'reused_constructed_pairs':1}))
