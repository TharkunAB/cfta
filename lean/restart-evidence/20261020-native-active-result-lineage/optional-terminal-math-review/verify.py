import argparse,hashlib,json
from pathlib import Path
h=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,default=Path('/home/tritlo/Code/mcfta'));a=p.parse_args()
m=json.loads((h/'manifest.json').read_text())
for base,items in [(h,m['files']),(a.root,m['sources'])]:
 for item in items:
  b=(base/item['path']).read_bytes();assert len(b)==item['bytes'] and hashlib.sha256(b).hexdigest()==item['sha256'],item['path']
e=a.root/'lean/restart-evidence/20261020-native-active-result-lineage'
for stem,snapshot in [('root-optional-terminal-strict-2','reviewed-optional-terminal.lean'),('root-terminal-generation-strict-1','reviewed-terminal-generation.lean')]:
 meta=json.loads((e/(stem+'.json')).read_text());assert meta['exit_code']==0
 assert not (e/meta['log']).read_bytes()
 assert (h/snapshot).read_bytes()==(e/meta['source']).read_bytes()
 assert hashlib.sha256((e/meta['source']).read_bytes()).hexdigest()==meta['sha256']
 assert json.loads((e/meta['limits']).read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 assert meta['wrapper'][meta['wrapper'].index('--mem')+1]=='4G'
 assert meta['wrapper'][meta['wrapper'].index('--time')+1]=='5m'
print(json.dumps({'status':'PASS','pins':len(m['files'])+len(m['sources']),'lean_jobs':0,'public_pairs':0,'constructed_pairs':0,'reused_strict_receipts':2}))
