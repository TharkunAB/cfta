import argparse,hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--live',action='store_true');a=p.parse_args()
def check(base,item):
 b=(base/item['path']).read_bytes();assert len(b)==item['bytes'] and hashlib.sha256(b).hexdigest()==item['sha256'],item['path']
m=json.loads((HERE/'manifest.json').read_text())
for x in m['files']:check(HERE,x)
r=json.loads((HERE/'source-pins.json').read_text())['files']
for x in r:check(a.root,x)
source=(HERE/'unfold-kernels.lean').read_bytes()
assert source==(HERE/'unfold-kernels-direct-2.source.lean').read_bytes()
assert source.decode().count('SourceCurrentNativeCapturedMuUnfoldRows.capture ')==1
private=source.decode().split('private theorem checked_witness :',1)[1].split(' := by',1)[0].strip()
public=source.decode().split('theorem actual_captured_unfold :',1)[1].split(' := checked_witness',1)[0].strip()
assert private==public
for stem in ['unfold-kernels-direct-2','unfold-kernels-public-1']:
 meta=json.loads((HERE/(stem+'.json')).read_text());assert meta['exit_code']==0
 assert meta['command'][0]=='/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
 assert '-Dlinter.all=true' in meta['command']
 assert meta['wrapper'][0]=='/home/tritlo/Code/heavy-management/bin/capped'
 assert meta['wrapper'][meta['wrapper'].index('--mem')+1]=='4G'
 assert meta['wrapper'][meta['wrapper'].index('--time')+1]=='5m'
 assert json.loads((HERE/meta['limits']).read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 usage=json.loads((HERE/(stem+'.usage.json')).read_text());assert usage['age_seconds']<600 and usage['remaining_percent']>1
 assert hashlib.sha256((HERE/meta['source']).read_bytes()).hexdigest()==meta['sha256']
assert not (HERE/'unfold-kernels-direct-2.log').read_bytes()
printer=(HERE/'unfold-kernels-public-1.source.lean').read_text();assert printer.encode().startswith(source)
for option in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:assert 'set_option '+option in printer
name='MicroCFTA.CapturedStoredUnfoldFixture.actual_captured_unfold'
for prefix in ['#check @','#print ','#print axioms ']:assert prefix+name in printer
log=(HERE/'unfold-kernels-public-1.log').read_text()
assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.',log)
reports=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',log)
assert len(reports)+len(re.findall(r'does not depend on any axioms',log))==1
for report in reports:assert set(re.split(r',\s*',re.sub(r'\.\{[^}]*\}','',report).strip())) <= {'propext','Classical.choice','Quot.sound'}
selection=json.loads((HERE/'unfold-kernels-selection.json').read_text())
assert selection['finalized'] and selection['strict']=='unfold-kernels-direct-2'
assert selection['public_heads']==[name] and selection['groups'][0]['name']=='unfold-kernels-public-1'
assert selection['lean_jobs']==3 and selection['failed_attempts']==1
if a.live:
 live=a.root/'lean/restart-evidence/20261020-native-captured-stored-rows/captured-stored-unfold-fixture'
 for x in m['selected_owner_files']:assert (HERE/x).read_bytes()==(live/x).read_bytes(),x
print(json.dumps({'status':'PASS','pins':len(m['files'])+len(r),'new_lean_jobs':0,'owned_pairs':0,'reused_constructed_pairs':1,'reused_selected_commands':2,'mode':'live' if a.live else 'ordinary'}))
