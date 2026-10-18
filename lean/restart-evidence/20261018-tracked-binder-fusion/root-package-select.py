import hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
read=lambda n:json.loads((HERE/n).read_text())
def write(n,v):(HERE/n).write_text(json.dumps(v,indent=2)+'\n')
names=read('new-modules.json');prefixes=['marker-choice','tracked-slot','tracked-erase']
sels=[read(p+'-selection.json') for p in prefixes]
groups=[{**g,'kind':'new-public' if g['kind']=='public' else g['kind']} for s in sels for g in s['groups']]
for p in ['binder-contract','binder-uniform']:groups+=read(p+'-selection.json')['groups']
assert len(groups)==8 and sum(g['pairs'] for g in groups if g['kind']=='new-public')==9 and sum(g['pairs'] for g in groups if g['kind']=='constructed')==5
components=[p+'-manifest.json' for p in prefixes+['binder-contract','binder-contract-consequence','binder-uniform','slot-review']]
for n in components:assert (HERE/n).is_file(),n
write('selected-groups.json',groups)
write('selected-strict.json',{n:s['strict'] for n,s in zip(names,sels)})
write('selected-canonical.json',{n:s['canonical'] for n,s in zip(names,sels)})
constructed={s['constructed_strict']:p+'-kernels.lean' for p,s in zip(prefixes,sels)}
constructed.update({'binder-contract-direct-5':'binder-contract-counterexample.lean','binder-uniform-direct-1':'binder-uniform-kernels.lean'})
write('selected-constructed-strict.json',constructed);write('component-manifests.json',components)
write('expected-counts.json',{'pairs':{'new-public':9,'constructed':5,'private-claim':0},'modules':3,'constructed_strict':5,'components':7})
for n,expected in read('frozen-modules.json').items():assert hashlib.sha256((ROOT/'lean/MicroCFTA'/(n+'.lean')).read_bytes()).hexdigest()==expected
write('selection-status.json',{'finalized':True})
log=(HERE/'full-audit-1.log').read_text()
write('selected-audit.json',{'name':'full-audit-1','jobs':int(re.findall(r'Build completed successfully \((\d+) jobs\)\.',log)[-1]),'dependency_checks':int(re.findall(r'Checked axiom dependencies of (\d+) MicroCFTA theorems\.',log)[-1])})
print('Selected9 public,3 integration fixtures,1 exact counterexample,1 checked consequence,7 manifests')
