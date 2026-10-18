import hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
read=lambda name:json.loads((HERE/name).read_text())
def write(name,value):(HERE/name).write_text(json.dumps(value,indent=2)+'\n')
names=read('new-modules.json')
prefixes=['filtered-source','node-fusion','filtered-union','binder-free']
selections=[read(prefix+'-selection.json') for prefix in prefixes]
groups=[{**group,'kind':'new-public' if group['kind']=='public' else group['kind']} for s in selections for group in s['groups']]
assert sum(g['pairs'] for g in groups if g['kind']=='new-public')==8
assert sum(g['pairs'] for g in groups if g['kind']=='constructed')==4
components=[prefix+'-manifest.json' for prefix in prefixes]+['node-fusion-review-manifest.json','fusion-boundary-manifest.json']
for name in components:assert (HERE/name).is_file(),name
write('selected-groups.json',groups)
write('selected-strict.json',{name:s['strict'] for name,s in zip(names,selections)})
write('selected-canonical.json',{name:s['canonical'] for name,s in zip(names,selections)})
write('selected-constructed-strict.json',{s['constructed_strict']:prefix+'-kernels.lean' for prefix,s in zip(prefixes,selections)})
write('component-manifests.json',components)
write('expected-counts.json',{'pairs':{'new-public':8,'constructed':4,'private-claim':0},'modules':4,'constructed_strict':4,'components':len(components)})
for name,expected in read('frozen-modules.json').items():assert hashlib.sha256((ROOT/'lean/MicroCFTA'/(name+'.lean')).read_bytes()).hexdigest()==expected
write('selection-status.json',{'finalized':True})
log=(HERE/'full-audit-1.log').read_text()
write('selected-audit.json',{'name':'full-audit-1','jobs':int(re.findall(r'Build completed successfully \((\d+) jobs\)\.',log)[-1]),'dependency_checks':int(re.findall(r'Checked axiom dependencies of (\d+) MicroCFTA theorems\.',log)[-1])})
print('Selected:8 public,4 constructed,4 production modules,6 manifests')
