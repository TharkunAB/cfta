import hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
read=lambda name:json.loads((HERE/name).read_text())
def write(name,value):(HERE/name).write_text(json.dumps(value,indent=2)+'\n')
names=read('new-modules.json')
prefixes=['issued-history','issued-writers','binder-rank','binder-plan','binder-child-depth']
selections=[read(prefix+'-selection.json') for prefix in prefixes]
groups=[{**group,'kind':'new-public' if group['kind']=='public' else group['kind']} for s in selections for group in s['groups']]
focused=read('binder-history-selection.json')
groups+=focused['groups']
assert sum(g['pairs'] for g in groups if g['kind']=='new-public')==21
assert sum(g['pairs'] for g in groups if g['kind']=='constructed')==6
components=[prefix+'-manifest.json' for prefix in prefixes]+['issued-review-manifest.json','binder-history-manifest.json']
for name in components:assert (HERE/name).is_file(),name
write('selected-groups.json',groups)
write('selected-strict.json',{name:s['strict'] for name,s in zip(names,selections)})
write('selected-canonical.json',{name:s['canonical'] for name,s in zip(names,selections)})
constructed={s['constructed_strict']:prefix+'-kernels.lean' for prefix,s in zip(prefixes,selections)}
constructed[focused['constructed_strict']]='binder-history-projections.lean'
write('selected-constructed-strict.json',constructed)
write('component-manifests.json',components)
write('expected-counts.json',{'pairs':{'new-public':21,'constructed':6,'private-claim':0},'modules':5,'constructed_strict':6,'components':len(components)})
for name,expected in read('frozen-modules.json').items():assert hashlib.sha256((ROOT/'lean/MicroCFTA'/(name+'.lean')).read_bytes()).hexdigest()==expected
write('selection-status.json',{'finalized':True})
log=(HERE/'full-audit-1.log').read_text()
write('selected-audit.json',{'name':'full-audit-1','jobs':int(re.findall(r'Build completed successfully \((\d+) jobs\)\.',log)[-1]),'dependency_checks':int(re.findall(r'Checked axiom dependencies of (\d+) MicroCFTA theorems\.',log)[-1])})
print('Selected:21 public,6 constructed,5 production modules,7 manifests')
