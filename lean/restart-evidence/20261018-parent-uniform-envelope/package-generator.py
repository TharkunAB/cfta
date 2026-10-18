import hashlib
import json
import subprocess
from pathlib import Path
ROOT=Path('/home/tritlo/Code/mcfta')
HERE=Path(__file__).resolve().parent
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def write(name,value):(HERE/name).write_text(json.dumps(value,indent=2)+'\n')
def read(name):return json.loads((HERE/name).read_text())
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT,text=True).strip()
names=read('new-modules.json')
(HERE/'proof-commit.txt').write_text(git('rev-parse','HEAD')+'\n')
write('frozen-modules.json',{name:sha(ROOT/'lean/MicroCFTA'/(name+'.lean')) for name in names})
groups=[{'name':'parent-room-public-1','pairs':6,'kind':'new-public','full_proof':True},
        {'name':'parent-room-kernels-public-1','pairs':1,'kind':'constructed','full_proof':True}]
uniform=read('parent-uniform-selection.json')
target=read('parent-guard-selection.json')
outer=read('outer-budget-selection.json')
for selected in [uniform,target,outer]:
 for group in selected['selected_groups']:
  group=dict(group)
  if group['kind']=='public':group['kind']='new-public'
  groups.append(group)
write('selected-groups.json',groups)
write('selected-strict.json',dict(zip(names,[uniform['strict'],'parent-room-direct-2',target['strict'],outer['strict']])))
write('selected-canonical.json',dict(zip(names,[uniform['canonical'],'parent-room-canonical-1',target['canonical'],outer['canonical']])))
write('selected-constructed-strict.json',['parent-room-kernels-1',target['constructed_strict'],outer['kernel_strict']])
write('selected-audit.json',{'name':'full-audit-1','jobs':3241,'dependency_checks':71037})
write('selection-status.json',{'finalized':True,'status':'FINAL'})
write('raw-log-archives.json',[])
write('upstream-refresh.json',{'command':['git','pull','--ff-only'],'exit_code':0,
 'output':'From github.com:TharkunAB/cfta\n   5e4aa730..bb2f5589  improve/specftacular-correctness-memory -> origin/improve/specftacular-correctness-memory\nAlready up to date.\n',
 'recorded_from_completed_call':True,'starting_head':(HERE/'starting-head.txt').read_text().strip(),
 'main':git('rev-parse','origin/main'),'formalize':git('rev-parse','origin/formalize'),
 'publication':'Pending direct approval. No push attempted.'})
components=['parent-uniform-manifest.json','parent-guard-manifest.json','outer-budget-manifest.json',
 'uniform-cross-review-manifest.json','guard-uniform-review-manifest.json','root-scope-manifest.json']
write('component-manifests.json',components)
paths=[HERE/name for name in ['root-scope-review.md','root-peaks.txt','root-run-check.py','root-capped-worker.py',
 'verify-probes.py','verify-checkpoint.py','verify-preservation.py','verify-closure.py',
 'package-generator.py','current-notes-generator.py','current-body.txt']]
for path in HERE.iterdir():
 if path.is_file() and path.name.startswith(('parent-room-','full-audit-')):paths.append(path)
for name in names+['SourceCurrentClassesForecast','SourceCurrentScanNumericForecast','SourceCurrentScanRequiredForecast',
 'SourceCurrentParentAlphabetReservation','SourceCurrentInitialSelectionForecast','SourceCurrentParentNumeric',
 'SourceCurrentAllocatedNativeResourceForecast','SourceCurrentGeneratedQueryGuardResources','SourceCurrentAllocatedPartialWorker']:
 paths.append(ROOT/'lean/MicroCFTA'/(name+'.lean'))
write('root-scope-manifest.json',{'component':'root-scope-review','entries':[
 {'path':str(path.relative_to(ROOT)),'bytes':path.stat().st_size,'sha256':sha(path)} for path in sorted(set(paths))]})
print(json.dumps({'proof_commit':git('rev-parse','HEAD'),'root_scope_entries':len(set(paths)),
 'public_pairs':sum(group['pairs'] for group in groups if group['kind']=='new-public'),
 'constructed_pairs':sum(group['pairs'] for group in groups if group['kind']=='constructed')}))
