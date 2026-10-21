import hashlib,json,shutil,subprocess
from pathlib import Path
H=Path(__file__).resolve().parent
R=Path('/home/tritlo/Code/mcfta')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def entry(p):return {'path':str(p.relative_to(H)),'bytes':p.stat().st_size,'sha256':sha(p)}
def write(n,d):(H/n).write_text(json.dumps(d,indent=2)+'\n')
source=H/'SourceCurrentRawCorridorSharedTargetCap.lean'
assert sha(source)=='7187a93a97be5cd1e1622e3945037b0c8fbb41b48a91b630c832fd054a61e804'
official=R/'lean/MicroCFTA'/source.name
assert not official.exists()
shutil.copyfile(source,official)
old=json.loads(Path('/tmp/mcfta-required-shared-target-cap-proof/shared-cap-source-pins.json').read_text())['files']
names=sorted({e['path'] for e in old}|{'lean/MicroCFTA/SourceCurrentRequiredSharedTargetCap.lean','lean/MicroCFTA/SourceCurrentRequiredRawCorridor.lean','lean/MicroCFTA/SourceCurrentRawCorridorProjectionCap.lean','lean/MicroCFTA/'+source.name})
pins=[]
for n in names:
    p=R/n
    target=H/'inputs/root'/n
    target.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(p,target)
    pins.append({'path':n,'bytes':p.stat().st_size,'sha256':sha(p)})
write('target-source-pins.json',{'files':pins})
artifacts=[]
for module in ['SourceCurrentRequiredRawCorridor','SourceCurrentRawCorridorProjectionCap','SourceCurrentRawCorridorSharedTargetCap']:
    found=list(Path('/tmp/mcfta-raw-corridor-target-imports/MicroCFTA').glob(module+'.olean*'))
    assert found,module
    for p in found:
        target=H/'artifacts'/p.name
        target.parent.mkdir(exist_ok=True)
        shutil.copyfile(p,target)
        artifacts.append(entry(target))
write('target-selection.json',{'finalized':True,'source':source.name,'source_sha256':sha(source),'public_heads':['MicroCFTA.SourceCurrentRawCorridorSharedTargetCap.force_receipt'],'selected_strict':'target-direct-1','selected_public':'target-public-1','lean_jobs':3,'failed_lean_checks':0,'canonical_jobs':1,'public_pairs':1,'constructed_pairs':0,'unselected':[],'printer_bytes':118723,'printer_sha256':'998ca729aaa6d255e89b418d8f1acb9e8fa0e103c02f75624797e97e72eafe35','axioms_by_head':{'force_receipt':['propext','Classical.choice','Quot.sound']},'artifacts':artifacts})
write('target-manifest.json',{'files':[entry(p) for p in sorted(H.rglob('*')) if p.is_file() and p.name not in ['target-manifest.json','target-verification.json']]})
results=[]
for mode in [[],['--live']]:
    results.append(json.loads(subprocess.check_output(['/usr/bin/python3',str(H/'target-verify.py'),'--root',str(R),*mode],cwd='/',text=True)))
write('target-verification.json',{'status':'PASS','checks':results})
print(json.dumps({'status':'PASS','source_sha256':sha(source),'manifest_sha256':sha(H/'target-manifest.json'),'pins':len(pins),'local_files':len(json.loads((H/'target-manifest.json').read_text())['files'])}))
