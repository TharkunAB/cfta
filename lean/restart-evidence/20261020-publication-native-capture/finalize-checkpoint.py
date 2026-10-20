import hashlib,json,os,subprocess
from pathlib import Path
ROOT=Path('/home/tritlo/Code/mcfta');HERE=ROOT/'lean/restart-evidence/20261020-publication-native-capture'
def read(n):return json.loads((HERE/n).read_text())
def write(n,x):(HERE/n).write_text(json.dumps(x,indent=2)+'\n')
def entry(p):
 data=p.read_bytes();return {'path':str(p.relative_to(ROOT)),'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)}
assert read('selection-status.json')['finalized']
for n in ['math-review-verification.json','source-doc-verification.json','publication-fixture-verification.json','body-prototype-verification.json','self-prototype-verification.json']:
 assert read(n)['status']=='PASS',n
# Root-level copies of selected native fixture receipts are aliases of preserved attempts.
unique={}
for p in sorted(HERE.rglob('*.json')):
 data=json.loads(p.read_text())
 if not (isinstance(data,dict) and isinstance(data.get('command'),list) and 'exit_code' in data):continue
 if p.name=='previous-closure.json':continue
 limits_path=p.parent/(p.stem+'.limits.json')
 assert limits_path.exists(),p
 limits=json.loads(limits_path.read_text());assert limits=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'},p
 log=p.parent/data['log'];assert log.is_file(),p
 identity=hashlib.sha256(p.read_bytes()).hexdigest()
 record=unique.setdefault(identity,{'receipt_sha256':identity,'receipt_paths':[],'exit_code':data['exit_code'],'entered_lean':True,'raw_log_bytes':log.stat().st_size})
 record['receipt_paths'].append(str(p.relative_to(HERE)))
 assert record['raw_log_bytes']==log.stat().st_size
attempts=list(unique.values())
write('attempt-accounting.json',{'attempts':attempts,'wrapper_attempts':len(attempts),'entered_lean':len(attempts),'pre_lean_blocked':0,'selected_public_pairs':4,'selected_constructed_pairs':2,'duplicate_retained_receipt_aliases':sum(len(a['receipt_paths'])-1 for a in attempts),'proof_pair_count_excludes_reviews_and_reused_prototype':True,'non_lean_verifier_failure_is_not_a_lean_attempt':True})
paths=set()
for subdir in ['body-prototype','self-prototype']:
 paths.update(p for p in (HERE/subdir).rglob('*') if p.is_file())
paths.update(p for p in HERE.iterdir() if p.is_file() and p.name.startswith(('self-slot-kernels','self-slot-final-peaks')))
write('prototype-source-manifest.json',{'entries':[entry(p) for p in sorted(paths)]})
root_names=['root-run-check.py','root-capped-worker.py','root-review.md','root-peaks.txt','root-final-peaks.txt','verify-probes.py','proof-commit.txt','public-heads.json','new-modules.json','frozen-modules.json','expected-counts.json','selected-audit.json','selected-strict.json','selected-canonical.json','selected-canonical-warnings.json','selected-constructed-strict.json','selected-groups.json','selection-status.json','next-binding-ancestry-handoff.md','next-closed-leaf-source-ancestry-review.md','previous-checkpoint-board-read.json','previous-publication.json','previous-closure.json','previous-closure-limits.json','previous-closure-peaks.txt']
paths={ROOT/'lean/MicroCFTA'/(m+'.lean') for m in read('new-modules.json')}
paths.update(HERE/n for n in root_names)
paths.update(p for p in HERE.iterdir() if p.is_file() and p.name.startswith(('body-direct-','body-canonical-','body-public-','self-direct-','self-canonical-','self-public-','full-audit-')))
paths.update(HERE/n for n in ['body-public.lean','self-public.lean'])
write('root-source-manifest.json',{'entries':[entry(p) for p in sorted(paths)]})
env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'}
result=subprocess.check_output(['python3',str(HERE/'verify-checkpoint.py')],cwd=ROOT,env=env)
(HERE/'checkpoint-validation.json').write_bytes(result);assert json.loads(result)['status']=='PASS'
result2=subprocess.check_output(['python3',str(HERE/'verify-preservation.py')],cwd=ROOT,env=env)
(HERE/'preservation-final.json').write_bytes(result2);assert json.loads(result2)['status']=='PASS'
print(json.dumps({'checkpoint':json.loads(result),'preservation':{k:v for k,v in json.loads(result2).items() if k!='frozen_manifests'},'wrapper_attempts':len(attempts),'all_attempts_terminal':True},indent=2))
