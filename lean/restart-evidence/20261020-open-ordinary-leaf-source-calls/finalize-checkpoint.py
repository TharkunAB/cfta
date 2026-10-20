import hashlib,json,os,re,subprocess
from pathlib import Path
ROOT=Path('/home/tritlo/Code/mcfta');HERE=ROOT/'lean/restart-evidence/20261020-open-ordinary-leaf-source-calls'
def read(n):return json.loads((HERE/n).read_text())
def write(n,x):(HERE/n).write_text(json.dumps(x,indent=2)+'\n')
def entry(p):
 d=p.read_bytes();return {'path':str(p.relative_to(ROOT)),'sha256':hashlib.sha256(d).hexdigest(),'bytes':len(d)}
assert read('selection-status.json')['finalized']
for n in ['math-review-verification.json','source-doc-verification.json','fixture-verification.json','counterexample-verification.json','prototype-verification.json']:assert read(n)['status']=='PASS',n
attempts=[]
for p in sorted(HERE.rglob('*.json')):
 if not re.search(r'(?:-(?:direct|public|canonical)-[0-9]+|full-audit-[0-9]+)\.json$',p.name):continue
 d=json.loads(p.read_text());assert isinstance(d.get('command'),list) and 'exit_code' in d,p
 assert Path(d['command'][0]).name in ['lean','lake']
 limits=json.loads((p.parent/(p.stem+'.limits.json')).read_text());assert limits=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'},p
 log=p.parent/d['log'];assert log.is_file()
 attempts.append({'stem':p.stem,'exit_code':d['exit_code'],'entered_lean':True,'raw_log_bytes':log.stat().st_size})
assert len(attempts)==19 and sum(a['exit_code']!=0 for a in attempts)==8
write('attempt-accounting.json',{'attempts':attempts,'wrapper_attempts':len(attempts),'entered_lean':len(attempts),'pre_lean_blocked':0,'selected_public_pairs':1,'selected_constructed_pairs':2,'proof_pair_count_excludes_reviews_and_reused_prototype':True,'non_lean_verifier_failure_is_not_a_lean_attempt':True,'raw_empty_rejected_verifier_output_retained':'union-leaf-verifier-attempt-1-verification.json'})
proto=Path('/tmp/mcfta-open-ordinary-leaf-source-calls');paths=[]
for p in proto.rglob('*'):
 if p.is_file():
  target=HERE/p.relative_to(proto);assert target.read_bytes()==p.read_bytes();paths.append(target)
write('prototype-source-manifest.json',{'entries':[entry(p) for p in sorted(paths)]})
names=['root-run-check.py','root-capped-worker.py','root-review.md','root-peaks.txt','root-final-peaks.txt','verify-probes.py','proof-commit.txt','public-heads.json','new-modules.json','frozen-modules.json','expected-counts.json','selected-audit.json','selected-strict.json','selected-canonical.json','selected-canonical-warnings.json','selected-constructed-strict.json','selected-groups.json','selection-status.json','next-binding-ancestry-handoff.md','next-source-leaf-general-composition-review.md','previous-checkpoint-board-read.json','previous-publication.json','previous-closure.json','previous-closure-limits.json','previous-closure-peaks.txt']
paths={ROOT/'lean/MicroCFTA'/(m+'.lean') for m in read('new-modules.json')};paths.update(HERE/n for n in names)
paths.update(p for p in HERE.iterdir() if p.is_file() and p.name.startswith(('leaf-direct-','leaf-canonical-','leaf-public-','full-audit-')));paths.add(HERE/'leaf-public.lean')
write('root-source-manifest.json',{'entries':[entry(p) for p in sorted(paths)]})
env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'}
for script,out in [('verify-checkpoint.py','checkpoint-validation.json'),('verify-preservation.py','preservation-final.json')]:
 data=subprocess.check_output(['python3',str(HERE/script)],cwd=ROOT,env=env);assert json.loads(data)['status']=='PASS';(HERE/out).write_bytes(data)
print(json.dumps({'checkpoint':read('checkpoint-validation.json'),'preservation':{k:v for k,v in read('preservation-final.json').items() if k!='frozen_manifests'},'wrapper_attempts':len(attempts),'failed_elaboration_attempts':8,'all_attempts_terminal':True},indent=2))
