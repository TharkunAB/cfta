from pathlib import Path
import hashlib,json,subprocess
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-recursive-driver-arity-20261027')
groups=[('Derive actual arity histories from each output heap', ['HistoryPost', 'HistoryOutputArity', 'FiniteHistoryResourcesArity']), ('Prove rendered original acceptance from initial arity', ['FiniteHistoryRenderingArity'])]
receipts=[json.loads(p.read_text()) for p in area.glob('strict-*/report.json')];records=[]
for title,shorts in groups:
 assert not subprocess.check_output(['git','diff','--cached','--name-only','-z'],cwd=root)
 paths=['lean/MicroCFTA/SourcePruningEnumeration'+s+'.lean' for s in shorts]
 for p in paths:
  sha=hashlib.sha256((root/p).read_bytes()).hexdigest();assert any(r['exit_code']==0 and r['bytes']==0 and r['source_sha256']==sha for r in receipts),p
 subprocess.run(['git','add','--',*paths],cwd=root,check=True)
 staged={s.decode() for s in subprocess.check_output(['git','diff','--cached','--name-only','-z'],cwd=root).split(b'\0') if s};assert staged==set(paths)
 subprocess.run(['git','diff','--cached','--check'],cwd=root,check=True)
 r=subprocess.run(['git','commit','-m',title],cwd=root,check=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root).decode().strip();records.append({'title':title,'head':head,'paths':paths,'output':r.stdout.decode()});print(head+' '+title,flush=True)
(area/'source-commits-history-render.json').write_text(json.dumps(records,indent=2)+'\n')

assert not subprocess.check_output(['git','diff','--cached','--name-only','-z'],cwd=root)
subprocess.run(['git','add','--','lean/MicroCFTA/Audit.lean'],cwd=root,check=True)
subprocess.run(['git','diff','--cached','--check'],cwd=root,check=True)
r=subprocess.run(['git','commit','-m','Audit derived finite histories and original acceptance'],cwd=root,check=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root).decode().strip()
(area/'source-head.txt').write_text(head+'\n')
(area/'source-commit-audit.json').write_text(json.dumps({'head':head,'output':r.stdout.decode()},indent=2)+'\n')
print(head+' Audit derived finite histories and original acceptance')
