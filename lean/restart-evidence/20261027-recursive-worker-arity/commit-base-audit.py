from pathlib import Path
import json,subprocess
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-recursive-worker-arity-20261027')
groups=[('Retain full native head bounds with arity',['lean/MicroCFTA/SourcePruningEnumerationNativeHeadBoundedResourcesArity.lean']),('Retain actual endpoint arity in the zero-depth finite driver',['lean/MicroCFTA/SourcePruningEnumerationFiniteArityContract.lean']),('Audit recursive worker and captured-head arity proofs',['lean/MicroCFTA/Audit.lean'])]
records=[]
for title,paths in groups:
 assert not subprocess.check_output(['git','diff','--cached','--name-only','-z'],cwd=root)
 subprocess.run(['git','add','--',*paths],cwd=root,check=True)
 staged={s.decode() for s in subprocess.check_output(['git','diff','--cached','--name-only','-z'],cwd=root).split(b'\0') if s};assert staged==set(paths)
 subprocess.run(['git','diff','--cached','--check'],cwd=root,check=True)
 r=subprocess.run(['git','commit','-m',title],cwd=root,check=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root).decode().strip();records.append(dict(head=head,title=title,paths=paths,output=r.stdout.decode()));print(head+' '+title,flush=True)
(area/'source-commits-base-audit.json').write_text(json.dumps(records,indent=2)+'\n');(area/'source-head.txt').write_text(head+'\n')
