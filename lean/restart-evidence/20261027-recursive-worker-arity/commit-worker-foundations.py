from pathlib import Path
import json,subprocess
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-recursive-worker-arity-20261027')
groups=[('Retain arity through inherited allocation and resident binders',['PartialStepArity']),('Derive arity for all completed recursive worker families',['PartialActualArity','PartialWorkerArity']),('Derive arity through selected prefixes and captured ordinary receipts',['NativeNarrowArity','PrefixArity','OrdinaryReceiptArity'])]
records=[]
for title,shorts in groups:
 assert not subprocess.check_output(['git','diff','--cached','--name-only','-z'],cwd=root)
 paths=['lean/MicroCFTA/SourcePruningEnumeration'+s+'.lean' for s in shorts]
 subprocess.run(['git','add','--',*paths],cwd=root,check=True)
 staged={s.decode() for s in subprocess.check_output(['git','diff','--cached','--name-only','-z'],cwd=root).split(b'\0') if s};assert staged==set(paths)
 subprocess.run(['git','diff','--cached','--check'],cwd=root,check=True)
 result=subprocess.run(['git','commit','-m',title],cwd=root,check=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root).decode().strip();records.append(dict(head=head,title=title,paths=paths,output=result.stdout.decode()));print(head+' '+title,flush=True)
(area/'source-commits-foundations.json').write_text(json.dumps(records,indent=2)+'\n')
