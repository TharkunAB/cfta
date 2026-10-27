from pathlib import Path
import hashlib,json,subprocess
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-recursive-worker-arity-20261027')
groups=[('Retain arity at actual incoming query and dispatch endpoints',['IncomingQueryArity','IncomingNodeArity','IncomingNodeObservedArity','DispatchArity','FoldArity']),('Derive arity through terminal and ordered child traversal',['TerminalArity','ChildObservedArity','ChildResourcesArity','TraversalResourcesArity']),('Retain arity through selected edges and captured native heads',['SelectedEdgeResourcesArity','CapturedEdgeResourcesArity','NativeHeadResourcesArity'])]
reports=[]
for p in area.glob('strict-*/report.json'):
 r=json.loads(p.read_text())
 if r.get('exit_code')==0 and r.get('bytes')==0: reports.append(r)
records=[]
for title,shorts in groups:
 assert not subprocess.check_output(['git','diff','--cached','--name-only','-z'],cwd=root)
 paths=['lean/MicroCFTA/SourcePruningEnumeration'+s+'.lean' for s in shorts]
 for p in paths:
  data=(root/p).read_bytes();sha=hashlib.sha256(data).hexdigest();assert any(r.get('source_sha256')==sha for r in reports),p
 subprocess.run(['git','add','--',*paths],cwd=root,check=True)
 staged={s.decode() for s in subprocess.check_output(['git','diff','--cached','--name-only','-z'],cwd=root).split(b'\0') if s};assert staged==set(paths)
 subprocess.run(['git','diff','--cached','--check'],cwd=root,check=True)
 r=subprocess.run(['git','commit','-m',title],cwd=root,check=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root).decode().strip();records.append(dict(head=head,title=title,paths=paths,output=r.stdout.decode()));print(head+' '+title,flush=True)
(area/'source-commits-query-child-head.json').write_text(json.dumps(records,indent=2)+'\n')
