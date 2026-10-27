from pathlib import Path
import json,subprocess
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-worker-arity-20261027')
groups=[('Preserve arity through probe selection and shared targets',['Selection','Merge','SharedTarget']),('Preserve arity through conjunction and class scans',['Conjunction','Seeded','Scan']),('Preserve arity through actual class edits and passes',['ClassEdit','ClassPass']),('Derive arity for completed local reduction and parent edges',['LocalReduction','Parent','Audit'])]
records=[]
for title,shorts in groups:
    assert not subprocess.check_output(['git','diff','--cached','--name-only','-z'],cwd=root)
    paths=['lean/MicroCFTA/'+('Audit' if s=='Audit' else 'SourcePruningEnumeration'+s+'Arity')+'.lean' for s in shorts]
    subprocess.run(['git','add','--',*paths],cwd=root,check=True)
    staged={x.decode() for x in subprocess.check_output(['git','diff','--cached','--name-only','-z'],cwd=root).split(b'\0') if x}
    assert staged==set(paths)
    subprocess.run(['git','diff','--cached','--check'],cwd=root,check=True)
    result=subprocess.run(['git','commit','-m',title],cwd=root,check=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root).decode().strip()
    records.append(dict(head=head,title=title,paths=paths,output=result.stdout.decode()))
    print(head+' '+title,flush=True)
(area/'source-commits-composition.json').write_text(json.dumps(records,indent=2)+'\n')
(area/'source-head.txt').write_text(head+'\n')
