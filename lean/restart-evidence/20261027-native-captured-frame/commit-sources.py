from pathlib import Path
import hashlib,json,subprocess
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-native-captured-frame-20261027')
git=lambda *a:subprocess.check_output(['git',*a],cwd=root)
subprocess.run(['python3',str(area/'verify-checks.py')],check=True)
assert git('branch','--show-current').decode().strip()=='formalize'
assert git('rev-parse','HEAD').decode().strip()==(area/'base.txt').read_text().strip()
assert not git('diff','--cached','--name-only')
modules=json.loads((area/'modules.json').read_text()); paths=['lean/MicroCFTA/'+m+'.lean' for m in modules]+['lean/MicroCFTA/Audit.lean']
assert set(git('diff','--name-only').decode().splitlines())=={'lean/MicroCFTA/Audit.lean'}
assert set(git('ls-files','--others','--exclude-standard').decode().splitlines())==set(paths)-{'lean/MicroCFTA/Audit.lean'}
sources=area/'sources';sources.mkdir()
patch=git('diff','--binary','--','lean/MicroCFTA/Audit.lean')
for rel in paths:
 data=(root/rel).read_bytes();(sources/Path(rel).name).write_bytes(data)
 if rel!='lean/MicroCFTA/Audit.lean':
  result=subprocess.run(['git','diff','--no-index','--binary','--','/dev/null',rel],cwd=root,stdout=subprocess.PIPE)
  assert result.returncode==1;patch+=result.stdout
(area/'proof-change.patch').write_bytes(patch)
groups=[
 ('Prove native payload locality and neutral assignment foundations',modules[:3]+modules[5:6]),
 ('Preserve neutral assignments through actual incoming writes and folds',modules[3:5]+modules[6:9]),
 ('Compose neutral semantics through terminal and shallow child receipts',modules[9:14]),
 ('Carry canonical storage through actual ordinary alternative history',modules[14:16]),
 ('Restore captured-slot language through native expansion and finalization',modules[16:]+['Audit'])]

commits=[]
for message,selectedModules in groups:
 selected=['lean/MicroCFTA/'+m+'.lean' for m in selectedModules]
 subprocess.run(['git','add','--',*selected],cwd=root,check=True)
 assert set(git('diff','--cached','--name-only').decode().splitlines())==set(selected)
 for rel in selected:assert git('show',':'+rel)==(root/rel).read_bytes()
 subprocess.run(['git','diff','--cached','--check'],cwd=root,check=True)
 subprocess.run(['git','commit','-m',message],cwd=root,check=True)
 head=git('rev-parse','HEAD').decode().strip()
 for rel in selected:assert git('show',head+':'+rel)==(root/rel).read_bytes()
 commits.append({'commit':head,'message':message,'paths':selected})
(area/'source-commits.json').write_text(json.dumps(commits,indent=2)+'\n');print(json.dumps(commits,indent=2))
