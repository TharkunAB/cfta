import json,shutil,subprocess
from pathlib import Path
H=Path(__file__).resolve().parent
for p in Path('/tmp').glob('mcfta-actual-branch-independent-review*'):
 if p.is_file():shutil.copyfile(p,H/p.name)
for p in Path('/tmp').glob('mcfta-outer-top-owner-assessment*'):
 if p.is_file() and not (H/p.name).exists():shutil.copyfile(p,H/p.name)
src=Path('/tmp/mcfta-plain-owner-final-fixture-review');dst=H/'fixture-review'
assert src.is_dir() and not dst.exists();shutil.copytree(src,dst)
verifiers=list(dst.glob('*verify.py'));assert len(verifiers)==1
subprocess.run(['/usr/bin/python3',str(verifiers[0]),'--live'],check=True,cwd='/',stdout=subprocess.DEVNULL)
components=json.loads((H/'components.json').read_text());components.append({'path':'fixture-review','verifier':verifiers[0].name,'live':True})
(H/'components.json').write_text(json.dumps(components,indent=2)+'\n')
for stem in ['mcfta-outer-owner-archive-1','mcfta-outer-owner-archive-2']:
 for suffix in ['json','log','limits.json','peaks.txt','source.py','usage.json']:
  p=Path('/tmp')/(stem+'.'+suffix);assert p.is_file();shutil.copyfile(p,H/'root-support'/p.name)
print(json.dumps({'status':'PASS','components':len(components)}))
