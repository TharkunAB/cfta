import hashlib,json,shutil,subprocess
from pathlib import Path
H=Path(__file__).resolve().parent
R=H.parents[2]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(n,d):(H/n).write_text(json.dumps(d,indent=2)+'\n')
components=[('local-branches','/tmp/mcfta-actual-local-branch-cases','local-branch-verify.py'),('parent-branches','/tmp/mcfta-actual-parent-branch-cases','parent-branch-verify.py'),('plain-rows','/tmp/mcfta-outer-plain-row-shapes','plain-row-verify.py'),('plain-review','/tmp/mcfta-outer-plain-progress-review','verify.py'),('fixture-review-old','/tmp/mcfta-plain-owner-fixture-review','verify.py')]
for name,source,verifier in components:
 dst=H/name
 assert not dst.exists()
 shutil.copytree(source,dst)
 candidates=list(dst.glob('*verify.py'))
 assert len(candidates)==1,(name,candidates)
 subprocess.run(['/usr/bin/python3',str(candidates[0]),'--live'],check=True,cwd='/',stdout=subprocess.DEVNULL)
write('components.json',[{'path':n,'verifier':list((H/n).glob('*verify.py'))[0].name,'live':True} for n,_,_ in components])
for source in ['/tmp/mcfta-outer-top-owner-assessment.md','/tmp/mcfta-outer-top-owner-assessment-source-pins.json']:
 p=Path(source)
 if p.exists():shutil.copyfile(p,H/p.name)
support=H/'root-support';support.mkdir()
for stem in ['mcfta-outer-owner-baseline-1','mcfta-outer-owner-proof-push-1']:
 for suffix in ['json','log','limits.json','peaks.txt','source.py','usage.json']:
  p=Path('/tmp')/(stem+'.'+suffix);assert p.exists(),p;shutil.copyfile(p,support/p.name)
previous=H/'previous-publication-support';previous.mkdir()
for pattern in ['mcfta-warm-final-publication*','mcfta-warm-final-push.log','mcfta-warm-final-remote.txt','mcfta-warm-board-readback.json','mcfta-warm-seal-2.*','mcfta-warm-seal-readback-1.*']:
 for p in Path('/tmp').glob(pattern):
  if p.is_file():shutil.copyfile(p,previous/p.name)
sources={}
for module in ['SourceCurrentActualLocalBranchCases','SourceCurrentActualParentBranchCases','SourceCurrentOuterPlainRowShapes','SourceCurrentOuterPlainOwnerProgress']:
 source='lean/MicroCFTA/'+module+'.lean';sources[source]={'sha256':sha(R/source)}
write('selected-sources.json',sources)
write('frozen-modules.json',{Path(n).stem:v['sha256'] for n,v in sources.items()})
write('selected-checks.json',{'root_strict':'owner-strict-1','root_public':'owner-public-1','canonical':'owner-canonical-1','audit':'audit-2','fixture_strict':'fixture-strict-5','fixture_public':'fixture-public-2','fixture_source':'PlainOwnerFixture.lean','fixture_sha256':sha(H/'PlainOwnerFixture.lean'),'unselected_successes':['audit-1','fixture-strict-4'],'incomplete_printer':'fixture-public-1'})
print(json.dumps({'status':'PASS','components':len(components),'proof':(H/'proof-commit.txt').read_text().strip(),'source_files':len(sources)}))
