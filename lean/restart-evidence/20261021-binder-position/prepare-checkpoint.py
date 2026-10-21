import hashlib,json,shutil,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2]
def write(name,data):(HERE/name).write_text(json.dumps(data,indent=2)+'\n')
components=[]
for src,dst,verifier in [('mcfta-binder-free-publication-positions','binder','binder-position-verify.py'),('mcfta-binder-position-independent-review','independent-review','verify.py')]:
 destination=HERE/dst;assert not destination.exists();shutil.copytree('/tmp/'+src,destination)
 for mode in [[],['--live']]:subprocess.run(['/usr/bin/python3',str(destination/verifier),'--root',str(ROOT),*mode],cwd='/',check=True,stdout=subprocess.DEVNULL)
 components.append({'path':dst,'verifier':verifier,'extra':['--root',str(ROOT)],'live':True})
write('components.json',components)
name='lean/MicroCFTA/SourceCurrentBinderFreePublicationPositions.lean';sha=hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
write('selected-sources.json',{name:{'sha256':sha}});write('frozen-modules.json',{Path(name).stem:sha})
write('selected-checks.json',{'strict':'binder-position-strict-1','audit':'audit-1','public':'binder/binder-position-public-1'})
support=HERE/'root-support';support.mkdir()
for stem in ['mcfta-binder-position-baseline-1','mcfta-binder-position-proof-push-1']:
 for suffix in ['json','log','limits.json','peaks.txt','source.py','usage.json']:
  source=Path('/tmp')/(stem+'.'+suffix);assert source.is_file(),source;shutil.copyfile(source,support/source.name)
previous=HERE/'previous-publication-support';previous.mkdir()
for pattern in ['mcfta-outer-merge-support-publication.json','mcfta-outer-merge-support-final-publication*','mcfta-outer-merge-support-final-push.log','mcfta-outer-merge-support-final-remote.txt','mcfta-outer-merge-support-board-readback.json','mcfta-outer-merge-support-seal-1.*','mcfta-outer-merge-support-support-1.*']:
 found=[p for p in Path('/tmp').glob(pattern) if p.is_file()];assert found,pattern
 for source in found:shutil.copyfile(source,previous/source.name)
print(json.dumps({'status':'PASS','components':len(components),'new_modules':1}))
