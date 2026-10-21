import hashlib,json,shutil,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2]
def write(name,data):(HERE/name).write_text(json.dumps(data,indent=2)+'\n')
components=[]
for src,dst,verifier in [('mcfta-outer-merge-position-support','outer','outer-support-verify.py'),('mcfta-mu-position-store-investigation','native-investigation','verify.py'),('mcfta-outer-merge-support-independent-review','independent-review','verify.py'),('mcfta-supported-writer-investigation','writer-investigation','verify.py')]:
 destination=HERE/dst;assert not destination.exists();shutil.copytree('/tmp/'+src,destination)
 for mode in [[],['--live']]:subprocess.run(['/usr/bin/python3',str(destination/verifier),'--root',str(ROOT),*mode],cwd='/',check=True,stdout=subprocess.DEVNULL)
 components.append({'path':dst,'verifier':verifier,'extra':['--root',str(ROOT)],'live':True})
write('components.json',components)
name='lean/MicroCFTA/SourceCurrentOuterMergePositionSupport.lean';sha=hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
write('selected-sources.json',{name:{'sha256':sha}});write('frozen-modules.json',{Path(name).stem:sha})
write('selected-checks.json',{'strict':'outer-support-strict-1','audit':'audit-1','public':'outer/outer-support-public-1'})
support=HERE/'root-support';support.mkdir()
for stem in ['mcfta-outer-merge-support-baseline-1','mcfta-outer-merge-support-proof-push-1']:
 for suffix in ['json','log','limits.json','peaks.txt','source.py','usage.json']:
  source=Path('/tmp')/(stem+'.'+suffix);assert source.is_file(),source;shutil.copyfile(source,support/source.name)
previous=HERE/'previous-publication-support';previous.mkdir()
for pattern in ['mcfta-merge-positive-publication.json','mcfta-merge-positive-final-publication*','mcfta-merge-positive-final-push.log','mcfta-merge-positive-final-remote.txt','mcfta-merge-positive-board-readback.json','mcfta-merge-positive-seal-1.*','mcfta-merge-positive-support-1.*']:
 found=[p for p in Path('/tmp').glob(pattern) if p.is_file()];assert found,pattern
 for source in found:shutil.copyfile(source,previous/source.name)
print(json.dumps({'status':'PASS','components':len(components),'new_modules':1}))
