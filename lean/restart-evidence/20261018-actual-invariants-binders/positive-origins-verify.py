"""Check the positive guard origin evidence without running Lean."""
import hashlib,json,re,runpy
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
manifest=json.loads((HERE/'positive-origins-manifest.json').read_text())
for entry in manifest['entries']:
 path=ROOT/entry['path']
 assert sha(path)==entry['sha256'] and path.stat().st_size==entry['bytes'],entry['path']
assert sha(ROOT/manifest['production'])==manifest['source_sha256']
for stem in manifest['selected_runs']:
 meta=json.loads((HERE/(stem+'.json')).read_text())
 assert meta['exit_code']==0,stem
 limits=json.loads((HERE/meta['limits']).read_text())
 assert limits=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'},stem
 if 'source' in meta:
  assert sha(HERE/meta['source'])==meta['sha256'],stem
  assert meta['command'][-1]==str(HERE/meta['source']),stem
for stem in ['positive-origins-direct-3','positive-origins-kernels-2']:
 assert not (HERE/(stem+'.log')).read_bytes(),stem
assert sha(HERE/'positive-origins-direct-3.source.lean')==manifest['source_sha256']
canonical=(HERE/'positive-origins-canonical-1.log').read_text()
assert 'Build completed successfully (1349 jobs).' in canonical
assert len(re.findall(r'^warning:',canonical,re.M))==1
assert 'InternedFreshOrdinaryClosedCompletion.lean:24:5' in canonical
assert 'error:' not in canonical
check=runpy.run_path(str(HERE/'verify-probes.py'))['check_group']
for stem,pairs,kind in [('positive-origins-public-1',7,'new-public'),('positive-origins-kernels-public-1',1,'constructed')]:
 check(dict(name=stem,pairs=pairs,kind=kind,full_proof=True))
assert sha(HERE/'positive-origins-kernels.lean')==sha(HERE/'positive-origins-kernels-2.source.lean')
assert (HERE/'positive-origins-kernels-public-1.source.lean').read_bytes().startswith((HERE/'positive-origins-kernels-2.source.lean').read_bytes())
for stem in ['positive-origins-direct-1','positive-origins-kernels-1']:
 meta=json.loads((HERE/(stem+'.json')).read_text())
 assert meta['exit_code']==1 and sha(HERE/meta['source'])==meta['sha256']
print(json.dumps(dict(status='PASS',entries=len(manifest['entries']),public_pairs=7,constructed_pairs=1,strict_empty=True,canonical_jobs=1349)))
