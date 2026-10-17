import hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
manifest=json.loads((HERE/'busy-owner-manifest.json').read_text())
for item in manifest['entries']:
 data=(ROOT/item['path']).read_bytes()
 assert len(data)==item['bytes'],item['path']
 assert hashlib.sha256(data).hexdigest()==item['sha256'],item['path']
source=ROOT/'lean/MicroCFTA/SourceCurrentOuterBusyOwners.lean'
assert source.read_bytes()==(HERE/'busy-owner-direct-4.source.lean').read_bytes()
assert (HERE/'busy-owner-direct-4.log').read_bytes()==b''
assert (HERE/'busy-owner-kernel-strict-1.log').read_bytes()==b''
assert not re.search(r'\bsorry\b|\baxiom\b|\bunsafe\b|set_option linter\.[^\n]*false',source.read_text())
canonical=(HERE/'busy-owner-canonical-1.log').read_text()
assert canonical.startswith('{"memory.max": "4294967296", "memory.high": "4294967296", "memory.swap.max": "0"}\n')
assert 'Build completed successfully (1413 jobs).' in canonical
assert 'error:' not in canonical
for stem,count,proofs in [('busy-owner-public-2',11,True),('busy-owner-kernels-2',2,False)]:
 code=(HERE/(stem+'.source.lean')).read_text()
 log=(HERE/(stem+'.log')).read_text()
 assert not re.search(r'error(?:\(|:)|warning(?:\(|:)|sorryAx|⋯|…|\.{3}|truncat|failed to pretty',log),stem
 checks=re.findall(r'^#check @(\S+)',code,re.M)
 assert len(checks)==count
 assert re.findall(r'^#print axioms (\S+)',code,re.M)==checks
 assert re.findall(r'^#print (?!axioms )(\S+)',code,re.M)==(checks if proofs else [])
 for option in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:
  assert 'set_option '+option in code
 blocks=re.findall(r'depends on axioms:\s*\[([^]]*)\]',log,re.S)
 assert len(blocks)+log.count('does not depend on any axioms')==count
 for block in blocks:
  axioms={re.sub(r'\.\{[^}]+\}','',x.strip()) for x in block.split(',') if x.strip()}
  assert axioms <= {'propext','Classical.choice','Quot.sound'},axioms
 assert json.loads((HERE/(stem+'.json')).read_text())['exit_code']==0
kernel=(HERE/'busy-owner-kernels-2.source.lean').read_text()
stripped='\n'.join(line for line in kernel.splitlines() if not line.startswith(('#check ','#print ')))+'\n'
assert (HERE/'busy-owner-kernel-strict-1.source.lean').read_text()==stripped
for n in [1,2,3]:
 assert json.loads((HERE/f'busy-owner-direct-{n}.json').read_text())['exit_code']==1
for path in HERE.glob('busy-owner-*.limits.json'):
 assert json.loads(path.read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
print(json.dumps({'status':'PASS','hashes':len(manifest['entries']),'public':11,'constructed':2,'strict_empty':True,'canonical_jobs':1413}))
