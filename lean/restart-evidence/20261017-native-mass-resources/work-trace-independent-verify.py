from pathlib import Path
import hashlib,json,re
root=Path(__file__).resolve().parents[3]
base=Path(__file__).resolve().parent
sources=[('SourceRecursiveIntersectionWorkMass','2683ffd0d82b254bd5a91bc6fe6d0fd929af4856afa1ec51aea749eb88f41b3e','work-mass-direct-3'),('SourceCurrentAllocatedRecursiveMassTrace','e9578e2d8fa8aea3eea4eab1dbf03eb8ba5476448976ff4fef1964518fda11b8','mass-trace-direct-4')]
names=[]
for module,digest,attempt in sources:
 p=root/f'lean/MicroCFTA/{module}.lean'
 assert hashlib.sha256(p.read_bytes()).hexdigest()==digest
 assert p.read_bytes()==(base/(attempt+'.source.lean')).read_bytes()
 assert (base/(attempt+'.log')).read_bytes()==b''
 names+=['MicroCFTA.'+module+'.'+n for n in re.findall(r'^(?:(?:noncomputable )?def|theorem|inductive) ([^\s({:]+)',p.read_text(),re.M)]
names+=['MicroCFTA.SourceRecursiveIntersectionWorkMass.Inputs.'+n for n in ['pure','edge','node','union']]
assert len(names)==30
public=(base/'work-trace-independent-public.lean').read_text()
for name in names:
 assert '#print axioms '+name+'\n' in public and '#check @'+name+'\n' in public
for stem,pairs in [('work-trace-independent-public',30),('work-trace-independent-kernels',1)]:
 p=base/(stem+'.lean');assert p.read_bytes()==(base/(stem+'-1.source.lean')).read_bytes()
 text=p.read_text();assert text.count('#print axioms ')==pairs and text.count('#check @')==pairs
 for opt in ['explicit','fullNames','proofs','universes','deepTerms']:
  assert 'set_option pp.'+opt+' true\n' in text
 assert 'set_option pp.maxSteps 10000000\n' in text and 'set_option linter.all true\n' in text
 log=(base/(stem+'-1.log')).read_text()
 assert not re.search(r'error(?:\(|:)|warning:|sorryAx',log)
 assert len(re.findall(r'depends on axioms:|does not depend on any axioms',log))==pairs
 for group in re.findall(r'depends on axioms:\s*\[(.*?)\]',log,re.S):
  for axiom in group.split(','):
   assert re.sub(r'\.\{[^}]*\}','',axiom.strip()) in {'propext','Classical.choice','Quot.sound'}
for name,jobs in [('canonical-work-mass-2.log',1181),('canonical-mass-trace-2.log',1205)]:
 assert f'Build completed successfully ({jobs} jobs).' in (base/name).read_text()
for p in [base/'work-trace-independent-public.lean',base/'work-trace-independent-kernels.lean',base/'work-trace-independent-review.md']:
 raw=p.read_bytes();assert raw.endswith(b'\n') and not raw.endswith(b'\n\n'),p
manifest=base/'work-trace-independent-manifest.json'
if manifest.exists():
 data=json.loads(manifest.read_text());assert len(data['files'])==data['file_count']
 for item in data['files']:
  p=root/item['path'];assert p.stat().st_size==item['bytes'],p
  assert hashlib.sha256(p.read_bytes()).hexdigest()==item['sha256'],p
print('PASS: frozen WorkMass and MassTrace; 30 public pairs and 1 own two-step mixed prefix kernel; standard axioms.')
