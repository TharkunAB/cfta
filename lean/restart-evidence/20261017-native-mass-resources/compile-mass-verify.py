from pathlib import Path
import hashlib,json,re
root=Path(__file__).resolve().parents[3]
base=Path(__file__).resolve().parent
source=root/'lean/MicroCFTA/SourceRecursiveIntersectionCompileMass.lean'
assert hashlib.sha256(source.read_bytes()).hexdigest()=='78b3f1797c112d78ac26b372d94bf3f2e5d6f61b2a92094900e73caeac402287'
assert source.read_bytes()==(base/'compile-mass-direct-3.source.lean').read_bytes()
assert (base/'compile-mass-direct-3.log').read_bytes()==b''
names=re.findall(r'^theorem ([^\s({:]+)',source.read_text(),re.M)
assert len(names)==14
public=(base/'compile-mass-public.lean').read_text()
for name in names:
 full='MicroCFTA.SourceRecursiveIntersectionCompileMass.'+name
 assert '#print axioms '+full+'\n' in public
 assert '#check @'+full+'\n' in public
for stem,pairs,attempt in [('compile-mass-public',14,1),('compile-mass-kernels',2,2)]:
 probe=base/(stem+'.lean')
 assert probe.read_bytes()==(base/(stem+'-'+str(attempt)+'.source.lean')).read_bytes()
 text=probe.read_text()
 assert text.count('#print axioms ')==pairs and text.count('#check @')==pairs
 for option in ['explicit','fullNames','proofs','universes','deepTerms']:
  assert 'set_option pp.'+option+' true\n' in text
 assert 'set_option pp.maxSteps 10000000\n' in text
 assert 'set_option linter.all true\n' in text
 log=(base/(stem+'-'+str(attempt)+'.log')).read_text()
 assert not re.search(r'error(?:\(|:)|warning:|sorryAx',log)
 assert len(re.findall(r'depends on axioms:|does not depend on any axioms',log))==pairs
 for group in re.findall(r'depends on axioms:\s*\[(.*?)\]',log,re.S):
  for axiom in group.split(','):
   assert re.sub(r'\.\{[^}]*\}','',axiom.strip()) in {'propext','Classical.choice','Quot.sound'}
assert 'Build completed successfully (1186 jobs).' in (base/'canonical-checked-compile-mass-1.log').read_text()
for p in [source,base/'compile-mass-public.lean',base/'compile-mass-kernels.lean',base/'compile-mass-review.md']:
 raw=p.read_bytes(); assert raw.endswith(b'\n') and not raw.endswith(b'\n\n'),p
manifest=base/'compile-mass-manifest.json'
if manifest.exists():
 data=json.loads(manifest.read_text());assert len(data['files'])==data['file_count']
 for item in data['files']:
  p=root/item['path'];assert p.stat().st_size==item['bytes'],p
  assert hashlib.sha256(p.read_bytes()).hexdigest()==item['sha256'],p
print('PASS: frozen production; 14 public and 2 actual integration pairs; standard axioms; canonical1186.')
