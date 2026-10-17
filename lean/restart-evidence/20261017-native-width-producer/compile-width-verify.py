from pathlib import Path
import hashlib,json,re
root=Path(__file__).resolve().parents[3]
base=Path(__file__).resolve().parent
source=root/'lean/MicroCFTA/SourceRecursiveIntersectionCompileWidth.lean'
assert hashlib.sha256(source.read_bytes()).hexdigest()=='443ff65d844653bf749e3f378bd83f3bbbfc41009e32525334d954f858f4113e'
assert source.read_bytes()==(base/'compile-width-direct-3.source.lean').read_bytes()
assert (base/'compile-width-direct-3.log').read_bytes()==b''
names=re.findall(r'^theorem ([^\s({:]+)',source.read_text(),re.M);assert len(names)==7
public=(base/'compile-width-public.lean').read_text()
for name in names:
 full='MicroCFTA.SourceRecursiveIntersectionCompileWidth.'+name
 assert '#print axioms '+full+'\n' in public and '#check @'+full+'\n' in public
for stem,pairs in [('compile-width-public',7),('compile-width-kernels',2)]:
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
assert 'Build completed successfully (1186 jobs).' in (base/'canonical-compile-width-1.log').read_text()
for p in [source,base/'compile-width-public.lean',base/'compile-width-kernels.lean',base/'compile-width-review.md']:
 raw=p.read_bytes();assert raw.endswith(b'\n') and not raw.endswith(b'\n\n'),p
manifest=base/'compile-width-manifest.json'
if manifest.exists():
 data=json.loads(manifest.read_text());assert len(data['files'])==data['file_count']
 for item in data['files']:
  p=root/item['path'];assert p.stat().st_size==item['bytes'],p
  assert hashlib.sha256(p.read_bytes()).hexdigest()==item['sha256'],p
print('PASS: frozen all-branch compiler; 7 public and 2 constructed-source integration pairs; standard axioms; canonical1186.')
