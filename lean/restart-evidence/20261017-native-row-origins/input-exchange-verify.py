from pathlib import Path
import hashlib,json,re
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
manifest=json.loads((HERE/'input-exchange-manifest.json').read_text())
for entry in manifest['entries']:
 path=ROOT/entry['path']
 assert path.is_file(),entry['path']
 data=path.read_bytes()
 assert len(data)==entry['bytes'],entry['path']
 assert hashlib.sha256(data).hexdigest()==entry['sha256'],entry['path']
validation=json.loads((HERE/'input-exchange-validation.json').read_text())
assert (HERE/'input-exchange-direct-2.log').stat().st_size==0
for stem in ['input-exchange-direct-2','input-exchange-canonical-1','input-exchange-public-1','input-exchange-kernels-3']:
 meta=json.loads((HERE/(stem+'.json')).read_text())
 assert meta['exit_code']==0,stem
 assert (HERE/(stem+'.caps')).read_text().splitlines()==['4294967296','4294967296','0'],stem
for key in ['public','integration']:
 group=validation[key]; stem=group['stem']
 source=(HERE/(stem+'.source.lean')).read_text()
 output=(HERE/(stem+'.log')).read_text()
 for option in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.universes true','pp.deepTerms true','pp.proofs.threshold 254','pp.maxSteps 10000000']:
  assert 'set_option '+option+'\n' in source,(stem,option)
 assert not re.search(r'error:|error\(|warning:|sorryAx|⋯|declaration uses',output),stem
 assert source.count('#check @')==source.count('#print axioms ')==group['pairs'],stem
 assert output.count('depends on axioms:')==group['pairs'],stem
 if key=='public':
  assert len(re.findall(r'^#print (?!axioms)',source,re.M))==group['pairs']
 for dependencies in re.findall(r'depends on axioms: \[(.*?)\]',output,re.S):
  for name in dependencies.split(','):
   name=re.sub(r'\.\{[^}]*\}','',name.strip())
   assert name in ['propext','Classical.choice','Quot.sound'],(stem,name)
assert 'Build completed successfully (322 jobs).' in (HERE/'input-exchange-canonical-1.log').read_text()
production=ROOT/validation['production']
assert production.read_bytes()==(HERE/'input-exchange-direct-2.source.lean').read_bytes()
print('PASS',len(manifest['entries']),'hashed entries; strict empty; canonical322; public4; constructed integrations2; standard axioms only')
