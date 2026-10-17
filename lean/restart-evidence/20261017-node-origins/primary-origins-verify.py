import hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
manifest=json.loads((HERE/'primary-origins-manifest.json').read_text())
for item in manifest['entries']:
 path=ROOT/item['path']
 assert len(path.read_bytes())==item['bytes'],item['path']
 assert hashlib.sha256(path.read_bytes()).hexdigest()==item['sha256'],item['path']
for name in ['primary-exposure-strict-final','primary-origins-direct-3']:
 assert (HERE/(name+'.log')).stat().st_size==0,name
 assert json.loads((HERE/(name+'.json')).read_text())['exit_code']==0,name
 assert json.loads((HERE/(name+'.limits.json')).read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'},name
for name,count in [('primary-exposure-canonical-1',1158),('primary-origins-canonical-1',1162)]:
 assert json.loads((HERE/(name+'.json')).read_text())['exit_code']==0,name
 assert f'Build completed successfully ({count} jobs).' in (HERE/(name+'.log')).read_text(),name
name='primary-origins-public-1'
source=(HERE/(name+'.source.lean')).read_text();log=(HERE/(name+'.log')).read_text()
checks=re.findall(r'^#check @(\S+)',source,re.M)
assert len(checks)==9
assert re.findall(r'^#print axioms (\S+)',source,re.M)==checks
assert re.findall(r'^#print (?!axioms )(\S+)',source,re.M)==checks
for option in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:
 assert 'set_option '+option in source,option
assert not re.search(r'error(?:\(|:)|warning(?:\(|:)|sorryAx|⋯|…|\.{3}|truncat|failed to pretty',log)
blocks=re.findall(r'depends on axioms:\s*\[([^]]*)\]',log,re.S)
assert len(blocks)+log.count('does not depend on any axioms')==9
for block in blocks:
 axioms={re.sub(r'\.\{[^}]+\}','',v.strip()) for v in block.split(',') if v.strip()}
 assert axioms<={'propext','Classical.choice','Quot.sound'},axioms
assert json.loads((HERE/(name+'.json')).read_text())['exit_code']==0
print(f"PASS {len(manifest['entries'])} entries; public9; two strict logs empty; canonical1158/1162; standard axioms only")
