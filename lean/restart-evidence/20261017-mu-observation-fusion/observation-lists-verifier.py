from pathlib import Path
import hashlib,json,re
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def meta(stem):
 m=json.loads((HERE/(stem+'.json')).read_text())
 assert m['exit_code']==0,stem
 assert json.loads((HERE/m['limits']).read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'},stem
 return m
def probes(group):
 m=meta(group['stem']); source=(HERE/m['source']).read_text(); log=(HERE/m['log']).read_text()
 assert sha(HERE/m['source'])==m['sha256']
 for option in ['set_option linter.all true','set_option pp.explicit true','set_option pp.fullNames true','set_option pp.proofs true','set_option pp.proofs.threshold 254','set_option pp.universes true','set_option pp.deepTerms true','set_option pp.maxSteps 10000000']:
  assert option in source,(group['stem'],option)
 assert len(re.findall(r'^#check @',source,re.M))==len(group['names'])
 assert len(re.findall(r'^#print axioms ',source,re.M))==len(group['names'])
 if group['full_proof']:
  assert len(re.findall(r'^#print (?!axioms )',source,re.M))==len(group['names'])
 assert not re.search(r': (?:error|warning):|sorryAx|failed to pretty print|…|\.\.\.',log),group['stem']
 for name in group['names']:
  found=re.search(re.escape("'"+name+"' depends on axioms: [")+r'(.*?)\]',log,re.S)
  assert found,(group['stem'],name)
  axioms={re.sub(r'\.\{[^}]*\}','',x.strip()) for x in found[1].split(',') if x.strip()}
  assert axioms<={'propext','Classical.choice','Quot.sound'},(name,axioms)

m=json.loads((HERE/'observation-lists-manifest.json').read_text())
for item in m['entries']:
 path=ROOT/item['path']; assert path.stat().st_size==item['bytes']; assert sha(path)==item['sha256'],str(path)
strict=meta('observation-lists-direct-1')
assert not (HERE/strict['log']).read_bytes()
assert sha(HERE/strict['source'])==sha(ROOT/'lean/MicroCFTA/SourceCurrentOpenObservationLists.lean')
canonical=meta('observation-lists-canonical-1')
assert 'Build completed successfully (546 jobs).' in (HERE/canonical['log']).read_text()
for group in m['probe_groups']:probes(group)
print(f"PASS {len(m['entries'])} immutable entries; 2 public pairs; 1 pure integration; standard axioms; caps4G/4G/0")
