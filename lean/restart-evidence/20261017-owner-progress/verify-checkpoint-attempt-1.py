import hashlib,json,re,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
resources=json.loads((HERE/'resources-manifest.json').read_text())
for item in resources['entries']:
 data=(ROOT/item['path']).read_bytes()
 assert len(data)==item['bytes'],item['path']
 assert sha(ROOT/item['path'])==item['sha256'],item['path']
components=['outer-key','busy-owner','edge-idle','guard-growth','copied-warm']
counts=[]
for name in components:
 subprocess.run(['python3',str(HERE/(name+'-verify.py'))],cwd=ROOT,check=True,capture_output=True,text=True)
 counts.append(len(json.loads((HERE/(name+'-manifest.json')).read_text())['entries']))
modules=json.loads((HERE/'frozen-modules.json').read_text())
proof=(HERE/'proof-commit.txt').read_text().strip()
for name,expected in modules.items():
 path='lean/MicroCFTA/'+name+'.lean'
 assert sha(ROOT/path)==expected
 blob=subprocess.check_output(['git','show',proof+':'+path],cwd=ROOT)
 assert hashlib.sha256(blob).hexdigest()==expected
 assert not re.search(r'\bsorry\b|\baxiom\b|\bunsafe\b|set_option linter\.[^\n]*false',(ROOT/path).read_text()),path
audit=(HERE/'lean-audit.log').read_text()
assert audit.startswith('4294967296\n4294967296\n0\n')
assert 'Checked axiom dependencies of 67182 MicroCFTA theorems.' in audit
assert 'Build completed successfully (3040 jobs).' in audit
assert 'error:' not in audit
assert json.loads((HERE/'audit-execution.json').read_text())['exit_code']==0
assert subprocess.check_output(['git','show',proof+':lean/MicroCFTA/Audit.lean'],cwd=ROOT)==(ROOT/'lean/MicroCFTA/Audit.lean').read_bytes()
groups=[('outer-key-public-1',4,True),('outer-key-kernels-3',2,False),('busy-owner-public-2',11,True),('busy-owner-kernels-2',2,False),('edge-idle-public-1',12,True),('edge-idle-kernels-2',3,False),('guard-growth-public-1',4,True),('copied-warm-public-1',22,True),('copied-warm-kernels-2',2,False)]
for name,count,proofs in groups:
 code=(HERE/(name+'.source.lean')).read_text();log=(HERE/(name+'.log')).read_text()
 assert not re.search(r'error(?:\(|:)|warning(?:\(|:)|sorryAx|⋯|…|\.{3}|truncat|failed to pretty',log),name
 checks=re.findall(r'^#check @(\S+)',code,re.M)
 assert len(checks)==count,name
 assert re.findall(r'^#print axioms (\S+)',code,re.M)==checks
 assert re.findall(r'^#print (?!axioms )(\S+)',code,re.M)==(checks if proofs else [])
 for option in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:
  assert 'set_option '+option in code,(name,option)
 blocks=re.findall(r'depends on axioms:\s*\[([^]]*)\]',log,re.S)
 assert len(blocks)+log.count('does not depend on any axioms')==count,name
 for block in blocks:
  observed={re.sub(r'\.\{[^}]+\}','',name.strip()) for name in block.split(',') if name.strip()}
  assert observed <= {'propext','Classical.choice','Quot.sound'},observed
expected=json.loads((HERE/'expected-validation.json').read_text())
assert sum(counts)==expected['component_entries']==243
assert len(groups)==expected['probe_groups']==9
assert sum(count for _,count,_ in groups)==expected['probe_pairs']==62
assert sum(count for _,count,proofs in groups if proofs)==expected['public_pairs']==53
assert expected['public_handwritten_heads']+expected['generated_constructors']==53
report={'status':'PASS',**expected,'component_entry_counts':dict(zip(components,counts)),'resources_entries':len(resources['entries']),'hash_references':sum(counts)+len(resources['entries']),'source_modules':modules,'proof_commit':proof,'only_standard_axioms':True,'no_general_completion_claim':True}
print(json.dumps(report,indent=2))
