import hashlib,json,re,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
expected=json.loads((HERE/'expected-validation.json').read_text())
counts={}
for component in expected['components']:
 subprocess.run(['python3',str(HERE/(component+'-verify.py'))],cwd=ROOT,check=True,capture_output=True,text=True)
 manifest=json.loads((HERE/(component+'-manifest.json')).read_text())
 counts[component]=len(manifest['entries'])
modules=json.loads((HERE/'frozen-modules.json').read_text())
proof=(HERE/'proof-commit.txt').read_text().strip()
assert len(modules)==7
for name,digest in modules.items():
 path='lean/MicroCFTA/'+name+'.lean'
 assert sha(ROOT/path)==digest,name
 assert hashlib.sha256(subprocess.check_output(['git','show',proof+':'+path],cwd=ROOT)).hexdigest()==digest,name
 assert not re.search(r'\bsorry\b|\baxiom\b|\bunsafe\b|set_option linter\.[^\n]*false',(ROOT/path).read_text()),path
for module,stem in expected['strict_sources'].items():
 assert sha(HERE/(stem+'.source.lean'))==modules[module],module
 assert (HERE/(stem+'.log')).stat().st_size==0,stem
for name,count,printed in expected['groups']:
 source=(HERE/(name+'.source.lean')).read_text();log=(HERE/(name+'.log')).read_text()
 assert not re.search(r'error(?:\(|:)|warning(?:\(|:)|sorryAx|⋯|…|\.{3}|truncat|failed to pretty',log),name
 checks=re.findall(r'^#check @(\S+)',source,re.M)
 assert len(checks)==count,name
 assert re.findall(r'^#print axioms (\S+)',source,re.M)==checks,name
 assert re.findall(r'^#print (?!axioms )(\S+)',source,re.M)==(checks if printed or name in expected['integration_full_proof_groups'] else []),name
 for option in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:
  assert 'set_option '+option in source,(name,option)
 blocks=re.findall(r'depends on axioms:\s*\[([^]]*)\]',log,re.S)
 assert len(blocks)+log.count('does not depend on any axioms')==count,name
 for block in blocks:
  observed={re.sub(r'\.\{[^}]+\}','',v.strip()) for v in block.split(',') if v.strip()}
  assert observed<={'propext','Classical.choice','Quot.sound'},(name,observed)
audit=(HERE/'full-audit-1.log').read_text()
assert f"Checked axiom dependencies of {expected['audit_dependency_checks']} MicroCFTA theorems." in audit
assert f"Build completed successfully ({expected['audit_jobs']} jobs)." in audit
assert 'error:' not in audit
assert json.loads((HERE/'full-audit-1.json').read_text())['exit_code']==0
assert json.loads((HERE/'full-audit-1.limits.json').read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
assert subprocess.check_output(['git','show',proof+':lean/MicroCFTA/Audit.lean'],cwd=ROOT)==(ROOT/'lean/MicroCFTA/Audit.lean').read_bytes()
resources=json.loads((HERE/'resources-manifest.json').read_text())
for entry in resources['entries']:
 path=ROOT/entry['path']
 assert sha(path)==entry['sha256'],entry['path']
 assert path.stat().st_size==entry['bytes'],entry['path']
public=sum(count for _,count,printed in expected['groups'] if printed)
integrations=sum(count for _,count,printed in expected['groups'] if not printed)
assert public==expected['public_pairs']
assert integrations==expected['constructed_pairs']
assert public==expected['public_handwritten_heads']+expected['generated_constructors']
assert len(expected['groups'])==expected['probe_groups']
assert sum(counts.values())==expected['component_entries']
report={'status':'PASS',**expected,'component_entry_counts':counts,'resources_entries':len(resources['entries']),'hash_references':sum(counts.values())+len(resources['entries']),'source_modules':modules,'proof_commit':proof,'only_standard_axioms':True,'general_outer_progress_still_open':True,'new_haskell_behavior_patch':False}
print(json.dumps(report,indent=2))
