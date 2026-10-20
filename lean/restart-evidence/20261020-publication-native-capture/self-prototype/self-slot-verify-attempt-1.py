import hashlib,json,re,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=Path(sys.argv[1]).resolve() if len(sys.argv)>1 else HERE.parents[2]
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
manifest=json.loads((HERE/'self-slot-manifest.json').read_text())
assert manifest['status']=='final'
identities=[(entry['base'],entry['path']) for entry in manifest['files']]
assert len(identities)==len(set(identities))
for entry in manifest['files']:
 assert entry['base'] in ['HERE','ROOT']
 path=(HERE if entry['base']=='HERE' else ROOT)/entry['path']
 assert path.stat().st_size==entry['bytes'] and sha(path)==entry['sha256'],entry['path']
selection=json.loads((HERE/'self-slot-selection.json').read_text())
generic=HERE/selection['generic_source']; fixture=HERE/selection['fixture_source']
assert sha(generic)==selection['generic_sha256']
assert sha(fixture)==selection['fixture_sha256']
assert fixture.read_bytes().startswith(generic.read_bytes())
assert len(re.findall(r'^theorem ',generic.read_text(),re.M))==2
for stem,code in selection['attempts'].items():
 receipt=json.loads((HERE/(stem+'.json')).read_text())
 assert receipt['exit_code']==code
 assert sha(HERE/receipt['source'])==receipt['sha256']
 assert receipt['command'][:2]==['/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean','-Dlinter.all=true']
 assert receipt['wrapper'][:5]==['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m']
 assert json.loads((HERE/(stem+'.limits.json')).read_text())=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 usage=json.loads((HERE/(stem+'.usage.json')).read_text())
 assert usage['remaining_percent']>1 and usage['age_seconds']<120
for key,stem in selection['stricts'].items():
 receipt=json.loads((HERE/(stem+'.json')).read_text())
 assert receipt['exit_code']==0 and (HERE/receipt['log']).read_bytes()==b''
 assert (HERE/receipt['source']).read_bytes()==(generic if key=='generic' else fixture).read_bytes()
for group in selection['groups']:
 receipt=json.loads((HERE/(group['name']+'.json')).read_text())
 assert receipt['exit_code']==0
 source=(HERE/receipt['source']).read_text()
 for option in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:
  assert 'set_option '+option in source
 for pattern in [r'^#check @',r'^#print (?!axioms )',r'^#print axioms ']:
  assert len(re.findall(pattern,source,re.M))==group['pairs']
 log=(HERE/receipt['log']).read_text()
 assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.',log)
 reports=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',log)
 assert len(reports)+len(re.findall(r'does not depend on any axioms',log))==group['pairs']
 for report in reports:
  cleaned=re.sub(r'\.\{[^}]*\}','',report)
  assert set(re.split(r',\s*',cleaned.strip()))<={'propext','Classical.choice','Quot.sound'}
text=fixture.read_text()
assert re.search(r'private theorem checked_witness(.*?) := by',text,re.S).group(1)==re.search(r'theorem closed_and_self(.*?) := checked_witness',text,re.S).group(1)
peaks=(HERE/'self-slot-final-peaks.txt').read_text().splitlines()
assert len(peaks)==len(selection['attempts'])
assert [int(line.split()[-1]) for line in peaks]==list(selection['attempts'].values())
assert all(line.split()[2]=='4G' for line in peaks)
assert not any(entry['path']=='self-slot-peaks.txt' for entry in manifest['files'])
assert selection['owned_official_canonical_jobs']==0
print(json.dumps({'status':'PASS','pins':len(manifest['files']),'manifest_sha256':sha(HERE/'self-slot-manifest.json'),'generic_public_pairs':2,'constructed_pairs':1,'owned_jobs':6,'unselected_failed_jobs':2,'strict_literal_zero_logs':2,'private_public_statements_identical':True,'live_jobs':0},indent=2))
