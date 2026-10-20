import hashlib,json,re,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=Path(sys.argv[1]).resolve() if len(sys.argv)>1 else HERE.parents[2]
DEST=Path('lean/restart-evidence/20261020-build-structural-row-origins')
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
manifest=json.loads((HERE/'build-row-manifest.json').read_text())
assert manifest['status']=='final'
assert len({entry['path'] for entry in manifest['files']})==len(manifest['files'])
for entry in manifest['files']:
 relative=Path(entry['path'])
 path=HERE/relative.name if relative.parent==DEST else ROOT/relative
 assert path.stat().st_size==entry['bytes'] and sha(path)==entry['sha256'], entry['path']
selection=json.loads((HERE/'build-row-selection.json').read_text())
source=HERE/selection['source']
assert sha(source)==selection['source_sha256']
for stem,code in selection['attempts'].items():
 receipt=json.loads((HERE/(stem+'.json')).read_text())
 assert receipt['exit_code']==code
 assert sha(HERE/receipt['source'])==receipt['sha256']
 assert receipt['command'][:2]==['/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean','-Dlinter.all=true']
 assert receipt['wrapper'][:5]==['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m']
 limits=json.loads((HERE/(stem+'.limits.json')).read_text())
 assert limits=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 usage=json.loads((HERE/(stem+'.usage.json')).read_text())
 assert usage['remaining_percent']>1 and usage['age_seconds']<120
strict=json.loads((HERE/(selection['strict']+'.json')).read_text())
assert strict['exit_code']==0 and (HERE/strict['log']).read_bytes()==b''
assert (HERE/strict['source']).read_bytes()==source.read_bytes()
for group in selection['groups']:
 receipt=json.loads((HERE/(group['name']+'.json')).read_text())
 assert receipt['exit_code']==0
 printed_source=(HERE/receipt['source']).read_text()
 assert printed_source.startswith(source.read_text())
 for option in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:
  assert 'set_option '+option in printed_source
 for pattern in [r'^#check @',r'^#print (?!axioms )',r'^#print axioms ']:
  assert len(re.findall(pattern,printed_source,re.M))==group['pairs']
 log=(HERE/receipt['log']).read_text()
 assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.',log)
 reports=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',log)
 assert len(reports)+len(re.findall(r'does not depend on any axioms',log))==group['pairs']
 for report in reports:
  cleaned=re.sub(r'\.\{[^}]*\}','',report)
  assert set(re.split(r',\s*',cleaned.strip()))<={'propext','Classical.choice','Quot.sound'}
text=source.read_text()
assert re.search(r'private theorem checked_witness(.*?) := by',text,re.S).group(1)==re.search(r'theorem actual_builds(.*?) := checked_witness',text,re.S).group(1)
assert text.count('exact build_row_origin ')==5
assert sha(ROOT/selection['module'])==selection['module_sha256']
assert (ROOT/selection['module']).read_bytes()==(HERE/'build-row-production.source.lean.txt').read_bytes()
peaks=(HERE/'build-row-final-peaks.txt').read_text().splitlines()
assert len(peaks)==len(selection['attempts'])
assert [int(line.split()[-1]) for line in peaks]==list(selection['attempts'].values())
assert all(line.split()[2]=='4G' for line in peaks)
assert not any(entry['path'].endswith('/build-row-peaks.txt') for entry in manifest['files'])
print(json.dumps({'status':'PASS','pins':len(manifest['files']),'manifest_sha256':sha(HERE/'build-row-manifest.json'),'constructed_pairs':1,'actual_cases':5,'owned_production_public_pairs':0,'owned_jobs':3,'strict_literal_zero':True,'private_public_statements_identical':True,'live_jobs':0},indent=2))
