import hashlib,json,runpy
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def write(n,v):(HERE/n).write_text(json.dumps(v,indent=2)+'\n')
s={'constructed_strict':'binder-uniform-direct-1','canonical':None,'groups':[{'name':'binder-uniform-public-1','pairs':1,'kind':'constructed','full_proof':True}],'new_production':0}
c=runpy.run_path(str(HERE/'verify-probes.py'));c['check_group'](s['groups'][0])
r=json.loads((HERE/'binder-uniform-direct-1.json').read_text());assert r['exit_code']==0 and not (HERE/r['log']).read_bytes();c['check_limits']('binder-uniform-direct-1')
assert (HERE/r['source']).read_bytes()==(HERE/'binder-uniform-kernels.lean').read_bytes()
assert (HERE/'binder-uniform-kernels.lean').read_bytes().startswith((HERE/'binder-contract-direct-5.source.lean').read_bytes())
write('binder-uniform-selection.json',s)
(HERE/'binder-uniform-report.md').write_text('''# Refuted uniform source induction

The checked counterexample refutes tracked Fusion at rank0 for one smart
binder. no_uniform derives that no positive bound can supply Fusion for
every source expression at all strictly smaller ranks. Every selected Mu
has positive physical depth. Therefore the existing uniform writer theorem
has an unattainable premise under the old unrestricted contract.
The particular-body publication theorem does not use that uniform premise.

This file copies the frozen counterexample and adds only its direct logical
consequence. Direct1 has a zero-byte log. Full public1 passes all eight
printer/linter settings and standard-axiom checks. This is one additional
constructed consequence pair, not a second countermodel or a Haskell defect.
''')
(HERE/'binder-uniform-verify.py').write_text('''import hashlib,json,runpy
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
read=lambda n:json.loads((HERE/n).read_text())
for e in read('binder-uniform-manifest.json')['entries']:
 assert hashlib.sha256((ROOT/e['path']).read_bytes()).hexdigest()==e['sha256'],e['path']
c=runpy.run_path(str(HERE/'verify-probes.py'));s=read('binder-uniform-selection.json')
for g in s['groups']:c['check_group'](g)
r=read(s['constructed_strict']+'.json');assert r['exit_code']==0 and not (HERE/r['log']).read_bytes();c['check_limits'](s['constructed_strict'])
assert (HERE/r['source']).read_bytes()==(HERE/'binder-uniform-kernels.lean').read_bytes()
assert (HERE/r['source']).read_bytes().startswith((HERE/'binder-contract-direct-5.source.lean').read_bytes())
print(json.dumps({'status':'PASS','constructed_pairs':1,'new_production':0,'all_positive_uniform_bounds_refuted':True,'pins':len(read('binder-uniform-manifest.json')['entries'])}))
''')
paths=[p for p in HERE.glob('binder-uniform-*') if p.is_file() and p.name!='binder-uniform-manifest.json']
paths += [HERE/n for n in ['binder-contract-direct-5.source.lean','binder-contract-manifest.json','root-run-check.py','root-capped-worker.py','verify-probes.py']]
write('binder-uniform-manifest.json',{'entries':[{'path':str(p.relative_to(ROOT)),'sha256':sha(p)} for p in sorted(set(paths))]})
print('Uniform consequence frozen:',len(set(paths)))
