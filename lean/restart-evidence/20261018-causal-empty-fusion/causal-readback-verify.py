import hashlib,json,re,runpy
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((HERE/'causal-readback-manifest.json').read_text())
for f in m['files']:
 p=ROOT/f['path'];assert p.stat().st_size==f['bytes'] and sha(p)==f['sha256'],p
s=json.loads((HERE/'causal-readback-selection.json').read_text());assert s['finalized'] and s['status']=='final'
c=runpy.run_path(str(HERE/'causal-readback-probe-check.py'))
for g in s['groups']:c['check_group'](g)
for stem in m['executions']:
 x=json.loads((HERE/(stem+'.json')).read_text())
 assert x['wrapper'][:5]==['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m'];c['check_limits'](stem)
 assert 'leanprover--lean4---v4.34.1'in x['command'][0]
 if 'source'in x:assert sha(HERE/x['source'])==x['sha256']
for stem in m['selected_executions']:assert json.loads((HERE/(stem+'.json')).read_text())['exit_code']==0
for a in s['retained_unselected']:assert json.loads((HERE/(a['stem']+'.json')).read_text())['exit_code']==a['exit_code']
for stem in [s['strict'],s['constructed_strict']]:
 x=json.loads((HERE/(stem+'.json')).read_text());assert not (HERE/x['log']).read_bytes()
x=json.loads((HERE/(s['strict']+'.json')).read_text());p=ROOT/s['production']
assert p.read_bytes()==(HERE/x['source']).read_bytes() and sha(p)==s['sha256']
assert len(re.findall(r'^theorem ',p.read_text(),re.M))==1 and not re.search(r'\bsorry\b|\baxiom\b',p.read_text())
x=json.loads((HERE/(s['canonical']+'.json')).read_text());log=(HERE/x['log']).read_text()
assert 'Build completed successfully (655 jobs).'in log and not re.search(r'warning:|error:',log)
k=HERE/'causal-readback-kernels.lean';x=json.loads((HERE/(s['constructed_strict']+'.json')).read_text());assert k.read_bytes()==(HERE/x['source']).read_bytes()
x=json.loads((HERE/(s['constructed_group']+'.json')).read_text());assert (HERE/x['source']).read_text().startswith(k.read_text())
t=k.read_text();a=t.index('private theorem checked_witness :')+len('private theorem checked_witness :');b=t.index('theorem actual_used_empty_replacement :')+len('theorem actual_used_empty_replacement :')
assert t[a:t.index(' := by',a)]==t[b:t.index(' := checked_witness',b)]
print(json.dumps({'status':'PASS','files':len(m['files']),'public_pairs':1,'constructed_pairs':1,'strict_log_bytes':0,'constructed_log_bytes':0,'exact_public_witness_statement':True,'retained_failed_attempts':3}))
