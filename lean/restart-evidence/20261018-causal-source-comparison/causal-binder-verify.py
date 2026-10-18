import hashlib,json,re,runpy
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((HERE/'causal-binder-manifest.json').read_text())
for f in m['files']:
 p=ROOT/f['path'];assert p.stat().st_size==f['bytes'] and sha(p)==f['sha256'],p
s=json.loads((HERE/'causal-binder-selection.json').read_text());assert s['finalized'] and s['status']=='final'
c=runpy.run_path(str(HERE/'causal-binder-probe-check.py'))
for g in s['groups']:c['check_group'](g)
for stem in m['executions']:
 x=json.loads((HERE/(stem+'.json')).read_text())
 assert x['wrapper'][:5]==['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m'];c['check_limits'](stem)
 assert 'leanprover--lean4---v4.34.1' in x['command'][0]
 if 'source'in x:assert sha(HERE/x['source'])==x['sha256']
for stem in m['selected_executions']:assert json.loads((HERE/(stem+'.json')).read_text())['exit_code']==0
for a in s['retained_unselected']:assert json.loads((HERE/(a['stem']+'.json')).read_text())['exit_code']==a['exit_code']
x=json.loads((HERE/(s['strict']+'.json')).read_text());assert not (HERE/x['log']).read_bytes()
p=ROOT/s['production'];assert p.read_bytes()==(HERE/x['source']).read_bytes() and sha(p)==s['sha256']
text=p.read_text();assert len(re.findall(r'^theorem ',text,re.M))==1
assert not re.search(r'\bsorry\b|\baxiom\b',text)
assert 'theorem binder (smart : Bool) (body : Syntax Symbol Guard) (ih : Law body) : Law (.binder smart body)' in text
assert all(line.rstrip()==line for line in text.splitlines())
x=json.loads((HERE/(s['canonical']+'.json')).read_text());log=(HERE/x['log']).read_text();assert 'Build completed successfully (648 jobs).'in log and not re.search(r'warning:|error:',log)
print(json.dumps({'status':'PASS','files':len(m['files']),'public_pairs':1,'constructed_pairs':0,'strict_log_bytes':0,'retained_failed_attempts':1}))
