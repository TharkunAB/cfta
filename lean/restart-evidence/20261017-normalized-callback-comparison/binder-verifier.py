from pathlib import Path
import hashlib,json,re
ROOT=Path('/home/tritlo/Code/mcfta');HERE=Path(__file__).resolve().parent
m=json.loads((HERE/'binder-manifest.json').read_text())
for item in m['entries']:
 p=ROOT/item['path'];raw=p.read_bytes()
 assert len(raw)==item['bytes'] and hashlib.sha256(raw).hexdigest()==item['sha256'],str(p)
assert (ROOT/m['production']['path']).read_bytes()==(HERE/'binder-direct-3.source.lean').read_bytes()
assert (HERE/'binder-direct-3.log').read_bytes()==b''
for stem in ['binder-direct-3','binder-canonical-1','binder-public-1','binder-kernels-1']:
 assert json.loads((HERE/(stem+'.json')).read_text())['exit_code']==0,stem
 assert (HERE/(stem+'.caps')).read_text().splitlines()==['4294967296','4294967296','0'],stem
for stem,name in [('binder-public-1','MicroCFTA.SourceCurrentNativeBinderExecution.decompose'),('binder-kernels-1','MicroCFTA.NativeBinderExecutionKernels.closed')]:
 s=(HERE/(stem+'.source.lean')).read_text();log=(HERE/(stem+'.log')).read_text()
 for option in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:
  assert 'set_option '+option in s
 assert not re.search(r': (?:error|warning)(?:\(|:)|\bsorryAx\b',log)
 a=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log)
 assert len(a)==1 and a[0][0]==name
 for cmd in ['#check @','#print ','#print axioms ']:assert cmd+name in s
 assert {x.strip().split('.{')[0] for x in a[0][1].split(',') if x.strip()}<={'propext','Classical.choice','Quot.sound'}
print('PASS',len(m['entries']),'entries; 1 public +1 initial producer pair; strict empty; standard axioms; caps4G/4G/0')
