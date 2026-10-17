from pathlib import Path
import hashlib,json,re
ROOT=Path('/home/tritlo/Code/mcfta');HERE=Path(__file__).resolve().parent
m=json.loads((HERE/'native-mu-history-manifest.json').read_text())
for item in m['entries']:
 p=ROOT/item['path'];raw=p.read_bytes()
 assert len(raw)==item['bytes'] and hashlib.sha256(raw).hexdigest()==item['sha256'],str(p)
assert (ROOT/m['production']['path']).read_bytes()==(HERE/'native-mu-history-direct-2.source.lean').read_bytes()
assert (HERE/'native-mu-history-direct-2.log').read_bytes()==b''
for stem in ['native-mu-history-direct-2','native-mu-history-canonical-1','native-mu-history-public-1','native-mu-history-kernels-2']:
 assert json.loads((HERE/(stem+'.json')).read_text())['exit_code']==0,stem
 assert (HERE/(stem+'.caps')).read_text().splitlines()==['4294967296','4294967296','0'],stem
assert 'Build completed successfully (535 jobs).' in (HERE/'native-mu-history-canonical-1.log').read_text()
for stem,names in [('native-mu-history-public-1',m['public_names']),('native-mu-history-kernels-2',m['kernel_names'])]:
 s=(HERE/(stem+'.source.lean')).read_text();log=(HERE/(stem+'.log')).read_text()
 for option in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:
  assert 'set_option '+option in s,(stem,option)
 assert not re.search(r': (?:error|warning)(?:\(|:)|\bsorryAx\b',log),stem
 a=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log)
 assert len(a)==len(names) and {n for n,_ in a}==set(names),stem
 for name,ax in a:
  for cmd in ['#check @','#print ','#print axioms ']:assert cmd+name in s,(stem,name)
  assert {x.strip().split('.{')[0] for x in ax.split(',') if x.strip()}<={'propext','Classical.choice','Quot.sound'},name
print('PASS',len(m['entries']),'immutable entries; 3 public +1 constructed pair; strict empty; standard axioms; caps4G/4G/0')
