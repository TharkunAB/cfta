from pathlib import Path
import hashlib,json,re
ROOT=Path('/home/tritlo/Code/mcfta')
HERE=Path(__file__).resolve().parent
m=json.loads((HERE/'request-winner-manifest.json').read_text())
for item in m['entries']:
 p=ROOT/item['path']; raw=p.read_bytes()
 assert len(raw)==item['bytes'] and hashlib.sha256(raw).hexdigest()==item['sha256'],str(p)
assert (ROOT/m['production']['path']).read_bytes()==(HERE/'request-winner-direct-3.source.lean').read_bytes()
assert (HERE/'request-winner-direct-3.log').read_bytes()==b''
for stem in ['request-winner-direct-3','request-winner-canonical-1','request-winner-public-1']:
 assert json.loads((HERE/(stem+'.json')).read_text())['exit_code']==0,stem
 assert (HERE/(stem+'.caps')).read_text().splitlines()==['4294967296','4294967296','0'],stem
s=(HERE/'request-winner-public-1.source.lean').read_text(); log=(HERE/'request-winner-public-1.log').read_text()
name='MicroCFTA.SourceCurrentNativeRequestWinner.winner'
for option in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:
 assert 'set_option '+option in s
for command in ['#check @','#print ','#print axioms ']:assert command+name in s
assert not re.search(r': (?:error|warning)(?:\(|:)|\bsorryAx\b',log)
a=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log)
assert len(a)==1 and a[0][0]==name
assert {x.strip().split('.{')[0] for x in a[0][1].split(',') if x.strip()}<={'propext','Classical.choice','Quot.sound'}
print('PASS',len(m['entries']),'entries; 1 public pair; strict empty; standard axioms; caps4G/4G/0')
