from pathlib import Path
import hashlib,json,re
ROOT=Path('/home/tritlo/Code/mcfta');HERE=Path(__file__).resolve().parent
m=json.loads((HERE/'publication-callback-manifest.json').read_text())
for item in m['entries']:
 p=ROOT/item['path'];raw=p.read_bytes()
 assert len(raw)==item['bytes'] and hashlib.sha256(raw).hexdigest()==item['sha256'],str(p)
assert (ROOT/m['production']['path']).read_bytes()==(HERE/'publication-callback-direct-2.source.lean').read_bytes()
assert (HERE/'publication-callback-direct-2.log').read_bytes()==b''
for stem in ['publication-callback-direct-2','publication-callback-canonical-1','publication-callback-public-1']:
 assert json.loads((HERE/(stem+'.json')).read_text())['exit_code']==0,stem
 assert (HERE/(stem+'.caps')).read_text().splitlines()==['4294967296','4294967296','0'],stem
s=(HERE/'publication-callback-public-1.source.lean').read_text();log=(HERE/'publication-callback-public-1.log').read_text()
for option in ['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']:
 assert 'set_option '+option in s
assert not re.search(r': (?:error|warning)(?:\(|:)|\bsorryAx\b',log)
a=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log)
assert len(a)==3 and {n for n,_ in a}==set(m['public_names'])
for name,ax in a:
 for cmd in ['#check @','#print ','#print axioms ']:assert cmd+name in s
 assert {x.strip().split('.{')[0] for x in ax.split(',') if x.strip()}<={'propext','Classical.choice','Quot.sound'}
print('PASS',len(m['entries']),'entries; 3 public pairs; strict empty; standard axioms; caps4G/4G/0')
