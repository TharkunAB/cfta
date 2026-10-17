from pathlib import Path
import hashlib,json,re
root=Path('/home/tritlo/Code/mcfta')
e=root/'lean/restart-evidence/20261017-computable-query-rank'
p=root/'lean/MicroCFTA/SourceRecursiveIntersectionNumericSourceProfile.lean'
assert hashlib.sha256(p.read_bytes()).hexdigest()=='2c7a2c5a41dd01f1530ec4fb9ba3f909224cf46146c96a6c8f215241ac396a7f'
assert re.findall(r'^(?:def|theorem) ([^\s(]+)',p.read_text(),re.M)==['limits_bound','initial_bound','branching','source_branching','branching_mono']
assert (e/'numeric-source-profile-direct-4.log').stat().st_size==0
build=(e/'numeric-source-profile-canonical-1.log').read_text()
assert 'Build completed successfully (1178 jobs).' in build
assert re.findall(r'^warning: (.*)',build,re.M)==['MicroCFTA/InternedFreshOrdinaryClosedCompletion.lean:24:5: Variable name `inputs` is not explicitly referenced.']
for filename,expected in [('numeric-source-profile-public-1.log',5),('numeric-source-profile-kernels-4.log',2)]:
 text=(e/filename).read_text()
 assert not re.search(r'error:|error\(|warning:|sorryAx|truncat',text,re.I),filename
 reports=re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]",text,re.S)
 none=re.findall(r"'([^']+)' does not depend on any axioms",text)
 assert len(reports)+len(none)==expected,(filename,len(reports),len(none))
 for name,axioms in reports:
  for axiom in axioms.split(','):
   assert axiom.strip().split('.{')[0] in {'propext','Classical.choice','Quot.sound'},(name,axiom)
 for name in [x[0] for x in reports]+none:
  assert name+' :' in text,name
 print(filename,expected,'full-signature/axiom pairs PASS')
kernel=(e/'numeric-source-profile-kernels.lean').read_text()
assert len(re.findall(r'^theorem ([^\s(]+)',kernel,re.M))==2
assert not re.search(r'\bsorry\b|^axiom ',kernel,re.M)
assert 'InternedValueMassHeap.Stored 3 constantNode.2' in kernel
assert 'InternedValueMassHeap.initialBound constantNode.2 = 5' in kernel
if (e/'numeric-source-profile-manifest.json').exists():
 data=json.loads((e/'numeric-source-profile-manifest.json').read_text())
 assert data['file_count']==len(data['files'])
 for item in data['files']:
  raw=(root/item['path']).read_bytes()
  assert len(raw)==item['bytes'] and hashlib.sha256(raw).hexdigest()==item['sha256'],item['path']
 print('manifest',len(data['files']),'exact entries PASS')
print('source, strict, canonical, recursive growth, and initial-sum distinction PASS')
