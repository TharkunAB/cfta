from pathlib import Path
import hashlib,json,re
root=Path('/home/tritlo/Code/mcfta')
e=root/'lean/restart-evidence/20261017-generated-query-resources'
p=root/'lean/MicroCFTA/SourceCurrentConstrainedCapCheckedJointComputedQuery.lean'
source=p.read_text()
assert hashlib.sha256(p.read_bytes()).hexdigest()=='16da2f6f7400895cba5fc84d1b8521b969730f9ea8109d32b7d2a9a3546e0a0b'
assert re.findall(r'^theorem ([^\s(]+)',source,re.M)==['of_receipt','generated_complete']
assert 'initialBound' not in source
assert 'prefix_bound receipt.trace good' in source
assert 'InventoryQuery.generated_complete bits depth' in source
assert (e/'generated-computed-direct-1.log').stat().st_size==0
build=(e/'generated-computed-canonical-1.log').read_text()
assert 'Build completed successfully (1359 jobs).' in build
assert re.findall(r'^warning: (.*)',build,re.M)==['MicroCFTA/InternedFreshOrdinaryClosedCompletion.lean:24:5: Variable name `inputs` is not explicitly referenced.']
for filename,expected in [('generated-computed-public-1.log',2),('generated-computed-kernels-2.log',1)]:
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
kernel=(e/'generated-computed-kernels.lean').read_text()
assert len(re.findall(r'^theorem ([^\s(]+)',kernel,re.M))==1
assert not re.search(r'\bsorry\b|^axiom ',kernel,re.M)
assert 'CheckedJointComputedQuery.generated_complete 24 2' in kernel
assert 'inventory.source = empty' in kernel
assert 'next.roots = [left, right]' in kernel
assert 'receipt.meaning' in kernel
if (e/'generated-computed-manifest.json').exists():
 data=json.loads((e/'generated-computed-manifest.json').read_text())
 assert data['file_count']==len(data['files'])
 for item in data['files']:
  raw=(root/item['path']).read_bytes()
  assert len(raw)==item['bytes'] and hashlib.sha256(raw).hexdigest()==item['sha256'],item['path']
 print('manifest',len(data['files']),'exact entries PASS')
print('own generated return, exact joint receipt, current entry source, causal mass, and computed resources PASS')
