from pathlib import Path
import hashlib,json,re
root=Path('/home/tritlo/Code/mcfta')
e=root/'lean/restart-evidence/20261017-computable-query-rank'
p=root/'lean/MicroCFTA/SourceCurrentAllocatedNativeComputedBudget.lean'
source=p.read_text()
assert hashlib.sha256(p.read_bytes()).hexdigest()=='82d4affc8d0e587504f9f8cdfaf37dc34e946d4de7e7d5f8a7a690b60e8983b8'
assert re.findall(r'^(?:def|theorem) ([^\s(]+)',source,re.M)==['instructionBound','instructionBound_mono','nodeBudget_le','initial']
assert 'initialBound' not in source
assert 'prefix_bound receipt.trace good' in source
assert (e/'native-computed-direct-2.log').stat().st_size==0
build=(e/'native-computed-canonical-1.log').read_text()
assert 'Build completed successfully (1282 jobs).' in build
assert re.findall(r'^warning: (.*)',build,re.M)==['MicroCFTA/InternedFreshOrdinaryClosedCompletion.lean:24:5: Variable name `inputs` is not explicitly referenced.']
for filename,expected in [('native-computed-public-1.log',4),('native-computed-kernels-5.log',2)]:
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
kernel=(e/'native-computed-kernels.lean').read_text()
assert len(re.findall(r'^theorem ([^\s(]+)',kernel,re.M))==2
assert not re.search(r'\bsorry\b|^axiom ',kernel,re.M)
assert 'SourceCurrentAllocatedNativeComputedBudget.initial 24' in kernel
assert 'SourceCurrentAllocatedNativeComputedBudget.initial 4' in kernel
assert 'InternedValueMassHeap.Stored 3 simpleNode.2' in kernel
assert 'InternedValueMassHeap.initialBound simpleNode.2 = 5' in kernel
assert 'OutputFinite' not in kernel
if (e/'native-computed-manifest.json').exists():
 data=json.loads((e/'native-computed-manifest.json').read_text())
 assert data['file_count']==len(data['files'])
 for item in data['files']:
  raw=(root/item['path']).read_bytes()
  assert len(raw)==item['bytes'] and hashlib.sha256(raw).hexdigest()==item['sha256'],item['path']
 print('manifest',len(data['files']),'exact entries PASS')
print('computed initial completion, same trace, causal mass, strict, and canonical PASS')
