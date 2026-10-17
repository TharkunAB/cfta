from pathlib import Path
import hashlib,json,re
root=Path('/home/tritlo/Code/mcfta')
e=root/'lean/restart-evidence/20261017-native-instruction-budget'
source=root/'lean/MicroCFTA/SourceCurrentAllocatedNativeInitialInstructionBudget.lean'
assert hashlib.sha256(source.read_bytes()).hexdigest()=='fd79f4a82546505c9d0263fe8bbed668e99d4aa70acdcb7902dbec51783a2eb8'
assert re.findall(r'^theorem ([^\s(]+)',source.read_text(),re.M)==['complete','initial']
for name in ['initial-instruction-budget-direct-1.log','instruction-step-direct-1.log','instruction-trace-direct-2.log']:
 assert (e/name).stat().st_size==0,name
assert 'Build completed successfully (1276 jobs).' in (e/'initial-instruction-budget-canonical-1.log').read_text()
for filename,expected in [('initial-budget-review-public-1.log',2),('initial-budget-review-kernels-3.log',2)]:
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
kernel=(e/'initial-budget-review-kernels.lean').read_text()
assert 'SourceCurrentAllocatedNativeInitialInstructionBudget.initial 24' in kernel
assert 'SourceCurrentAllocatedNativeInitialInstructionBudget.initial 128' in kernel
assert 'OutputFinite' not in kernel
assert len(re.findall(r'^theorem ([^\s(]+)',kernel,re.M))==2
assert not re.search(r'\bsorry\b|^axiom ',kernel,re.M)
if (e/'initial-budget-review-manifest.json').exists():
 data=json.loads((e/'initial-budget-review-manifest.json').read_text())
 assert data['file_count']==len(data['files'])
 for item in data['files']:
  raw=(root/item['path']).read_bytes()
  assert len(raw)==item['bytes'] and hashlib.sha256(raw).hexdigest()==item['sha256'],item['path']
 print('manifest',len(data['files']),'exact entries PASS')
print('initial-only construction, exact warm replay, mixed Mu/union, strict, and canonical validation PASS')
