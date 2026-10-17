from pathlib import Path
import hashlib,json,re
root=Path('/home/tritlo/Code/mcfta')
e=root/'lean/restart-evidence/20261017-native-width-producer'
source=root/'lean/MicroCFTA/SourceCurrentAllocatedNativeWidthStep.lean'
assert hashlib.sha256(source.read_bytes()).hexdigest()=='28762ce5b345d7203096969fdc868d940adcf7522cb2fba05a49eca48a23aedf'
assert (e/'width-step-direct-3.log').stat().st_size==0
assert 'Build completed successfully (1216 jobs).' in (e/'canonical-width-step-1.log').read_text()
for filename,expected in [('width-step-public-1.log',8),('width-step-kernels-4.log',2)]:
 text=(e/filename).read_text()
 assert not re.search(r'error:|error\(|warning:|sorryAx|truncat',text,re.I),filename
 reports=re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]",text,re.S)
 noaxioms=re.findall(r"'([^']+)' does not depend on any axioms",text)
 assert len(reports)+len(noaxioms)==expected,(filename,len(reports),len(noaxioms))
 for name,axioms in reports:
  for axiom in axioms.split(','):
   base=axiom.strip().split('.{')[0]
   assert base in {'propext','Classical.choice','Quot.sound'},(name,base)
 print(filename,expected,'pairs PASS')
if (e/'width-step-manifest.json').exists():
 data=json.loads((e/'width-step-manifest.json').read_text())
 assert data['file_count']==len(data['files'])
 for item in data['files']:
  p=root/item['path']; raw=p.read_bytes()
  assert len(raw)==item['bytes'] and hashlib.sha256(raw).hexdigest()==item['sha256'],p
 print('manifest',len(data['files']),'exact entries PASS')
print('production, canonical, strict, public, and integration checks PASS')
