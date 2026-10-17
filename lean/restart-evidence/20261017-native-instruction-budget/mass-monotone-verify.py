from pathlib import Path
import hashlib,json,re
root=Path('/home/tritlo/Code/mcfta')
e=root/'lean/restart-evidence/20261017-native-instruction-budget'
source=root/'lean/MicroCFTA/SourceCurrentAllocatedRecursiveMassMonotone.lean'
assert hashlib.sha256(source.read_bytes()).hexdigest()=='707fa9615c64ef7cf024d9af0a680e12647fa2b5a7cec5da1ec1581beb1fe57c'
assert len(re.findall(r'^theorem ([^\s(]+)',source.read_text(),re.M))==8
assert (e/'mass-monotone-direct-1.log').stat().st_size==0
assert 'Build completed successfully (1206 jobs).' in (e/'mass-monotone-canonical-1.log').read_text()
for filename,expected in [('mass-monotone-public-1.log',8),('mass-monotone-kernels-2.log',2)]:
 text=(e/filename).read_text()
 assert not re.search(r'error:|error\(|warning:|sorryAx|truncat',text,re.I),filename
 reports=re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]",text,re.S)
 noaxioms=re.findall(r"'([^']+)' does not depend on any axioms",text)
 assert len(reports)+len(noaxioms)==expected,(filename,len(reports),len(noaxioms))
 for name,axioms in reports:
  for axiom in axioms.split(','):
   assert axiom.strip().split('.{')[0] in {'propext','Classical.choice','Quot.sound'},(name,axiom)
 print(filename,expected,'pairs PASS')
if (e/'mass-monotone-manifest.json').exists():
 data=json.loads((e/'mass-monotone-manifest.json').read_text())
 assert data['file_count']==len(data['files'])
 for item in data['files']:
  p=root/item['path']; raw=p.read_bytes()
  assert len(raw)==item['bytes'] and hashlib.sha256(raw).hexdigest()==item['sha256'],p
 print('manifest',len(data['files']),'exact entries PASS')
print('strict, canonical, public, and integration checks PASS')
