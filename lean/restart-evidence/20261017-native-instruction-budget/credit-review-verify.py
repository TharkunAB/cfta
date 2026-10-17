from pathlib import Path
import hashlib,json,re
root=Path('/home/tritlo/Code/mcfta')
e=root/'lean/restart-evidence/20261017-native-instruction-budget'
source=root/'lean/MicroCFTA/SourceRecursiveIntersectionInstructionCredit.lean'
assert hashlib.sha256(source.read_bytes()).hexdigest()=='1789998048af5fa42dfd01523226f22d81b79973a63d50fd15cca80e6be62cef'
assert len(re.findall(r'^(?:def|theorem) ([^\s(]+)',source.read_text(),re.M))==13
assert (e/'instruction-credit-direct-3.log').stat().st_size==0
assert 'Build completed successfully (1176 jobs).' in (e/'instruction-credit-canonical-1.log').read_text()
for filename,expected in [('credit-review-public-1.log',13),('credit-review-kernels-1.log',2)]:
 text=(e/filename).read_text()
 assert not re.search(r'error:|error\(|warning:|sorryAx|truncat',text,re.I),filename
 reports=re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]",text,re.S)
 noaxioms=re.findall(r"'([^']+)' does not depend on any axioms",text)
 assert len(reports)+len(noaxioms)==expected,(filename,len(reports),len(noaxioms))
 for name,axioms in reports:
  for axiom in axioms.split(','):
   assert axiom.strip().split('.{')[0] in {'propext','Classical.choice','Quot.sound'},(name,axiom)
 print(filename,expected,'pairs PASS')
if (e/'credit-review-manifest.json').exists():
 data=json.loads((e/'credit-review-manifest.json').read_text())
 assert data['file_count']==len(data['files'])
 for item in data['files']:
  raw=(root/item['path']).read_bytes()
  assert len(raw)==item['bytes'] and hashlib.sha256(raw).hexdigest()==item['sha256'],item['path']
 print('manifest',len(data['files']),'exact entries PASS')
print('source, canonical, strict, public, and integration checks PASS')
