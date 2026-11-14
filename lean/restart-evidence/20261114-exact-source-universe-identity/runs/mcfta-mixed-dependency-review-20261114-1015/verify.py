from pathlib import Path
import hashlib,json,re
root=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
pins=json.loads((root/'PINS').read_text());manifest=(root/'MANIFEST').read_bytes();assert sha(manifest)==pins['manifest_sha256'];expected=set()
for line in manifest.decode().splitlines():
 digest,size,name=line.split(' ',2);p=root/name;assert p.is_file() and not p.is_symlink();b=p.read_bytes();assert sha(b)==digest and len(b)==int(size);expected.add(name)
assert {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}==expected|{'MANIFEST','PINS'}
assert len(expected)==pins['payloads']
old=(root/'StoredDependencySeparation-UNCOMPILED.lean').read_text();new=(root/'StoredDependencySeparation-v2-UNCOMPILED.lean').read_text();addition=(root/'LEVEL-ADDITION.lean.txt').read_text()
assert sha(old.encode())=='3ac26a58972ed3111d14773377baa0a38b1bc0fe2e1f00556fa91b4b87e68766'
assert sha(new.encode())=='d9f9061a3650b3b3fdf2f14f1541d14c4158161669828a2fc84aafbe1a3698ab'
assert len(old.splitlines())==57 and len(new.splitlines())==108
assert new.replace('import MicroCFTA.EnumerationOrder\n','',1).replace(addition,'')==old
for file,source in [('HEADERS.json',old),('HEADERS-v2.json',new)]:
 for name,header in json.loads((root/file).read_text()).items():
  start=source.index('theorem '+name);end=source.index(':= by',start)+len(':= by');assert source[start:end]==header
assert not re.search(r'\b(?:sorry|admit|axiom)\b',new)
assert 'UNCOMPILED' in (root/'REPORT.md').read_text()
assert 'No compiler or evaluator checked this model' in (root/'FORMAL-COUNTERMODEL-AND-OBLIGATIONS.md').read_text()
assert pins['status']=='WRITE HALT; all new candidates/model UNCOMPILED'
print('PASS original57L identity, additive108L source and exact headers; all new candidates/model UNCOMPILED')
