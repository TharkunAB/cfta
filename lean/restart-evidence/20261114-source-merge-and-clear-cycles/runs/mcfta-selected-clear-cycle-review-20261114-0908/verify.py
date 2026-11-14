from pathlib import Path
import hashlib,json,re
root=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
pins=json.loads((root/'PINS').read_text());manifest=(root/'MANIFEST').read_bytes()
assert sha(manifest)==pins['manifest_sha256']
expected=set()
for line in manifest.decode().splitlines():
 digest,size,name=line.split(' ',2);p=root/name;assert p.is_file() and not p.is_symlink();b=p.read_bytes();assert len(b)==int(size) and sha(b)==digest;expected.add(name)
assert {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}==expected|{'MANIFEST','PINS'}
assert len(expected)==pins['payloads']
candidate=(root/'SelectedClearCycle-UNCOMPILED.lean').read_text()
assert sha(candidate.encode())=='22e13b09ef160c3833b8288512d0a0656c62dd787eb4e84b556644ccccbc50e3'
assert len(candidate.splitlines())==148
assert not re.search(r'\b(?:sorry|admit|axiom)\b',candidate)
assert 'attribute [local instance] recursionMonadList' in candidate
assert candidate.startswith('import MicroCFTA.SourcePruningEnumerationParkedLanguage\n')
assert 'theorem selected_clear_keeps_closed_references' in candidate
assert 'theorem proper_closed_references_no_assignment' in candidate
assert pins['status']=='WRITE HALT; UNCOMPILED; NO PROOF CREDIT'
print('PASS retained metadata/candidate identity; UNCOMPILED; no Lean command ran')
