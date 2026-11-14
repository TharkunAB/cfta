from pathlib import Path
import hashlib,json,re,sys
sys.dont_write_bytecode=True
from patch_replay import replay
root=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
manifest=(root/'MANIFEST').read_bytes();pins=json.loads((root/'PINS').read_text());frozen=json.loads((root/'FROZEN').read_text())
assert sha(manifest)==pins['manifest_sha256']==frozen['manifest_sha256']
assert sha((root/'PINS').read_bytes())==frozen['pins_sha256']
expected=set()
for row in manifest.decode().splitlines():
 digest,size,name=row.split(' ',2);p=root/name;assert p.is_file() and not p.is_symlink();b=p.read_bytes();assert sha(b)==digest and len(b)==int(size);expected.add(name)
assert {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}==expected|{'MANIFEST','PINS','FROZEN'}
assert len(expected)==pins['payload_count']
old=(root/'original-SourceSynthesisCurrentInitialIdentityPrefix.lean').read_text();new=(root/'SourceSynthesisCurrentInitialIdentityPrefix-v2-UNCOMPILED.lean').read_text();patch=(root/'repair.UNCOMPILED.patch').read_text();checks=json.loads((root/'CHECKS.json').read_text())
assert sha(old.encode())==checks['root_original_sha256'];assert sha(new.encode())==checks['root_candidate_sha256']
assert replay(old,patch)==new and replay(new,patch,True)==old
end=old.index(':= by',old.index('theorem accepted_initial_identity_prefix'))+len(':= by')
assert old[:end]==new[:end]==(root/'HEADER-original.txt').read_text()==(root/'HEADER-candidate.txt').read_text()
assert sha(old[:end].encode())==checks['header_sha256']
assert len(re.findall(r'\bprefixRun\b',new[end:]))==3
assert not re.search(r'\b(?:sorry|admit)\b',new)
assert sha((root/'prior-uncompiled-draft.lean').read_bytes())=='a032f69f341b0a7a15c410957b3a4832a834270ed44c9e7ec88e2e5e34003f1a'
assert sha((root/'original-private-actual-initial-identity-prefix.txt').read_bytes())=='e4803c1dfb5bf842e14c2a6bc067a4c8e3394b2bc0393bc3a743581e5e314d80'
assert frozen['status']=='WRITE HALT; UNCOMPILED'
print('PASS retained failure/draft, whole-header identity and exact forward/reverse patch replay; UNCOMPILED')
