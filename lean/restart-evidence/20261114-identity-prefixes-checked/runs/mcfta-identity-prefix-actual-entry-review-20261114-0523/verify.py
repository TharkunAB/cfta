from pathlib import Path
import hashlib,json,re
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
receipt=json.loads((root/'INITIALIZER-RECEIPT-CHECK.json').read_text())
draft=root/'SourceSynthesisCurrentInitialIdentityPrefix-UNCOMPILED.lean';text=draft.read_text()
assert receipt['draft_status']=='UNCOMPILED' and receipt['draft_sha256']==sha(draft.read_bytes())
assert receipt['same_initializer_receipt_all_fields'] and receipt['expected_instantiated_receipt_sha256']==receipt['actual_draft_receipt_sha256']
assert text.count('SourceSynthesisCurrentProgramSlotsInitialization.accepted')==receipt['call_count_in_draft']==1
assert len(re.findall(r'^theorem ',text,re.M))==1
assert not re.search(r'^(?:noncomputable )?(?:def|axiom|opaque) ',text,re.M)
assert not re.search(r'\b(?:sorry|admit)\b',text)
public_inputs=text.split('theorem accepted_initial_identity_prefix',1)[1].split(':\n    let bits :=',1)[0]
for forbidden in ['holeKey','fits','admits','(caller :','(memos :','(metadata :','(graph :','(model :']:
 assert forbidden not in public_inputs
sources=json.loads((root/'SOURCE-PINS.json').read_text());assert len(sources)==31
for source in sources:
 ranges=source['frozen_key_cut_ranges']
 if not ranges:continue
 name=Path(source['path']).name;cut=(root/'cuts'/(name+'.txt')).read_text();actual={}
 for line in cut.splitlines(keepends=True):
  m=re.match(r'^(\d+): (.*)',line,re.S)
  if m:actual[int(m[1])]=m[2]
 assert set(actual)=={i for a,z in ranges for i in range(a,z+1)}
 if name=='SourceSynthesisCurrentProgramSlotsInitialization.lean':
  source_text=''.join(actual[i] for i in sorted(actual));ending='(EnumerationState.initial handle) (fun uv => uv = 0)'
  a=source_text.index('∃ fields cache value heap');z=source_text.index(ending,a)+len(ending);original=source_text[a:z]
  substituted=re.sub(r'\bwidth\b','(bits + 2)',original);substituted=re.sub(r'(?<![\w.])initial\b','Cache.emptyState',substituted)
  a=text.index('∃ fields cache value heap');z=text.index(ending,a)+len(ending);conclusion=text[a:z]
  normalize=lambda x:re.sub(r'\s+','',x)
  assert normalize(substituted)==normalize(conclusion)
  assert sha(normalize(conclusion).encode())==receipt['actual_draft_receipt_sha256']
identity=next(s for s in sources if s['path'].endswith('/SourcePruningEnumerationIdentityPrefix.lean'))
assert identity['sha256']=='b37f79c2d81bce529e3bf9b366e6eddec9ad675b70d63eb109757539335ff41c'
assert frozen['status']=='WRITE HALT; UNCOMPILED SOURCE-ONLY'
print('PASS retained pins, exact initializer receipt preservation, source cuts and source-only candidate checks; UNCOMPILED')
