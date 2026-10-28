from pathlib import Path
import hashlib,json
area=Path('/tmp/mcfta-prepared-composition-20261028')
def sha(b):return hashlib.sha256(b).hexdigest()
expected={x['name']:x for x in json.loads((area/'public-blocks-index.json').read_text())}
seen={};reviews=[('sibling-origins/public-read-scopes-v1.json','blocks'),('prefix-origins/public-review.json','whole_read_complete_blocks'),('selector-admission/evidence/public-review.json','whole_blocks_read')]
for rel,key in reviews:
 for rec in json.loads((area/rel).read_text())[key]:
  assert rec['name'] in expected
  reference=expected[rec['name']]
  for prop in ['path','bytes','sha256']:assert rec[prop]==reference[prop],(rel,rec['name'],prop)
  raw=(area/rec['path']).read_bytes();assert len(raw)==rec['bytes'] and sha(raw)==rec['sha256']
  seen.setdefault(rec['name'],[]).append(rel)
assert set(seen)==set(expected)
for name,rec in json.loads((area/'document-inverse.json').read_text()).items():
 old=(area/'prior-documents'/name).read_bytes();insert=(area/'document-insertions'/('findings.md' if name=='FINDINGS.md' else 'common.md')).read_bytes();first,rest=old.split(b'\n',1);new=first+b'\n'+insert+rest
 assert sha(old)==rec['before_sha256'] and sha(new)==rec['after_sha256']
 assert (Path('/home/tritlo/Code/mcfta')/name).read_bytes()==new
 assert new.replace(insert,b'',1)==old
note=Path('/home/tritlo/Code/mcfta/lean/notes-current-prepared-composition.md').read_bytes();assert note==(area/'root-review/notes-current-prepared-composition.md').read_bytes()
report=dict(status='pass',whole_assigned_public_blocks=len(seen),whole_assigned_public_bytes=sum(x['bytes'] for x in expected.values()),coverage=seen,root_whole_public_appendix_read=False,document_inverses=9,note_bytes=len(note),note_sha256=sha(note))
(area/'root-review/review-verification.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='coverage'}))
