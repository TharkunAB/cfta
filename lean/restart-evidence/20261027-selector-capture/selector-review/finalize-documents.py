from pathlib import Path
import json,hashlib
repo=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-selector-capture-20261027');out=area/'selector-review';sha=lambda b:hashlib.sha256(b).hexdigest()
def put(rel,b):
 p=out/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b.encode() if isinstance(b,str) else b)
for name in ['document-paths.json','document-validation.json']:
 put('final-evidence/'+name,(area/name).read_bytes())
head='82fdb41fc9e55f57e2950ab78297140cbdc97c69';put('final-evidence/source-head.txt',head+'\n')
if (area/'source-head.txt').exists():assert (area/'source-head.txt').read_text().strip()==head
rows=json.loads((area/'document-validation.json').read_text());assert len(rows)==10;docs=[]
for x in rows:
 src=repo/x['path'];b=src.read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256'],x['path'];row={'document_source_path':str(src),'bytes':len(b),'sha256':sha(b)}
 if 'offset' in x:
  off=x['offset'];n=x['inserted_bytes'];cut=b[off:off+n];old=b[:off]+b[off+n:];assert old==(area/'prior-documents'/x['path']).read_bytes()
  rel='documents/insertions/'+x['path'];put(rel,cut);row.update({'insertion_copy':rel,'offset':off,'inserted_bytes':n,'insertion_sha256':sha(cut),'prior_bytes':len(old),'prior_sha256':sha(old),'entire_prior_body_inverse':True})
 else:
  assert x['path']=='lean/notes-current-selector-capture.md' and len(b)==10650 and sha(b)=='010db0432469065ab4468fd76dffac9fda3d2c8ff93a0ee97d177b76c5b23d54'
  rel='documents/'+x['path'];put(rel,b);row['whole_copy']=rel
 docs.append(row)
put('documents/independent-validation.json',json.dumps({'status':'PASS','full_new_note_read':True,'all_nine_actual_insertions_read':True,'documents':docs},indent=2)+'\n')
index=json.loads((out/'source-index.json').read_text());src=repo/'lean/notes-current-selector-capture.md';b=src.read_bytes();rel='documents/lean/notes-current-selector-capture.md';cut=f'cuts/{src.name}.1-{len(b.splitlines())}.txt';put(cut,b);index['sources'].append({'source':str(src),'whole':{'path':rel,'bytes':len(b),'sha256':sha(b)},'review_scope':'Whole final checkpoint note reviewed against checked source/public contracts and exact attempts.','cuts':[{'path':cut,'bytes':len(b),'sha256':sha(b),'first_line':1,'last_line':len(b.splitlines())}]});put('source-index.json',json.dumps(index,indent=2)+'\n')
for row in index['sources']:
 b=Path(row['source']).read_bytes();assert b==(out/row['whole']['path']).read_bytes();assert len(b)==row['whole']['bytes'] and sha(b)==row['whole']['sha256']
 for c in row['cuts']:
  bb=b''.join(b.splitlines(keepends=True)[c['first_line']-1:c['last_line']]);assert bb==(out/c['path']).read_bytes();assert len(bb)==c['bytes'] and sha(bb)==c['sha256']
final=json.loads((out/'final-checks-validation.json').read_text());final.update({'source_head':head,'documents':'PASS: whole new note, nine literal insertions, nine whole prior-body inverses','source_records':len(index['sources']),'literal_cuts':sum(len(x['cuts']) for x in index['sources']),'all_inspected_sources_match_current':True,'review_verdict':'CLEAR','bundle_status':'Ready to seal once final report is present'})
put('verification-final.json',json.dumps(final,indent=2)+'\n')
print(json.dumps({'status':'PASS','source_records':len(index['sources']),'literal_cuts':final['literal_cuts'],'new_note_bytes':10650,'prior_document_body_inverses':9}))
