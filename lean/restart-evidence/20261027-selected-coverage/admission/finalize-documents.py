from pathlib import Path
import hashlib,json
repo=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-selected-coverage-20261027');out=area/'admission';sha=lambda b:hashlib.sha256(b).hexdigest()
def put(rel,b):
 p=out/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b.encode() if isinstance(b,str) else b)
for name in ['document-paths.json','document-validation.json','root-document-validation.json']:
 put('final-evidence/'+name,(area/name).read_bytes())
rows=json.loads((area/'document-validation.json').read_text());docs=[]
assert len(rows)==10
for x in rows:
 src=repo/x['path'];b=src.read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256'],x['path']
 row={'document_source_path':str(src),'bytes':len(b),'sha256':sha(b)}
 if 'offset' in x:
  off=x['offset'];n=x['inserted_bytes'];cut=b[off:off+n];old=b[:off]+b[off+n:]
  assert old==(area/'prior-documents'/x['path']).read_bytes()
  assert len(old)==x['prior_bytes'] and sha(old)==x['prior_sha256']
  rel='documents/insertions/'+x['path'];put(rel,cut)
  row.update({'offset':off,'inserted_bytes':n,'insertion_copy':rel,'insertion_sha256':sha(cut),'prior_bytes':len(old),'prior_sha256':sha(old),'entire_prior_body_recovered':True})
 else:
  assert x['path']=='lean/notes-current-selected-coverage.md'
  assert len(b)==10380 and sha(b)=='8ada69c850ab52921f5ff453ab20fa220e0b05da81adb2b544fe9eebac65d559'
  rel='documents/'+x['path'];put(rel,b);row.update({'whole_copy':rel,'whole_note_read':True})
 docs.append(row)
put('documents/independent-validation.json',json.dumps({'status':'PASS','documents':docs,'all_nine_insertions_read':True,'full_new_note_read':True},indent=2)+'\n')
index=json.loads((out/'source-index.json').read_text())
for s in index['sources']:
 b=Path(s['source_path']).read_bytes();assert len(b)==s['bytes'] and sha(b)==s['sha256'];assert b==(out/s['copy']).read_bytes()
 for c in s['cuts']:
  cut=b''.join(b.splitlines(keepends=True)[c['start_line']-1:c['end_line']]);assert cut==(out/c['path']).read_bytes();assert len(cut)==c['bytes'] and sha(cut)==c['sha256']
checked=json.loads((out/'final-checks-validation.json').read_text());checked.update({'documents':'PASS: whole final note and nine exact inverse regions','seal':'Ready to seal after all report files are present','source_records':len(index['sources']),'literal_cuts':sum(len(s['cuts']) for s in index['sources']),'no_drift_in_reviewed_sources':True,'review_verdict':'CLEAR'})
put('verification-final.json',json.dumps(checked,indent=2)+'\n')
print(json.dumps({'status':'PASS','document_regions':9,'new_note_bytes':10380,'source_records':len(index['sources']),'literal_cuts':checked['literal_cuts']}))
