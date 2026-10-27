from pathlib import Path
import hashlib,json
repo=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-native-scan-coverage-20261027');out=area/'scan-review';sha=lambda b:hashlib.sha256(b).hexdigest()
def put(rel,b):
 p=out/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b.encode() if isinstance(b,str) else b)
rows=[];index=json.loads((out/'source-index.json').read_text())
for d in json.loads((area/'document-validation.json').read_text()):
 b=(repo/d['path']).read_bytes();assert len(b)==d['bytes'] and sha(b)==d['sha256']
 dest='documents/current/'+d['path'];put(dest,b)
 row={'document_source_path':str(repo/d['path']),'current':{'path':dest,'bytes':len(b),'sha256':sha(b)},'scope':'Inserted region read in full; whole bytes are preservation provenance.'}
 if 'offset' in d:
  prior=(area/'prior-documents'/d['path']).read_bytes();a=d['offset'];z=a+d['inserted_bytes'];assert b[:a]+b[z:]==prior
  olddest='documents/prior/'+d['path'];put(olddest,prior);insert=b[a:z];cut='documents/insertions/'+d['path'];put(cut,insert)
  row.update(prior={'path':olddest,'bytes':len(prior),'sha256':sha(prior)},insertion={'path':cut,'bytes':len(insert),'sha256':sha(insert),'byte_offset':a},inverse_exact=True)
 else:
  assert d['path']=='lean/notes-current-native-scan-coverage.md' and len(b)==11915 and sha(b)=='f44205254cd0743f8cd4040b0a8050dc5008af5db34ae7bf2e195aeadd0a2be5'
  row['scope']='Whole new note read. All claims checked against exact three sources, public signatures, scope and recorded checks.'
  c='cuts/notes-current-native-scan-coverage.md.1-'+str(len(b.splitlines()))+'.txt';put(c,b)
  index['sources'].append({'source':str(repo/d['path']),'whole':{'path':dest,'bytes':len(b),'sha256':sha(b)},'review_scope':'Whole final note read. Native no-hook coverage, original support, quantifier scopes, own branch effects, preserved attempts and global limits checked.','cuts':[{'path':c,'bytes':len(b),'sha256':sha(b),'first_line':1,'last_line':len(b.splitlines())}]})
 rows.append(row)
assert len(rows)==10 and sum(r.get('inverse_exact',False) for r in rows)==9
put('source-index.json',json.dumps(index,indent=2)+'\n')
put('documents/independent-validation.json',json.dumps({'status':'PASS','all_nine_insertions_read':True,'whole_new_note_read':True,'all_nine_complete_prior_bodies_recovered':True,'documents':rows},indent=2)+'\n')
for rel in ['document-validation.json','document-paths.json']:
 put('evidence/'+rel,(area/rel).read_bytes())
b=(area/'scan-owner/drafts/v1/SourcePruningEnumerationNativeBranchCoverage.lean').read_bytes();put('reviewed-drafts/scan-v1-untested.lean',b)
put('reviewed-drafts/version-provenance.json',json.dumps({'scan_v1':{'path':'reviewed-drafts/scan-v1-untested.lean','bytes':len(b),'sha256':sha(b),'check_status':'UNTESTED. Two tactic-placeholder syntax repairs precede V2 first strict check.'},'scan_v2':{'path':'reviewed-drafts/scan-v2.lean','sha256':sha((out/'reviewed-drafts/scan-v2.lean').read_bytes()),'check_status':'Actual strict-scan-1 failed; source and 273-byte diagnostic preserved.'},'scan_v3':{'path':'reviewed-drafts/scan-v3.lean','sha256':sha((out/'reviewed-drafts/scan-v3.lean').read_bytes()),'check_status':'Actual strict-scan-2 passed with empty diagnostic. Exact installed source.'},'head_v1':'Actual strict-head-1 passed unchanged.','parent_v1':'Actual strict-parent-1 passed unchanged.'},indent=2)+'\n')
put('reviewed-drafts/status-before-final-docs.json',(out/'reviewed-drafts/status.json').read_bytes())
put('reviewed-drafts/status.json',json.dumps({'status':'FINAL REVIEW CLEAR','source_head':'8368460445fe4b05073a1bf134e9e34e190f2282','sources':'Three final installed sources match successful strict snapshots. All proof sources and complete new public blocks read.','documents':'Whole new note and all nine insertions read; nine exact complete old-body inverses verified.','future_claims':'No archive, evidence-commit, push or publication result asserted.','compiler_run_by_reviewer':False},indent=2)+'\n')
print(json.dumps({'status':'PASS','documents':len(rows),'full_inverse_documents':9,'source_records':len(index['sources']),'literal_cuts':sum(len(r['cuts']) for r in index['sources'])}))
