from pathlib import Path
import hashlib,json,re
repo=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-continuation-coverage-20261027');out=area/'hook-policy-review';sha=lambda b:hashlib.sha256(b).hexdigest()
def put(rel,b):
 p=out/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b.encode() if isinstance(b,str) else b)
def copy(rel,dest=None):
 b=(area/rel).read_bytes();put(dest or 'evidence/'+rel,b);return b
raw=copy('public-readback-1/raw.log');rb=copy('public-readback-1/report.json');r=json.loads(rb);publicSource=copy('public-readback-1/public.lean');prior=copy('prior-public-readback/raw.log');new=copy('new-public-blocks.txt')
assert r['exit_code']==0 and len(raw)==r['bytes'] and sha(raw)==r['sha256'] and sha(publicSource)==r['source_sha256'];assert r['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'};assert raw==prior+new and len(raw)==783343 and len(prior)==710226 and len(new)==73117 and len(new.splitlines())==892
for b,count in [(raw,180),(prior,176),(new,4)]:
 blocks=re.findall(rb'depends on axioms: \[([^\]]*)\]',b,re.S);assert len(blocks)==count;assert all({x.strip() for x in v.split(b',')}<={b'propext',b'Classical.choice',b'Quot.sound'} for v in blocks);assert b'...' not in b and '\u2026'.encode() not in b
focus=[];text=raw.decode()
for name in ['SourceCurrentColdFiniteWarmCalls.constructed_node_calls','SourcePruningEnumerationRecursive.run_finite_complete_resources_render_sound_from_initial_arity']:
 start=re.search(r'^MicroCFTA\.'+re.escape(name)+r'(?=\s)',text,re.M).start();end=re.search(r"^'MicroCFTA\."+re.escape(name)+r"' depends on axioms: \[[^\]]*\]\n",text,re.M).end();block=text[start:end].encode();assert block in prior;dest='public-focus/'+name+'.txt';put(dest,block);focus.append({'name':name,'path':dest,'bytes':len(block),'sha256':sha(block),'exact_prior_block':True})
preserved={}
for manifest in ['prior-lean-sources.json','prior-strong-sources.json','prior-enumeration-sources.json','prior-haskell-sources.json']:
 rows=json.loads(copy(manifest))
 rows=[row for row in rows if row['path'] != 'lean/MicroCFTA/Audit.lean']
 for row in rows:
  b=(repo/row['path']).read_bytes();assert len(b)==row['bytes'] and sha(b)==row['sha256'],row['path']
 preserved[manifest]=len(rows)
audit=(repo/'lean/MicroCFTA/Audit.lean').read_bytes();old=copy('prior-sources/Audit.lean');meta=json.loads((area/'audit-import-insertion.json').read_text());at=meta['insertion_offset'];n=meta['inserted_bytes'];assert audit[:at]+audit[at+n:]==old and len(old)==meta['old_bytes'] and sha(old)==meta['old_sha256'] and sha(audit)==meta['new_sha256'];assert audit[at:at+n]==''.join('import MicroCFTA.'+m+'\n' for m in meta['modules']).encode()
for rel in ['public-validation.json','public-prefix-comparison.json','public-declarations.json','public-definitions.json','new-public-declarations.json','prior-public-declarations.json','initial-upstream-refresh.json','document-validation.json','document-paths.json','root-document-validation.json']:copy(rel)
rows=[];index=json.loads((out/'source-index.json').read_text())
for d in json.loads((area/'document-validation.json').read_text()):
 b=(repo/d['path']).read_bytes();assert len(b)==d['bytes'] and sha(b)==d['sha256'];dest='documents/current/'+d['path'];put(dest,b);row={'document_source_path':str(repo/d['path']),'current':{'path':dest,'bytes':len(b),'sha256':sha(b)}}
 if 'offset' in d:
  old=(area/'prior-documents'/d['path']).read_bytes();at=d['offset'];end=at+d['inserted_bytes'];assert b[:at]+b[end:]==old and len(old)==d['old_bytes'] and sha(old)==d['old_sha256'];oldDest='documents/prior/'+d['path'];put(oldDest,old);insert=b[at:end];insertDest='documents/insertions/'+d['path'];put(insertDest,insert);row.update(prior={'path':oldDest,'bytes':len(old),'sha256':sha(old)},insertion={'path':insertDest,'bytes':len(insert),'sha256':sha(insert),'byte_offset':at},inverse_exact=True,review_scope='Entire new inserted region read; entire current/prior documents retained for byte recovery.')
 else:
  assert d['path']=='lean/notes-current-continuation-coverage.md' and len(b)==13117 and sha(b)=='47741336661d81f2c0626b7efbff5ccdc6676a7970fad578509f8142fb3c04be';row['review_scope']='Whole new note read and checked against exact sources/public/checks/scopes.';count=len(b.splitlines());cut=f'cuts/notes-current-continuation-coverage.md.1-{count}.txt';put(cut,b);index['sources'].append({'source':str(repo/d['path']),'whole':{'path':dest,'bytes':len(b),'sha256':sha(b)},'review_scope':'Whole final note reviewed: original inputs, exact earlier-stop alternative, own native endpoints, quantifiers, attempts, resources and global limits.','cuts':[{'path':cut,'bytes':len(b),'sha256':sha(b),'first_line':1,'last_line':count}]})
 rows.append(row)
assert len(rows)==10 and sum(r.get('inverse_exact',False) for r in rows)==9
put('source-index.json',json.dumps(index,indent=2)+'\n');put('documents/independent-validation.json',json.dumps({'status':'PASS','all_four_full_new_public_blocks_read':True,'whole_new_note_read':True,'all_nine_insertions_read':True,'documents':rows},indent=2)+'\n')
# Retain named immutable untested drafts as such; strict snapshots retain every tested source.
for rel,dest in [('sibling-design/drafts/v1/SourcePruningEnumerationFiniteSiblingCoverage.lean','reviewed-drafts/sibling-v1-untested.lean'),('hook-head-review/parent-draft/drafts/v1/SourcePruningEnumerationFiniteParentCoverage.lean','reviewed-drafts/parent-v1-untested.lean'),('hook-head-review/parent-draft/drafts/v2/SourcePruningEnumerationFiniteParentCoverage.lean','reviewed-drafts/parent-v2-passed.lean')]:copy(rel,dest)
put('evidence/independent-final-observation-validation.json',json.dumps({'status':'PASS','source_head':'0684e0b726efa04c1063f0f71b24d58d77ffbea6','public':{'all_bytes':len(raw),'all_sha256':sha(raw),'old_exact_prefix_bytes':len(prior),'old_blocks':176,'new_bytes':len(new),'new_blocks':4,'all_blocks':180,'std3_only':True,'no_elision':True,'focused_prior_blocks':focus},'unchanged_source_counts':preserved,'audit_exact_inverse':True,'all_nine_document_inverses_exact':True,'reviewer_compiler_runs':0,'reviewer_build_runs':0,'future_archive_commit_publication_or_push_claims':False},indent=2)+'\n')
print(json.dumps({'status':'PASS','source_records':len(index['sources']),'literal_cuts':sum(len(r['cuts']) for r in index['sources']),'preserved':preserved,'public':len(raw),'documents':len(rows),'inverse_documents':9}))
