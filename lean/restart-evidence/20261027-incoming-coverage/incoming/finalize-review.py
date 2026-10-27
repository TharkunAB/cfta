from pathlib import Path
import json,hashlib,datetime,re
from zoneinfo import ZoneInfo
stage=Path('/tmp/mcfta-incoming-coverage-20261027');root=Path('/home/tritlo/Code/mcfta')
sha=lambda d:hashlib.sha256(d).hexdigest()
now=datetime.datetime.now(ZoneInfo('Europe/Stockholm')).strftime('%Y-%m-%d %H:%M:%S %Z')
source_head='a7d1733d3b07594ad9cb4418c2caad57a5e9005d'
public=(stage/'public-readback-1/raw.log').read_bytes();prior=(stage/'prior-public-readback/raw.log').read_bytes()
assert len(public)==577783 and sha(public)=='bbae218f7ede41793b66af3e68c8d2368517d023eb8992ec04301425557cb5f7'
assert public.startswith(prior) and len(prior)==539153
validation=json.loads((stage/'public-validation.json').read_text())
assert validation['status']=='pass' and validation['theorem_signatures_and_axiom_checks']==162 and len(validation['unchanged_prior_signatures'])==159
prior_sources=json.loads((stage/'prior-strong-sources.json').read_text());assert len(prior_sources)==82
for item in prior_sources:
 data=(root/item['path']).read_bytes();assert len(data)==item['bytes'] and sha(data)==item['sha256'],item['path']
source_validation=json.loads((stage/'source-validation.json').read_text())
for item in source_validation['strict_checks']:
 data=(root/'lean/MicroCFTA'/(item['module']+'.lean')).read_bytes();assert len(data)==item['bytes'] and sha(data)==item['sha256']
note=root/'lean/notes-current-incoming-coverage.md';note_data=note.read_bytes();assert len(note_data)==10328 and sha(note_data)=='f571036f4186dfb527149e45b5c95f4252c012e7546e27d2c6ad501276b3e91c'
docchecks=[]
for doc in json.loads((stage/'document-validation.json').read_text()):
 data=(root/doc['path']).read_bytes();assert len(data)==doc['bytes'] and sha(data)==doc['sha256']
 if 'offset' not in doc:continue
 start=doc['offset'];end=start+doc['inserted_bytes'];cut=data[start:end];old=(stage/'prior-documents'/doc['path']).read_bytes();assert data[:start]+data[end:]==old
 assert len(old)==doc['prior_bytes'] and sha(old)==doc['prior_sha256']
 first=data[:start].count(b'\n')+1;last=first+len(cut.splitlines(keepends=True))-1
 assert b''.join(data.splitlines(keepends=True)[first-1:last])==cut
 docchecks.append({**doc,'status':'PASS','literal_inverse_equals_preserved_old':True,'first_line':first,'last_line':last,'inserted_sha256':sha(cut)})
assert len(docchecks)==9 and len({x['inserted_sha256'] for x in docchecks})==2
for part,module,expected,block in [
 ('incoming','SourcePruningEnumerationIncomingCoverage','5d15f95614ff82c87a13bf102f6ad5a29cd631bc1a281a1882da2a3bb5c181b5',(7766,7967)),
 ('child','SourcePruningEnumerationChildCoverage','42c2c04998f0da78b90a545311429e5488b5b96f017ff96ef8bd2ee3580cf73d',(8095,8251))]:
 base=stage/part;assert not (base/'FROZEN.json').exists()
 index=json.loads((base/'source-index.json').read_text());records={x['snapshot']:x for x in index['records']}
 def whole(src,rel):
  data=src.read_bytes();dst=base/rel;dst.parent.mkdir(parents=True,exist_ok=True)
  if dst.exists():assert dst.read_bytes()==data,rel
  else:dst.write_bytes(data)
  records[rel]={'kind':'whole','source':str(src),'snapshot':rel,'bytes':len(data),'sha256':sha(data)}
 def cut(src,rel,a,b):
  full=src.read_bytes();data=b''.join(full.splitlines(keepends=True)[a-1:b]);dst=base/rel;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(data)
  records[rel]={'kind':'cut','source':str(src),'source_bytes':len(full),'source_sha256':sha(full),'first_line':a,'last_line':b,'snapshot':rel,'bytes':len(data),'sha256':sha(data)}
 installed=root/'lean/MicroCFTA'/(module+'.lean');assert sha(installed.read_bytes())==expected
 whole(installed,'installed/'+module+'.lean')
 for rel in ['public-validation.json','source-validation.json','modules.json','strict-checks.json','public-declarations.json','document-validation.json','document-paths.json','prior-strong-sources.json','prior-public-declarations.json','audit-import-insertion.json']:
  whole(stage/rel,'final-evidence/'+rel)
 for folder,names in [('public-readback-1',['public.lean','raw.log','report.json']),('prior-public-readback',['raw.log','report.json']),('audit-coverage-1',['raw.log','report.json']),('strict-audit-coverage-1',['raw.log','report.json','MicroCFTA/Audit.lean']),('build-incoming-coverage-1',['raw.log','report.json'])]:
  for name in names:whole(stage/folder/name,'final-evidence/'+folder+'/'+name)
 cut(stage/'public-readback-1/raw.log','public/'+module+'.full-signature-and-axioms.txt',*block)
 whole(note,'prose/notes-current-incoming-coverage.md')
 for doc in docchecks:cut(root/doc['path'],'prose/inserted-regions/'+doc['path']+'.txt',doc['first_line'],doc['last_line'])
 preservation={'status':'PASS','reviewed_at':now,'whole_note':{'path':str(note),'snapshot':'prose/notes-current-incoming-coverage.md','bytes':len(note_data),'sha256':sha(note_data)},'regions':docchecks,'unique_insert_payloads':2,'scope':'Every inserted region is a labeled literal line cut. Parent document size/hash identify the full source; no cut is labeled as a whole copy. Each inverse was compared byte-for-byte with its full preserved prior document.'}
 (base/'prose-review.json').write_text(json.dumps(preservation,indent=2)+'\n')
 finalcheck={'status':'PASS','reviewed_at':now,'source_checkpoint':source_head,'installed_source':{'module':module,'sha256':expected},'public':{'bytes':len(public),'sha256':sha(public),'full_own_block_lines_inclusive':block,'all_prior_public_bytes_literal_prefix':True,'prior_bytes':len(prior),'prior_theorem_blocks':159,'current_blocks':162,'new_theorems':3,'new_definitions':0,'standard_axioms_only':validation['axioms']},'prior_source_modules_unchanged':len(prior_sources),'document_inverses':len(docchecks),'audit_jobs':4237,'audit_theorem_dependencies':80050,'scope':'Local constructive native child preparation coverage; no traversal/whole recursive coverage or physical Haskell correspondence. Publication archive verification remains a later Root action.'}
 (base/'final-validation.json').write_text(json.dumps(finalcheck,indent=2)+'\n')
 report=(base/'report.txt').read_text()
 report+='\nFINAL CLEAR — '+now+'; source checkpoint '+source_head+'.\nThe final installed source identity matches the authoritative successful strict attempt exactly. Both complete own theorem public signatures were read, including all original admissions, grouped packet clauses, full Post/Memos, native/enum endpoints, uniform bounds and semantic observers. The full 10328-byte restart note was read. All nine inserted regions were checked; eight share one exact payload and FINDINGS adds its repair-status paragraph. Removing each insertion reproduces the preserved old document byte-for-byte. The current full public output starts with the literal entire 539153-byte prior output, preserving every one of the 159 old blocks; all 82 prior source pins match live bytes. Source/public validators, full public output, own literal full public block, original strict attempts and final Audit/build receipts are retained. Installed Audit passes 4237 jobs/80050 theorem dependencies; standalone strict Audit passes with the expected 56-byte dependency report. Public output is 577783 bytes SHA256 bbae218f7ede41793b66af3e68c8d2368517d023eb8992ec04301425557cb5f7; only the standard three axioms occur.\n\nStrongest reviewed statement: genuine original child admission yields an actual uniform child packet, then each supplied original satisfying model/native accepted concrete term/full old bucket Holds derives the SAME actual singleton and satisfying assignment extension. Fresh extension preserves all old variable values, forest equalities, slot constraints and stored residual fragments. Terminal branches preserve the original assignment. Old full Memos are retained, not inferred from query equality. The read outer core is not identified with a written branch core. Mu/Union empty stored buckets remain explicit; no every-future-filling retention is claimed. The note and inserted regions correctly leave ordered traversal coverage, accepting-edge selection, semantic selector/pruning contracts, recursive coverage, discharge/renderability/convergence and physical Haskell correspondence open. No new producer admission, future row/success, desired fresh assignment or final satisfaction is assumed by the all-child producer. Incoming has only its explicitly supplied original model and current Fits/Room as semantic/resource inputs. The original global H6/startup/captured claims are unchanged. No source or claim issue remains.\n\nThis seal freezes reviewed source/data bytes only. Portable archive creation/verification, committed-byte verification and publication must be completed by Root after this review; this report does not assert those later checks have run. No further writes are permitted inside this bundle after FROZEN.json is created.\n'
 (base/'report.txt').write_text(report)
 index.update(status='FINAL_CLEAR',records=list(records.values()),line_convention='one-based inclusive; preserve original LF')
 (base/'source-index.json').write_text(json.dumps(index,indent=2)+'\n')
 # Verify every physical source/cut payload before sealing. Historical drafts are checked only against their retained original sources.
 for item in records.values():
  data=(base/item['snapshot']).read_bytes();assert len(data)==item['bytes'] and sha(data)==item['sha256']
  src=Path(item['source']);full=src.read_bytes()
  if item['kind']=='cut':actual=b''.join(full.splitlines(keepends=True)[item['first_line']-1:item['last_line']])
  else:actual=full
  assert actual==data,item['snapshot']
 # Exclude ONLY the two own root files. Nested FROZEN files, if any, remain payloads.
 payloads=[]
 for path in sorted(base.rglob('*')):
  if path.is_file() and path not in [base/'pins.json',base/'FROZEN.json']:
   data=path.read_bytes();payloads.append({'path':str(path.relative_to(base)),'bytes':len(data),'sha256':sha(data)})
 pins={'status':'FROZEN','created_at':now,'source_checkpoint':source_head,'exclusions':['pins.json','FROZEN.json'],'files':payloads}
 pbytes=(json.dumps(pins,indent=2)+'\n').encode();(base/'pins.json').write_bytes(pbytes)
 seal={'status':'FROZEN','review':'CLEAR','created_at':now,'source_checkpoint':source_head,'manifest':'pins.json','manifest_bytes':len(pbytes),'manifest_sha256':sha(pbytes),'payload_files':len(payloads),'physical_files_including_manifest_and_seal':len(payloads)+2,'source_records':len(records),'literal_cuts':sum(x['kind']=='cut' for x in records.values()),'excluded_only_own_root_manifest_and_seal':True}
 (base/'FROZEN.json').write_text(json.dumps(seal,indent=2)+'\n')
 physical={str(p.relative_to(base)) for p in base.rglob('*') if p.is_file()}
 assert physical=={x['path'] for x in payloads}|{'pins.json','FROZEN.json'}
 for x in payloads:
  data=(base/x['path']).read_bytes();assert len(data)==x['bytes'] and sha(data)==x['sha256']
 print(json.dumps({'bundle':str(base),'payload_files':len(payloads),'physical_files':len(physical),'source_records':len(records),'literal_cuts':seal['literal_cuts'],'manifest_sha256':sha(pbytes),'seal_sha256':sha((base/'FROZEN.json').read_bytes())},indent=2))
