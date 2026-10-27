from pathlib import Path
import hashlib,json,datetime
from zoneinfo import ZoneInfo
base=Path('/tmp/mcfta-traversal-coverage-20261027/owner');stage=base.parent;root=Path('/home/tritlo/Code/mcfta')
assert not (base/'FROZEN.json').exists()
sha=lambda d:hashlib.sha256(d).hexdigest()
now=datetime.datetime.now(ZoneInfo('Europe/Stockholm')).strftime('%Y-%m-%d %H:%M:%S %Z')
head='6e496d20bf4c574eb00264a5efb237ad47368fcc'
index=json.loads((base/'source-index.json').read_text());sources=index['sources']
def whole(src,rel):
 data=src.read_bytes();out=base/rel;out.parent.mkdir(parents=True,exist_ok=True)
 if out.exists():assert out.read_bytes()==data,rel
 else:out.write_bytes(data)
 if not any(x['snapshot']==rel for x in sources):sources.append({'source':str(src),'snapshot':rel,'bytes':len(data),'sha256':sha(data),'cuts':[]})
 return next(x for x in sources if x['snapshot']==rel)
def literal_cut(src,rel,a,b):
 full=src.read_bytes();data=b''.join(full.splitlines(keepends=True)[a-1:b]);out=base/rel;out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(data)
 record=next((x for x in sources if x['source']==str(src)),None)
 if record is None:raise AssertionError('Capture the full source before its cuts: '+str(src))
 record['cuts'].append({'snapshot':rel,'first_line':a,'last_line':b,'bytes':len(data),'sha256':sha(data),'source_sha256':sha(full)})
module='SourcePruningEnumerationTraversalCoverage';installed=root/'lean/MicroCFTA'/(module+'.lean');expected='2c364afef1dc3f20742e48a2822f70b06589a98563c0bb688f81a2694b3497c6'
assert sha(installed.read_bytes())==expected and installed.read_bytes()==(base/'drafts/v2'/(module+'.lean')).read_bytes()
whole(installed,'installed/'+module+'.lean')
for rel in ['source-validation.json','public-validation.json','public-declarations.json','public-definitions.json','modules.json','prior-public-declarations.json','prior-strong-sources.json','audit-import-insertion.json','traversal-dependent-result-repair.json','document-validation.json']:
 whole(stage/rel,'final-evidence/'+rel)
for folder,names in [('audit-coverage-1',['report.json','raw.log']),('strict-audit-coverage-1',['report.json','raw.log','MicroCFTA/Audit.lean']),('public-readback-1',['public.lean','report.json','raw.log']),('prior-public-readback',['public.lean','report.json','raw.log'])]:
 for name in names:whole(stage/folder/name,'final-evidence/'+folder+'/'+name)
public=(stage/'public-readback-1/raw.log').read_bytes();prior=(stage/'prior-public-readback/raw.log').read_bytes()
assert len(public)==592943 and sha(public)=='921cbdba138795f31429b180e44c0c7489159d4305a1d5b977682740759bd354'
assert len(prior)==577783 and public.startswith(prior)
literal_cut(stage/'public-readback-1/raw.log','public/full-new-signature-and-axioms.txt',8252,8442)
v=json.loads((stage/'public-validation.json').read_text());assert v['status']=='pass' and v['theorem_signatures_and_axiom_checks']==163 and len(v['unchanged_prior_signatures'])==162 and v['new_public_theorems']==1
assert set(v['axioms'])=={'propext','Classical.choice','Quot.sound'} and v['no_elision']
oldpins=json.loads((stage/'prior-strong-sources.json').read_text());assert len(oldpins)==85
for x in oldpins:
 data=(root/x['path']).read_bytes();assert len(data)==x['bytes'] and sha(data)==x['sha256']
for name in ['strict-traversal-coverage-2','strict-audit-coverage-1','audit-coverage-1','public-readback-1']:
 r=json.loads((stage/name/'report.json').read_text());raw=(stage/name/'raw.log').read_bytes()
 assert r['exit_code']==0 and len(raw)==r['bytes'] and sha(raw)==r['sha256']
 assert r['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
checksource=json.loads((stage/'source-validation.json').read_text());assert checksource['status']=='pass'
for x in checksource['strict_checks']:
 data=(root/'lean/MicroCFTA'/(x['module']+'.lean')).read_bytes();assert len(data)==x['bytes'] and sha(data)==x['sha256']
audit=(root/'lean/MicroCFTA/Audit.lean').read_bytes();old_audit=(stage/'prior-sources/Audit.lean').read_bytes();audit_insert=json.loads((stage/'audit-import-insertion.json').read_text())
o=audit_insert['insertion_offset'];n=audit_insert['inserted_bytes'];assert audit[:o]+audit[o+n:]==old_audit
note=root/'lean/notes-current-traversal-coverage.md';note_data=note.read_bytes();assert len(note_data)==9240 and sha(note_data)=='dc365eb22f22352d822c2c8cfb5280a834cebb48001d1855eedee4ec02587b12'
whole(note,'prose/notes-current-traversal-coverage.md')
regions=[]
# Status parents are recorded with full identity. Their inspected copies are explicitly cuts.
for item in json.loads((stage/'document-validation.json').read_text()):
 path=root/item['path'];data=path.read_bytes();assert len(data)==item['bytes'] and sha(data)==item['sha256']
 if 'offset' not in item:continue
 start=item['offset'];end=start+item['inserted_bytes'];cut=data[start:end];old=(stage/'prior-documents'/item['path']).read_bytes()
 assert data[:start]+data[end:]==old and len(old)==item['prior_bytes'] and sha(old)==item['prior_sha256']
 a=data[:start].count(b'\n')+1;b=a+len(cut.splitlines(keepends=True))-1;assert b''.join(data.splitlines(keepends=True)[a-1:b])==cut
 rel='prose/inserted-regions/'+item['path']+'.txt';dst=base/rel;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(cut)
 regions.append({**item,'copy_kind':'literal_cut','snapshot':rel,'first_line':a,'last_line':b,'cut_bytes':len(cut),'cut_sha256':sha(cut),'inverse_status':'PASS exact preserved old bytes'})
assert len(regions)==9 and len({x['cut_sha256'] for x in regions})==2
prose={'status':'CLEAR','reviewed_at':now,'source_checkpoint':head,'full_note':{'source':str(note),'snapshot':'prose/notes-current-traversal-coverage.md','bytes':len(note_data),'sha256':sha(note_data)},'labeled_cuts':regions,'all_nine_old_document_inverses':'PASS','publication_archive_status':'Future Root action; not claimed by this review.'}
(base/'prose-review.json').write_text(json.dumps(prose,indent=2)+'\n')
# Record document cuts separately to avoid labeling partial copies as parent wholes.
(base/'document-cuts.json').write_text(json.dumps({'sources':[{'source':str(root/x['path']),'bytes':x['bytes'],'sha256':x['sha256'],'cuts':[{'snapshot':x['snapshot'],'first_line':x['first_line'],'last_line':x['last_line'],'bytes':x['cut_bytes'],'sha256':x['cut_sha256'],'source_sha256':x['sha256']}]} for x in regions]},indent=2)+'\n')
final={'status':'CLEAR','reviewed_at':now,'source_checkpoint':head,'source_sha256':expected,'full_old_contract_bytes':4287,'full_old_contract_sha256':'66bf891214a4587438f2dae24599e3bacf0a8efe57ccaae3ebd254d7c745528c','public_bytes':len(public),'public_sha256':sha(public),'old_public_prefix_bytes':len(prior),'old_blocks_byte_exact':162,'unchanged_prior_source_pins':85,'audit_jobs':4238,'audit_theorem_dependencies':80056,'own_public_block_first_line':8252,'own_public_block_last_line':8442,'nine_document_inverses':True,'audit_import_inverse':True,'new_definitions':0,'standard_axioms_only':True}
(base/'final-validation.json').write_text(json.dumps(final,indent=2)+'\n')
report=(base/'report.txt').read_text()
report+='\nFINAL CLEAR — '+now+'; source checkpoint '+head+'.\nInstalled exact v2 matches its successful strict snapshot and immutable draft. The entire new public signature and standard-three-axiom block were read (lines8252–8442), including full original admission/result packet, bounds-before-model observer, native endpoint/cache/query identities, ordered full-bucket acceptance, extension agreement and both original/final Satisfies conclusions. Current public bytes592943/SHA256921cbdba138795f31429b180e44c0c7489159d4305a1d5b977682740759bd354 start with the entire literal prior577783-byte output, preserving all162 earlier blocks. All85 prior source pins were checked against live bytes. Source/Audit standalone strict checks and installed Audit4238jobs/80056theorem dependencies pass at actual4GiB/swap0. Successful source raw is empty; strict Audit raw is its expected56-byte theorem report. The exact old Audit file is recovered by removing its one added import.\n\nThe full9240-byte new note (SHAdc365eb22f22352d822c2c8cfb5280a834cebb48001d1855eedee4ec02587b12) and the two distinct inserted payloads were read. Eight status regions are identical; FINDINGS adds its unchanged-repair-scope paragraph. All nine exact inserted cuts and parent source identities are retained with explicit cut bounds and labels; removing each insertion reproduces the complete preserved old document bytes. No partial copy is labeled as a whole parent document. The note and regions accurately state constructive coverage of ordered symbolic child preparation under original native/resource admission and accepted initial model. They explicitly leave actual selected-edge coverage, selector/pruning completeness, recursive expansion/rendering coverage, remaining native/public admissions, convergence and physical Haskell correspondence open. Opaque Mu/Union empty buckets and all earlier Haskell findings stay explicit. Original H6 and finite-render soundness claims are unchanged. No material precision issue remains.\n\nThis seal freezes only the reviewed source/data bytes. Portable archive creation/verification, committed-byte verification and publication remain later Root actions. The report does not claim that those actions already ran. No compiler/build/Git/network/board/repository or older frozen-area mutation was performed by this worker. No writes are permitted inside this owner bundle after FROZEN.json is created.\n'
(base/'report.txt').write_text(report)
index.update(status='FINAL_CLEAR',sources=sources);(base/'source-index.json').write_text(json.dumps(index,indent=2)+'\n')
# Recheck each retained source/cut and every labeled document cut before creating the seal.
for s in sources:
 data=(base/s['snapshot']).read_bytes();assert len(data)==s['bytes'] and sha(data)==s['sha256'];assert Path(s['source']).read_bytes()==data
 for c in s.get('cuts',[]):
  cut=(base/c['snapshot']).read_bytes();assert len(cut)==c['bytes'] and sha(cut)==c['sha256'];assert b''.join(data.splitlines(keepends=True)[c['first_line']-1:c['last_line']])==cut
for r in regions:
 cut=(base/r['snapshot']).read_bytes();assert sha(cut)==r['cut_sha256']
payloads=[]
for path in sorted(base.rglob('*')):
 if path.is_file() and path not in [base/'pins.json',base/'FROZEN.json']:
  data=path.read_bytes();payloads.append({'path':str(path.relative_to(base)),'bytes':len(data),'sha256':sha(data)})
pins={'status':'FROZEN','created_at':now,'source_checkpoint':head,'exclusions':['pins.json','FROZEN.json'],'files':payloads};pbytes=(json.dumps(pins,indent=2)+'\n').encode();(base/'pins.json').write_bytes(pbytes)
seal={'status':'FROZEN','review':'CLEAR','created_at':now,'source_checkpoint':head,'pins':'pins.json','pins_sha256':sha(pbytes),'payload_count':len(payloads),'exact_file_count':len(payloads)+2,'source_records':len(sources),'source_literal_cuts':sum(len(x.get('cuts',[])) for x in sources),'document_literal_cuts':len(regions),'excluded_only_own_root_pins_and_seal':True}
(base/'FROZEN.json').write_text(json.dumps(seal,indent=2)+'\n')
physical={str(p.relative_to(base)) for p in base.rglob('*') if p.is_file()};assert physical=={x['path'] for x in payloads}|{'pins.json','FROZEN.json'}
for x in payloads:
 data=(base/x['path']).read_bytes();assert len(data)==x['bytes'] and sha(data)==x['sha256']
print(json.dumps({**seal,'FROZEN_sha256':sha((base/'FROZEN.json').read_bytes())},indent=2))
