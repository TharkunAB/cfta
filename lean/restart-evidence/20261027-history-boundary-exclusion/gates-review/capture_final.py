from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import hashlib,json,re,shutil
A=Path('/tmp/mcfta-history-boundary-exclusion-20261027');O=A/'gates-review';R=Path('/home/tritlo/Code/mcfta')
def sha(d):return hashlib.sha256(d).hexdigest()
def save(rel,d):
 p=O/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(d);return {'snapshot':str(p),'bytes':len(d),'sha256':sha(d)}
def put(rel,obj):return save(rel,(json.dumps(obj,indent=2,ensure_ascii=False)+'\n').encode())
assert not (O/'FROZEN').exists()
h=O/'review-revisions/before-final';h.mkdir(parents=True,exist_ok=True)
for n in ['source-index.json','report.txt','OPEN.json','verification.json']:
 assert not (h/n).exists();shutil.copyfile(O/n,h/n)
records=json.loads((O/'source-index.json').read_text())['sources']
def capture(p,rel,scope,cuts=()):
 p=Path(p);d=p.read_bytes();rec={'source':str(p),**save(rel,d),'scope':'whole source/evidence identity','reviewed_scope':scope,'cuts':[]};records.append(rec)
 for first,last,label in cuts:
  c=b''.join(d.splitlines(keepends=True)[first-1:last]);rec['cuts'].append({'first_line':first,'last_line':last,**save(f'final-cuts/{p.stem}-{first}-{last}.txt',c),'scope':'literal cut','purpose':label})
 return d
for rel in ['source-head.txt','modules.json','strict-checks.json','source-validation.json','public-declarations.json','public-definitions.json','public-validation.json','document-paths.json','document-validation.json']:
 capture(A/rel,'final-evidence/'+rel,'whole final checkpoint metadata and validator receipt read')
assert (A/'source-head.txt').read_text().strip()=='87f6dee2580ba6b668775a34325b015ff2bfe4d0'
for phase in ['build-audit-final-1','strict-audit-final-1','public-readback-final-1']:
 report=json.loads(capture(A/phase/'report.json','final-evidence/'+phase+'/report.json','whole actual executed report read'))
 raw=capture(A/phase/'raw.log','final-evidence/'+phase+'/raw.log','WHOLE actual output read; public all1,568lines read in bounded chunks')
 assert report['exit_code']==0 and report['bytes']==len(raw) and report['sha256']==sha(raw)
 assert report['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 if phase=='build-audit-final-1':assert b'4160 jobs' in raw and b'79503 MicroCFTA theorems' in raw
 if phase=='strict-audit-final-1':assert raw==b'Checked axiom dependencies of 79503 MicroCFTA theorems.\n'
 if phase=='public-readback-final-1':assert len(raw)==110300 and sha(raw)=='383122731300d777da08a143fd2bf7112ea939f603b31eb2ffabca60f2e962ba'
capture(A/'public-readback-final-1/public.lean','final-evidence/public-readback-final-1/public.lean','whole public command source read')
# Literal full declarations, including axiom rows, from the actual public readback.
public=A/'public-readback-final-1/raw.log';data=public.read_bytes()
rec=next(x for x in reversed(records) if x['source']==str(public))
spans=[(1,74,'checked head fresh arity'),(75,158,'same-output full child retention'),(159,368,'entire selected checked-output consumer'),(369,400,'full ordinary receipt forget signature'),(401,446,'full decorated history forget signature'),(447,505,'full history assignment soundness'),(506,552,'own output Packet'),(553,631,'own output assignment construction'),(632,730,'original-root render soundness'),(731,877,'entire finite producer/conditional observer'),(878,930,'unchanged global H6'),(931,1057,'unchanged native captured renderer'),(1058,1200,'unchanged flat captured renderer'),(1201,1257,'complete ordinary arity receipt definition'),(1258,1568,'complete decorated history datatype and all constructors')]
for first,last,label in spans:
 cut=b''.join(data.splitlines(keepends=True)[first-1:last]);rec['cuts'].append({'first_line':first,'last_line':last,**save(f'public-cuts/{first}-{last}.txt',cut),'scope':'literal cut','purpose':label})
oldPublic=capture(A/'prior-public-readback/raw.log','final-evidence/prior-public-readback.log','whole prior readback identity; only three exact prior theorem blocks compared')
pattern=re.compile(rb'^(?:def |inductive )?MicroCFTA\.([A-Za-z0-9_.]+)(?:\s|$)',re.M)
def blocks(d):
 ms=list(pattern.finditer(d));return {m.group(1).decode():d[m.start():ms[i+1].start() if i+1<len(ms) else len(d)] for i,m in enumerate(ms)}
newBlocks,oldBlocks=blocks(data),blocks(oldPublic);oldResults=[]
for name in ['SourceCurrentColdFiniteWarmCalls.constructed_node_calls','SourcePruningEnumerationCapturedEdge.diagonal_render_sound_current','SourceFlatPruningCapturedEdge.render_sound_current_resources']:
 new,old=newBlocks[name],oldBlocks[name];assert new==old
 save('old-public-blocks/'+name+'.txt',new);oldResults.append({'declaration':name,'bytes':len(new),'sha256':sha(new),'byte_exact':True})
put('old-public-comparison.json',{'status':'PASS','whole_blocks_include_axiom_rows':True,'parser':'line-start declaration; def/inductive also terminate previous block','blocks':oldResults})
# Whole final note; source records for large old documents carry explicit cut-only review scope.
docResults=[];common=None
for entry in json.loads((A/'document-validation.json').read_text()):
 p=R/entry['path'];d=p.read_bytes();assert len(d)==entry['bytes'] and sha(d)==entry['sha256']
 if 'offset' not in entry:
  capture(p,'documents/'+p.name,'WHOLE final11545-byte restart note read',[(1,len(d.splitlines()),'whole final note')]);continue
 offset,count=entry['offset'],entry['inserted_bytes'];chunk=d[offset:offset+count];prior=A/'prior-documents'/entry['path'];old=prior.read_bytes();inverse=d[:offset]+d[offset+count:];assert inverse==old
 if entry['path']!='FINDINGS.md':
  if common is None:common=chunk
  assert chunk==common
 else:assert chunk.startswith(common)
 first=d[:offset].count(b'\n')+1;last=first+len(chunk.splitlines())-1
 assert b''.join(d.splitlines(keepends=True)[first-1:last])==chunk
 copy=save('document-cuts/'+entry['path'].replace('/','__')+'.txt',chunk)
 rec={'source':str(p),'bytes':len(d),'sha256':sha(d),'scope':'whole document identity; inspected new region ONLY','reviewed_scope':'literal inserted region read; historical body only inverse-byte equality checked','cuts':[{'first_line':first,'last_line':last,**copy,'scope':'literal cut of inserted region','byte_offset':offset,'inserted_bytes':count}]};records.append(rec)
 records.append({'source':str(prior),'bytes':len(old),'sha256':sha(old),'scope':'whole prior-document identity ONLY','reviewed_scope':'not historical semantic review; exact current-body inverse verified','cuts':[]})
 docResults.append({'path':entry['path'],'current_bytes':len(d),'current_sha256':sha(d),'inserted_offset':offset,'inserted_bytes':count,'inserted_sha256':sha(chunk),'first_line':first,'last_line':last,'prior_source':str(prior),'prior_bytes':len(old),'prior_sha256':sha(old),'recovered_prior_sha256':sha(inverse),'byte_exact_inverse':True,'cut_snapshot':copy['snapshot']})
put('document-inverses.json',{'status':'PASS','nine_old_bodies_exact':len(docResults)==9,'eight_identical_status_regions':True,'findings_extends_same_status_with_exact_inventory_and_haskell_scope':True,'historical_semantic_rereview':False,'documents':docResults})
# Recheck authoritative installed and strict identities. No compiler or external action.
sv=json.loads((A/'source-validation.json').read_text());assert sv['status']=='pass' and len(sv['strict_checks'])==8
for x in sv['strict_checks']:
 source=R/f'lean/MicroCFTA/{x["module"]}.lean';d=source.read_bytes();checked=(A/x['check']/f'MicroCFTA/{x["module"]}.lean').read_bytes();assert d==checked and len(d)==x['bytes'] and sha(d)==x['sha256']
# Review controls: preserve all preceding phase reports, replace only authoritative final summary.
now=datetime.now(ZoneInfo('Europe/Stockholm')).isoformat()
report=f'''[{now}] CLEAR — final source, public and document claim review.

Source checkpoint87f6dee2580ba6b668775a34325b015ff2bfe4d0. Read WHOLE all seven installed final modules (892lines), all13 public signatures/axiom blocks and both full data declarations (1,568lines/110,300B), the whole final note, and only the nine new document regions. No proof, repository, Git, network, board or build action was performed by this review. Previous frozen areas remain untouched. Earlier phase reports, exact contract mappings, failed attempts and corrections remain preserved inside this bundle.

Strongest result: an ACTUAL ResourceHistoryWithArity, actual restart decision, initial Canonical and SAME own-output Discharged let backward soundness transport output-own-heap assignment satisfaction to the original caller heap/cache. The actual own native renderer plus checks for every returned residual CONSTRUCTS the assignment. The ORIGINAL stored pending slot and ORIGINAL native lookup then give original native value acceptance and every original suspended Holds for the rendered term. Actual head/callback/tail/cache, returned metadata, native callers, full Memos and rendering Frame stay explicit. No final assignment, original acceptance, future success, universal Ranges or desired per-step semantic law is admitted.

Only numeric projected own arity is the added path annotation. Full old ordinary receipt/history definitions recover literally under name/appendix removal, and forget maps preserve SAME bounds/endpoints/output. Checked-constructor provenance supplies that numeric gate locally through an actual retained Post and coherent same edge identity. Same-output discharge derives full child retention; real entry gives nonterminality and initial Canonical plus actual operations gives later Canonical. Packet alone does not supply global checked-origin provenance. The bare finite producer still gives unannotated histories; all-path arity decoration from construction/intersection origins is OPEN.

The finite wrapper retains ENTIRE original2,235-byte header/conclusion prefix (f84b99bac2f1d2d7a350c343571d11b421ab32d9056c6e79d01b4f6300ff96c1), unchanged original admission and one old producer call. The arity-certified history appears ONLY as an appended observer antecedent at SAME bound+extra and actual output. No bound moves inside output/certificate quantifiers. Its original stable runtime, OutcomeResources, real per-output ResourceHistory and output Canonical family remain intact. The local selected wrapper preserves its entire old conclusion and original-inventory enteredPacket premise. Whole-history soundness correctly uses lower prefix/ordinary laws at ACTUAL post-prefix inventory/full Memos; it does not rebase inventory or infer full-Memos equality from query equality.

All seven definitive strict checks PASS/raw0 with warnings fatal/all linters and actual memory.max/high4GiB,swap0. Final aggregate PASS4160jobs/79503dependencies; its pre-existing unused-input warning is retained. Standalone strict Audit PASS56B. Public PASS110300B/{sha(data)},13signatures,10new,2full data declarations,only propext/Classical.choice/Quot.sound,no elision. Independent comparison confirms H6 and both prior captured renderer FULL signature/axiom blocks byte-exact. Source-validation8checks match actual installed/checked bytes. Historical missing-Fragment, metadata inference and install-order failures remain preserved; both finite wrapper variants passed and differ only in documentation.

The WHOLE new note11545B/7ee268ef424cec26a1aec7ec21c2a27db112de5f612b925a37227c1b13a74c61 and nine new status regions state these conditions accurately. All nine inverse removals recover the exact preserved old document bytes. Prefix/cut copies are explicitly labeled; no prefix-only snapshot is described as a whole file. H6 remains the global exact finite-tree construction claim. Unconditional bare-producer original acceptance, all-output discharge/render termination, enumeration coverage, remaining API contracts and physical Haskell execution correctness are NOT claimed. No Haskell source changed. The separate KBO candidate remains source-assessed only, unintegrated/unbuilt/unexecuted here; no fixed-defect claim is made.

No blocker found. The archive/publication prose describes the intended final checkpoint workflow. Creation and portable/committed archive verification must occur AFTER this review seal and Root's final preflight, before any authorized push. This report does NOT assert those later publication actions have happened. Stop review writes after the final FROZEN seal. Every cut uses one-based inclusive line bounds with original line endings retained.
'''
save('report.txt',report.encode());save('final-claim-review.txt',report.encode())
put('source-index.json',{'schema':'whole sources and explicit literal cuts','cut_convention':'one-based inclusive lines; splitlines(keepends=True); original LF retained; document byte offsets explicitly recorded','sources':records})
checks=0
for rec in records:
 d=Path(rec['source']).read_bytes();assert len(d)==rec['bytes'] and sha(d)==rec['sha256'];checks+=1
 if 'snapshot' in rec:assert d==Path(rec['snapshot']).read_bytes()
 for c in rec['cuts']:
  cut=b''.join(d.splitlines(keepends=True)[c['first_line']-1:c['last_line']]);assert len(cut)==c['bytes'] and sha(cut)==c['sha256'] and cut==Path(c['snapshot']).read_bytes();checks+=1
put('verification.json',{'status':'PASS','checked_at':now,'source_records':len(records),'cuts':sum(len(x['cuts']) for x in records),'byte_checks':checks,'seven_installed_match_authoritative_strict':True,'whole_public_read':True,'old_three_public_blocks_byte_exact':True,'nine_doc_inverses_byte_exact':True,'whole_note_and_nine_regions_read':True,'contract_mappings':'selected/history/finite exact literal mappings retained','publication_outcome':'not asserted; subsequent Root preflight/archive+committed verification required'})
put('OPEN.json',{'status':'CLEAR_PENDING_SEAL','reviewed_at':now,'reason':'Final byte checks complete; final seal next.','publication_outcome':'not asserted'})
print(json.dumps({'status':'CLEAR_PENDING_SEAL','source_records':len(records),'cuts':sum(len(x['cuts']) for x in records),'byte_checks':checks,'report_sha256':sha((O/'report.txt').read_bytes()),'source_index_sha256':sha((O/'source-index.json').read_bytes()),'old_public_blocks':oldResults},indent=2))
