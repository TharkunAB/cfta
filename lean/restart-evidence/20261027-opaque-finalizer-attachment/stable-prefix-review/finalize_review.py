from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import hashlib,json,shutil
A=Path('/tmp/mcfta-opaque-finalizer-attachment-20261027');O=A/'stable-prefix-review';R=Path('/home/tritlo/Code/mcfta')
assert not (O/'FROZEN').exists()
def sha(d):return hashlib.sha256(d).hexdigest()
def save(rel,d):
 p=O/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(d);return {'snapshot':str(p),'bytes':len(d),'sha256':sha(d)}
def put(rel,x):return save(rel,(json.dumps(x,indent=2,ensure_ascii=False)+'\n').encode())
history=O/'review-revisions/pre-claim';history.mkdir(parents=True,exist_ok=True)
for name in ['source-index.json','report.txt','OPEN.json','verification.json','public-review.json']:
 shutil.copyfile(O/name,history/name)
index=json.loads((O/'source-index.json').read_text());records=index['sources']
def capture(source,rel,scope):
 source=Path(source);d=source.read_bytes();r={'source':str(source),**save(rel,d),'scope':'whole evidence input','reviewed_scope':scope,'cuts':[]};records.append(r);return d,r
validation_data,_=capture(A/'document-validation.json','documents/document-validation.json','whole final document byte/offset validation read')
capture(A/'document-paths.json','documents/document-paths.json','whole final document path list read')
capture(A/'upstream-status.json','documents/upstream-status.json','whole source-only/unintegrated/unexecuted candidate status receipt read; no independent native execution performed')
validation=json.loads(validation_data)
inverses=[];common=[];note_identity=None
for item in validation:
 source=R/item['path'];d=source.read_bytes()
 assert len(d)==item['bytes'] and sha(d)==item['sha256']
 if 'offset' not in item:
  assert item['path']=='lean/notes-current-opaque-finalizer-attachment.md'
  copied,rec=capture(source,'documents/notes-current-opaque-finalizer-attachment.md','WHOLE final note read; all claims checked against actual sources, signatures and receipts')
  note_identity={'path':str(source),'bytes':len(d),'sha256':sha(d)}
  continue
 offset=item['offset'];length=item['inserted_bytes'];cut=d[offset:offset+length]
 first=d[:offset].count(b'\n')+1;last=first+len(cut.splitlines(keepends=True))-1
 assert b''.join(d.splitlines(keepends=True)[first-1:last])==cut
 before=(A/'prior-documents'/item['path']).read_bytes();inverse=d[:offset]+d[offset+length:]
 assert inverse==before
 relative='documents/cuts/'+item['path'].replace('/','__')+'.txt'
 rec={'source':str(source),'bytes':len(d),'sha256':sha(d),'scope':'WHOLE parent identity only; reviewed copy is explicitly a literal status-region cut','reviewed_scope':'only inserted current status region read; historical body not reread','cuts':[{'first_line':first,'last_line':last,'byte_offset':offset,**save(relative,cut),'scope':'literal inserted-region cut'}]}
 records.append(rec)
 inverses.append({'path':str(source),'first_line':first,'last_line':last,'offset':offset,'inserted_bytes':length,'inserted_sha256':sha(cut),'parent_bytes':len(d),'parent_sha256':sha(d),'prior_source':str(A/'prior-documents'/item['path']),'prior_bytes':len(before),'prior_sha256':sha(before),'inverse_bytes':len(inverse),'inverse_sha256':sha(inverse),'exact_inverse':True})
 if item['path']!='FINDINGS.md':common.append(cut)
assert len(inverses)==9 and len(common)==8 and all(c==common[0] for c in common)
assert note_identity['bytes']==9772 and note_identity['sha256']=='12cfd4ebb60694a49999acb13562b83d273d15960c7c23129cc1b02e282c37eb'
put('documents/inverse-verification.json',{'status':'PASS','all_nine_inverses_literal':True,'common_eight_regions_identical':True,'cut_convention':'one-based inclusive lines, original LF retained; byte offsets are zero-based','documents':inverses})
# Recheck exact current final source/strict/installed correspondence and source totals.
modules=json.loads((A/'modules.json').read_text());expected=['60806a2783eb4988013b5089f5414ebdbb19c25bdf09828efd2ebdc6a9849434','7c4ce6fa84d85da5e599fcf491b8ffd3f0aa8179c886eae429af6480104429af','5255b78cbf45c0be30060b9cc0f754e7e10ac9717eccad66475edd8968921896'];total_lines=0
for name,digest in zip(modules,expected):
 d=(R/f'lean/MicroCFTA/{name}.lean').read_bytes();assert sha(d)==digest;total_lines+=len(d.splitlines())
assert total_lines==484
head=(A/'source-head.txt').read_text().strip();assert head=='70cfa4a3ab78f0d28bf14952d8a6a5491a0b38a5'
now=datetime.now(ZoneInfo('Europe/Stockholm')).isoformat()
# Preserve prior phase report text and add its final claim closure as the main report.
report=f'''[{now}] FINAL CLEAR: opaque head/finalizer/own-output attachment, source checkpoint {head}.

Scope and final sources. The whole three installed modules were reviewed: StablePrefixResources 195 lines / {expected[0]}; FinalizerAttachment 203 lines / {expected[1]}; OutputAttachment 86 lines / {expected[2]}. Total 484 lines and four public theorems. The final module documentation is the only change from the earlier checked stable-prefix and attachment v2 proofs. All installed bytes match final strict source snapshots. No repository edit, Lean/compiler/build, Git, network or board action was run for this review.

Literal preservation. The ENTIRE old PrefixResources theorem contract recovers exactly: 5,226 bytes / SHA256 6c88b15b50516d558ac63223e21be2abaced2e83a9bea83882170d539b2d94f7. The mapping removes only the appended prefixResult conjunct, its observer grouping parentheses, and the new theorem name. The initial admission is unchanged. The full old proof body also recovers after removal of the one added goal/proof and separator. Both original traversal producer calls remain. All prior Post/full-Memos/cache/history/resource/rejection fields remain. A fixed prefixResult is chosen before every extra-fuel quantifier and may be stopped; the Packet-to-actual-complete-Trace observer remains conditional. Safe is never inferred from a stopped rejection or Frame.

Finalizer attachment. The new theorem consumes the original derived CompletedHeadReceipt plus actual projection/static child location/recursiveBoundary/nonterminal bucket gates. EdgeInputs.complete and own_prefix_packet derive genuine own-cache admission at the same native caller, full Memos and metadata. Original edge reservation derives the exact full child cost. The first adequate completed-head observation fixes the actual prefix endpoint and its original admitted remaining reservation. The suffix isolation producer is called once. A second common bound simultaneously covers the head, fixed prefix and that same suffix producer. Actual complete traces align the prefix caller/cache/queries, then fuel-independent Mu/Union allocation aligns the opaque cache, then the actual suffix aligns its exact final child cache/caller/queries. The actual residual and successful parent finalizer therefore retain isolation at the ORIGINAL headCache. Original Ready.inside plus own/prefix growth separates the parent slot from the fresh root. The actual suffix Post.keeps transports lookup to the same reached heap. No endpoint equality, final isolation, separate future prefix/suffix/finalizer success, or desired assignment is admitted. The full Memos witnesses stay their own actual producer witnesses; query equality is not full-Memos equality.

Own-output consumer. The head theorem is called once. An ACTUAL singleton false recordTypes result supplies callback Success, and its frame preserves isolation using genuine Total from head.completed.safe. The SAME remaining ResourceHistory starts at the literal Restart.decision, framed callback cache, returned inventory, reached caller, FULL returned Memos and recorded metadata. Its boundary-persistence induction gives isolation at the SAME output.cache and lookup at output.caller's OWN heap. That output is not Discharged. These are concrete actual path inputs of a local consumer. The theorem does not claim that every output contains an opaque event, does not transfer one sibling's cache to another, and is not a completion producer from a bare Packet. Earlier source analyses are retained in review-revisions and consumer-review.txt.

Validation read. All three final strict checks pass with raw0, warningAsError/all linters and actual memory.max/high 4 GiB, swap0. Actual strict Audit passes with its 56-byte informational output and 79,492 checked dependencies. Aggregate build passes 4,153 jobs / 79,492 dependencies; the pre-existing InternedFreshOrdinaryClosedCompletion unused-input warning is retained. Full public readback was read in consecutive chunks 1-353 and 354-676: seven complete signatures, four new, no printed data definitions, only propext/Classical.choice/Quot.sound. Whole public output is 48,268 bytes / eb63cd44545c988a6b73c3ee64b70fa810a291779c2cdf88636e4653841328bc. H6 and both prior conditional captured-renderer blocks independently compare byte-exact to the prior readback. source-validation reports four checked source identities including Audit and no Haskell source changes. The failed output attempts1/2 are retained: both checked v1 and failed for unresolved lookupNode; attempt2 repeated the wrong source path. Its honest correction receipt and successful v2 attempt3 are kept. No failed v1 is represented as a pass.

Final prose. The WHOLE final 9,772-byte note / {note_identity['sha256']} and all nine inserted current status regions were read. Eight common regions are byte-identical; the full FINDINGS region additionally records the KBO repair candidate. All nine inverse insertions independently reproduce exact prior bytes. Copy records label each status region as a cut and retain its full parent identity. No old historical document body was reread or mislabeled as a whole-source copy. No source or prose precision issue remains.

Strongest honest claim and open work. An actual admitted stable completed head with the stated opaque child occurrence retains that created isolated boundary at its own final cache; its actual false callback and SAME admitted tail preserve it at their own emitted output, excluding full structural discharge there. This does not establish whole-history backward assignment meaning, acceptance/coverage, remaining checked fresh-arity/retention provenance or physical Haskell execution correctness. Initial Canonical/storage is not Satisfies. Global H6 and the two conditional captured-renderer statements remain unchanged. The whole-system goal remains ACTIVE.

Upstream scope. The note/FINDINGS record origin/fix/kbo-definition-weights candidate d7b6a9dfff464eb32c17c314d4825d5b027f1b2d only as Root's source assessment: Natural weights, a lazy memoized acyclic map and a context-closure regression. It is not on main, integrated, built or executed in this checkpoint. Main remains 8766699b594eaad80381af2eee034c378ccf3192. No runtime repair success or Haskell defect beyond the retained earlier findings is inferred.

Publication condition. The archive paragraph is a concrete subsequent publication requirement. Root must create the immutable archive only after this review and live preflight pass, then verify portable frozen bytes and --committed tracked bytes before authorized push. This report does not assert archive creation, committed verification, publication or push already occurred. Those receipts remain outside the frozen bundle. All earlier frozen areas were left untouched.

Evidence. source-index.json records whole source/check identities and exact labeled literal cuts. contract-comparison.json and attachment-comparison.json preserve the full old contract/body and documentation-only mappings. public-review.json records all old-block byte equalities. documents/inverse-verification.json records all nine prior-body inverses. All stages and original failed sources remain preserved. This final report closes and seals only the bounded requested review.
'''
save('report.txt',report.encode())
public_review=json.loads((O/'public-review.json').read_text());public_review['prose_review']='FINAL CLEAR; all nine inverses verified';public_review['reviewed_at']=now;put('public-review.json',public_review)
put('prose-review.json',{'status':'CLEAR','reviewed_at':now,'source_checkpoint':head,'whole_note':note_identity,'new_status_regions':9,'all_inverse_bytes_exact':True,'historical_bodies_reread':False,'prefix_copies_are_explicit_cuts':True,'upstream_candidate':'source-only, unintegrated, unbuilt, unexecuted','archive_status':'subsequent publication requirement, not verified by this review','whole_goal_status':'ACTIVE'})
put('source-index.json',{'schema':'whole sources and explicit literal cuts','cut_convention':'one-based inclusive lines; splitlines(keepends=True); original LF bytes retained','sources':records})
# No OPEN marker remains, but historical OPEN stages are retained.
(O/'OPEN.json').unlink()
put('status.json',{'status':'FINAL CLEAR','reviewed_at':now,'source_checkpoint':head,'scope':'final actual three modules + public/build/Audit/document claims','publication_outcome':'not asserted'})
checks=0
for rec in records:
 d=Path(rec['source']).read_bytes();assert len(d)==rec['bytes'] and sha(d)==rec['sha256']
 if 'snapshot' in rec:assert d==Path(rec['snapshot']).read_bytes()
 checks+=1
 for cut in rec.get('cuts',[]):
  c=b''.join(d.splitlines(keepends=True)[cut['first_line']-1:cut['last_line']]);assert len(c)==cut['bytes'] and sha(c)==cut['sha256'] and c==Path(cut['snapshot']).read_bytes();checks+=1
assert (O/'comparison/old-contract.txt').read_bytes()==(O/'comparison/final-documented-recovered-old-contract.txt').read_bytes()
assert (O/'comparison/old-proof-body.txt').read_bytes()==(O/'comparison/recovered-old-proof-body.txt').read_bytes()
put('verification.json',{'status':'PASS','checked_at':now,'source_records':len(records),'cut_records':sum(len(r['cuts']) for r in records),'whole_and_cut_byte_checks':checks,'old_full_contract_and_body_literal':True,'all_nine_document_inverses_literal':True,'final_sources_match_installed_and_strict':True})
files={}
for p in sorted(O.rglob('*')):
 if p.is_file() and p.name not in ['FROZEN','pins.json']:
  d=p.read_bytes();files[str(p.relative_to(O))]={'bytes':len(d),'sha256':sha(d)}
put('pins.json',{'schema':'frozen-payload-files','files':files})
pins_data=(O/'pins.json').read_bytes();source_data=(O/'source-index.json').read_bytes();report_data=(O/'report.txt').read_bytes()
seal={'status':'FINAL CLEAR / FROZEN','frozen_at':now,'source_checkpoint':head,'payload_files':len(files),'total_files_including_pins_and_seal':len(files)+2,'source_records':len(records),'literal_cuts':sum(len(r['cuts']) for r in records),'pins':{'path':'pins.json','bytes':len(pins_data),'sha256':sha(pins_data)},'source_index':{'path':'source-index.json','bytes':len(source_data),'sha256':sha(source_data)},'report':{'path':'report.txt','bytes':len(report_data),'sha256':sha(report_data)},'publication_outcome':'not asserted; Root must perform archive/committed verification after review'}
put('FROZEN',seal)
print(json.dumps({**seal,'FROZEN_sha256':sha((O/'FROZEN').read_bytes())},indent=2))
