from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import hashlib,json,re,shutil
AREA=Path('/tmp/mcfta-opaque-finalizer-attachment-20261027')
OUT=AREA/'stable-prefix-review'
REPO=Path('/home/tritlo/Code/mcfta')


def sha(data): return hashlib.sha256(data).hexdigest()
def save(rel,data):
 p=OUT/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
 return {'snapshot':str(p),'bytes':len(data),'sha256':sha(data)}
def put_json(rel,data): return save(rel,(json.dumps(data,indent=2,ensure_ascii=False)+'\n').encode())

history=OUT/'review-revisions/pre-attachment'
history.mkdir(parents=True,exist_ok=True)
for name in ['source-index.json','report.txt','OPEN.json','verification.json']:
 if not (history/name).exists(): shutil.copyfile(OUT/name,history/name)
index=json.loads((history/'source-index.json').read_text())
records=index['sources']
# The first reviewed proof is preserved at its immutable proposal revision after comment insertion.
old_draft=records[0]
old_draft['historical_original_source']=old_draft['source']
old_draft['source']=str(AREA/'opaque-suffix-draft/revisions/stable-prefix-v1.lean')
assert sha(Path(old_draft['source']).read_bytes())==old_draft['sha256']
old_draft['scope']='whole historical pre-documentation source'

def capture(source,rel,spans,reviewed):
 p=Path(source);data=p.read_bytes();lines=data.splitlines(keepends=True)
 record={'source':str(p),**save(rel,data),'scope':'whole source/evidence input','reviewed_scope':reviewed,'cuts':[]}
 for first,last,label in spans:
  assert 1<=first<=last<=len(lines)
  cut=b''.join(lines[first-1:last])
  record['cuts'].append({'first_line':first,'last_line':last,**save(f'attachment-cuts/{p.stem}-{first}-{last}.txt',cut),'scope':'literal cut','purpose':label})
 records.append(record)
 return data

stable=capture(AREA/'opaque-suffix-draft/SourcePruningEnumerationOpaqueStablePrefixResources.lean','final-sources/SourcePruningEnumerationOpaqueStablePrefixResources.lean',[(1,11,'final module documentation'),(33,102,'full unchanged theorem contract plus appended family'),(103,142,'same two original calls and bounds'),(143,183,'actual prefix endpoint admission'),(185,193,'fixed prefix result')],'whole final source read; only module documentation added to prior reviewed proof')
attachment=capture(AREA/'opaque-suffix-draft/SourcePruningEnumerationOpaqueFinalizerAttachment.lean','final-sources/SourcePruningEnumerationOpaqueFinalizerAttachment.lean',[(1,15,'final documentation'),(36,48,'opaque prepare fuel independence'),(52,72,'full actual head admission and conclusion'),(73,106,'actual own-cache admission and original reservation'),(107,149,'first fixed event and single suffix producer'),(150,203,'common-bound endpoint alignment and actual residual/finalizer')],'whole final source read')
v2=capture(AREA/'opaque-suffix-draft/revisions/attachment-v2.lean','revisions/attachment-v2.lean',[(43,62,'full pre-documentation theorem contract'),(97,139,'first event and one suffix producer'),(140,191,'actual larger-bound replay and final attachment')],'whole checked attachment v2 read')
v1=capture(AREA/'opaque-suffix-draft/revisions/attachment-v1.lean','revisions/attachment-v1.lean',[],'historical initial draft retained; reviewed final proof is v2 plus documentation')
assert sha(stable)=='60806a2783eb4988013b5089f5414ebdbb19c25bdf09828efd2ebdc6a9849434'
assert sha(attachment)=='7c4ce6fa84d85da5e599fcf491b8ffd3f0aa8179c886eae429af6480104429af'
assert sha(v2)=='3104ea3c319b2c9723e42cf9622d10640f851cca7fa55542ec0e452abccfb9f5'

inputs=[
 ('SourcePruningEnumerationOpaqueSuffixIsolation',[(22,81,'allocation separation and actual finalizer core law'),(100,115,'actual residual/finalizer isolation'),(118,176,'full original suffix producer contract'),(177,234,'one traversal producer and protected/reference isolation')],'whole module read'),
 ('SourcePruningEnumerationHeadAdmission',[(40,102,'all actual HeadAdmission and CompletedHeadReceipt fields')],'lines 1-115 read; full identity retained'),
 ('SourcePruningEnumerationOwnPrefixPacket',[(17,55,'all actual own allocation Packet derivation')],'whole module read'),
 ('SourcePruningEnumerationOpaqueEventTrace',[(139,174,'actual complete selected children/finalizer decomposition'),(176,224,'actual opaque event with exact before/after caches')],'lines 125-226 read; full identity retained'),
 ('SourcePruningEnumerationEdgeInputs',[(14,75,'actual child list and full own prefix output'),(76,131,'actual own runtime and genuine children proof')],'whole module read'),
 ('SourcePruningEnumerationCachedPrepare',[(9,28,'actual Mu/Union branch has no fuel use')],'lines 1-105 read; focused use is prepareChild branch'),
 ('SourcePruningEnumerationIsolatedPending',[(19,34,'exact root/stored/incoming certificate and discharge exclusion'),(62,80,'actual fresh allocation isolation')],'whole module read'),
 ('SourcePruningEnumerationTraversalResources',[(30,94,'original cost and entire resource producer contract')],'lines 1-125 read; full identity retained')
]
for stem,spans,scope in inputs:
 capture(REPO/f'lean/MicroCFTA/{stem}.lean',f'attachment-inputs/{stem}.lean',spans,scope)

strict_checks=[]
for check,stem,expected in [
 ('strict-finalizer-attachment-1','SourcePruningEnumerationOpaqueFinalizerAttachment',sha(v2)),
 ('strict-stable-prefix-final-1','SourcePruningEnumerationOpaqueStablePrefixResources',sha(stable)),
 ('strict-finalizer-attachment-final-1','SourcePruningEnumerationOpaqueFinalizerAttachment',sha(attachment))]:
 source=capture(AREA/check/f'MicroCFTA/{stem}.lean',f'attachment-strict/{check}/{stem}.lean',[],'whole exact checked source compared to reviewed variant')
 report=capture(AREA/check/'report.json',f'attachment-strict/{check}/report.json',[],'whole actual strict report read')
 raw=capture(AREA/check/'raw.log',f'attachment-strict/{check}/raw.log',[],'whole empty actual strict raw output read')
 result=json.loads(report)
 assert sha(source)==expected==result['source_sha256']
 assert result['exit_code']==0 and result['bytes']==len(raw)==0 and sha(raw)==result['sha256']
 assert result['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 strict_checks.append({'name':check,'source_sha256':expected,'exit_code':0,'raw_bytes':0,'memory_max':4294967296,'swap_max':0})

comment_maps=[]
for current,basis,label in [(stable,Path(old_draft['source']).read_bytes(),'stable-prefix'),(attachment,v2,'attachment')]:
 match=re.search(rb'/-!\n.*?\n-/\n\n',current,re.S);assert match
 recovered=current[:match.start()]+current[match.end():]
 assert recovered==basis
 save(f'comment-mapping/{label}-inserted-comment.txt',match.group())
 save(f'comment-mapping/{label}-recovered-proof.lean',recovered)
 comment_maps.append({'source':label,'current_sha256':sha(current),'basis_sha256':sha(basis),'comment_only_exact':True,
  'mapping':'Remove only the new module documentation block including its following blank line.'})

# Re-run the literal full old contract recovery on the final documented stable source.
old=Path(OUT/'whole/SourcePruningEnumerationOpaquePrefixResources.lean').read_bytes()
def header(data,name):
 start=data.index(('theorem '+name+'\n').encode());end=data.index(b' := by\n',start);return data[start:end]
old_header=header(old,'complete_with_prefix_resources')
new_header=header(stable,'complete_with_stable_prefix_resources')
kept,_=new_header.rsplit(' ∧\n      ∃ prefixResult :'.encode(),1)
assert kept.endswith(b'eventBefore eventQueries)')
recovered=kept[:-1].replace(b'theorem complete_with_stable_prefix_resources\n',b'theorem complete_with_prefix_resources\n',1).replace('      (∀ {Typing : Type}'.encode(),'      ∀ {Typing : Type}'.encode(),1)
assert recovered==old_header
save('comparison/final-documented-recovered-old-contract.txt',recovered)
assert v2.count(b'EnumerationDischargeHistory.opaque_suffix_complete_isolated_resources')==1
assert attachment.count(b'EnumerationDischargeHistory.opaque_suffix_complete_isolated_resources')==1
comparison={'status':'PASS','comment_maps':comment_maps,'stable_full_old_contract_recovery':{'bytes':len(old_header),'sha256':sha(old_header),'exact':True},'attachment_suffix_producer_calls':1,'actual_own_prefix_producer_calls':1,'actual_stable_prefix_producer_calls':1,'strict_checks':strict_checks,'attachment_is_new_consumer_not_replacement_producer':True}
put_json('attachment-comparison.json',comparison)
put_json('source-index.json',{'schema':'whole sources and explicit literal cuts','cut_convention':'one-based inclusive lines; splitlines(keepends=True); original LF bytes retained','sources':records})
now=datetime.now(ZoneInfo('Europe/Stockholm')).isoformat()
report=f'''[{now}] CLEAR / OPEN: stable prefix and actual completed-head finalizer attachment.

Final documented source identities are stable-prefix {sha(stable)} (195 lines) and attachment {sha(attachment)} (203 lines). Both actual final strict checks pass with empty output, memory.max/high 4,294,967,296 bytes and swap.max 0. Removing only each inserted module documentation block recovers the previously checked proofs exactly: stable 168a87ad62cb933d730733ce6ec42db64945114c06462e7f7a015b06632a2fed and attachment v2 3104ea3c319b2c9723e42cf9622d10640f851cca7fa55542ec0e452abccfb9f5. The initial attachment v1 is retained as historical data.

Full old contract retention. The final stable-prefix theorem recovers the complete old PrefixResources theorem contract literally: {len(old_header):,} bytes / SHA256 {sha(old_header)}. The initial admission changes only the theorem name. The full old proof body recovers after the one added result goal, proof bullet and separator are removed. It makes the same two original traversal producer calls. The grouped existing Packet-to-actual-Trace observer is retained. The appended prefixResult is fixed before all extra-fuel quantifiers and can be a stopped rejection. This is not an unconditional completion assertion.

Attachment admission. completed_head_opaque_isolated consumes the original CompletedHeadReceipt at its literal caller, full Memos, captured cache and completed headCache. Its explicit additional gates are the actual edge constraint projection, a static child location in the generated child list, recursiveBoundary=true, and a bucket with no terminal trie. CompletedHeadReceipt already contains the derived stable completed-head family. No extra prefix success, suffix success, finalizer success, final isolation, or desired assignment is assumed. This is a local receipt consumer, not a bare-Packet completion producer.

Actual own allocation. The proof extracts the real stored ordinary parent, selected edge, original Ready and realized lookup. EdgeInputs.complete supplies the exact prepare action/own core, full cache invariants and genuine current children. own_prefix_packet derives the own Packet without changing caller, full Memos or metadata. The original edge reservation rewrites to the exact child-list cost. It is not replaced by a future reservation.

One sufficient common execution. The first observation at W=B+headBound fixes the completed consumed-prefix caller, queries and cache using prefixResult. Its actual Trace instantiates the returned PrefixAdmission, which supplies full event Memos/Packet, native Fits/guard carrier and the remaining original reservation. The opaque step has no native query effect, so reserving the suffix at that same event seed is valid. The old opaque suffix producer is invoked exactly once. Its full result packet includes native Post, exact query field, cache invariants, complete-or-rejection shape, resources and isolation.

The second observation at nextWork=B+headBound+(sr+sn+sp+sh+sk) is simultaneously sufficient for the original completed-head family, consumed-prefix family and suffix family. The fixed prefixResult aligns all four actual prefix fields. opaque_prepare_fuel applies only to recursive-boundary Mu/Union and shows the actual opaque cache is unchanged by the increased index fuel. The actual suffix Trace then aligns the suffix producer result at the same caller, queries and returned child cache. A canonical stopped suffix contradicts that observed complete Trace; no Safe property is asserted for rejection.

Final endpoint. The actual second decomposition supplies the real residual finish and parent finalizer into the original headCache. Ready.inside and own/prefix counter growth prove that the parent slot differs from the fresh opaque root. The existing finalizer law changes that different raw slot and ancestry; residual recording retains representatives and values. The suffix isolation law therefore applies to the SAME actual headCache. Native lookup at the SAME reached heap follows from the suffix Post.effects.keeps. Query equality is used only to align the actual execution query input; no full-Memos equality is inferred. Full event/suffix Memos remain their own actual producer witnesses.

Strongest current claim. Every original derived CompletedHeadReceipt with these actual projection/location/opaque gates has some held root and handle with lookupNode at its reached heap equal to this boundary value and IsolatedPending at its own completed headCache. The result does not establish attachment through later callbacks or recursive tails. It does not claim full output discharge, assignment acceptance, coverage, arbitrary low-fuel validity, or a Haskell defect. The new attachment is not a replacement for the old full resource packet; its narrower lookup/isolation conclusion is a new consumer theorem.

No source blocker found. Exact source/check copies and focused literal cuts are in source-index.json. attachment-comparison.json records comment-only mappings, literal full old contract recovery, one suffix call and actual checks. Earlier review evidence is preserved under review-revisions/pre-attachment. This bundle stays OPEN until Root supplies final installation/public/Audit evidence. No prior frozen area, repository source, Git, build, network or board write was used.
'''
save('report.txt',report.encode())
put_json('OPEN.json',{'status':'OPEN','reviewed_at':now,'review_result':'CLEAR','reason':'Wait for final installation/public/Audit as requested by parent.','reviewed_final_sources':[sha(stable),sha(attachment)],'publication_status':'not evaluated or predicted'})
print(json.dumps({'status':'CLEAR / OPEN','report_sha256':sha((OUT/'report.txt').read_bytes()),'source_index_sha256':sha((OUT/'source-index.json').read_bytes()),'whole_records':len(records),'literal_cuts':sum(len(r['cuts']) for r in records)},indent=2))
