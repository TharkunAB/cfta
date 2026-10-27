from pathlib import Path
import hashlib,json,datetime
R=Path('/tmp/mcfta-history-checked-origins-20261027/origin-checkpoint-review');A=R.parent
assert not (R/'FROZEN').exists()
def ident(b):return {'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def js(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
now=datetime.datetime.now().astimezone().isoformat()
report=f'''[{now}] CLEAR — final checked-arity origin checkpoint.

Source checkpoint6f380cee25b1d13caef617907264ecff1cb28c39. Reviewed all seven final sources,1158lines,36new public theorems/eight definitions. Current native source is197lines/a6fe378f59aae4192efc9173510d9d101d86d1e8a717ae8418028bd47c036892; actual-body source is158lines/105cbf646b39ef31aaf2e30b4fc71acebe940de9bf9d5789489e18171f9f1030. The whole source identities and precise literal cuts are in source-index.json. The earlier218line native variant is historical. Its unused Classical sentinel convenience wrapper was removed; the three retained public theorem blocks remain byte exact. No mathematical or current claim blocker found.

Strongest new result: initial physical Good, actual EdgeReady and the SAME rich completed physical body Receipt derive Fits of the actual returned edge. The postcondition parameter is arbitrary. The proof derives the actual ready/accepted observation or sentinel internally. It retains ordered raw child Walk/full constructor endpoint on acceptance, and actual first sentinel step/tail Trace/Top+Empty/full endpoint on rejection. Operations may change while the first native heap stays the same. No raw done is promoted to rich Trace. Rich Receipt already records actual physical Inputs and final Good. The result checks the returned edge; it does not classify every child-created edge record or whole native query.

The key-dependent Heap checks EVERY edgeRecords key at that key's own child count. It is distinct from the older guard-only annotation Heap and from Satisfies. Checked source syntax supplies the count relation explicitly. SourceChecked requires normalized Cached equalities AND the real source accepted Boolean at each original syntactic child count; it derives Fits rather than assuming projected arity as a new source fact. Raw build remains raw. Actual child lengths, constructor insertions, both binder probes, canonical hits, pending prefixes and stored encode/execute/unfold preserve this resource at their literal stopping states. Environment values do not allocate unchecked edges in this proof.

Actual allocated MkEdge and RejectReceipt preserve the ENTIRE Heap from their exact before to after. They take the genuine old receipt and initial Heap, derive requested-key/payload coherence and check the actual newly inserted key. They add no desired final Heap, extra Ready or future successful action. ParentEdge construction yields returned-edge arity, but its live MkEdge begins at the actual middle after local child reduction. The original Parent-before to middle invariant remains a separate gap. A generic Post/old-record Keeps plus returned-row Fits cannot check arbitrary new records.

The selected-head consumers preserve actual caller, native heap, full Memos, metadata, inventory and captured-cache parameters. One consumes genuine earlier Parent construction, returned heap equation, full retained Post and matching edge identity; current coherence derives full ordered record equality. The other consumes Heap at the SAME current head-input caller. Bare Packet does not supply this resource. No query equality is promoted to full Memos equality.

accepted_body_produced calls its original body_produced ONCE. The ENTIRE2501B old admission/result is recovered literally by only reversing the theorem name, explicit native State qualification and the final appended Fits field. SHA f451a351efe91d40fb4d086b53f7ff783035198b56c1ecd6e95a3bb19f08d081. Its original actual semantic child Walk admission stays explicit. accepted_receipt_fits instead extracts an actual raw child Walk from the same physical Receipt and real ready branch; it does not supply an arbitrary future semantic child result.

All seven final strict sources match installed bytes; each final module check passes with empty raw output, all warnings/linters fatal, actual memory.max/high4GiB and swap0. Aggregate Audit PASS4167jobs/79583dependencies; standalone strict Audit PASS56B. Public final108304B SHA4af04f90177cd45d423b0482336b04e93e62e374f72d3bdc4b4f2d99afc44c49 read WHOLE in contiguous chunks1–430,431–850,851–1260,1261–1661. It contains42complete theorem signature/axiom blocks (36new), eight printed definition declarations and only propext/Classical.choice/Quot.sound. The generated mutual definition declarations use their printed brecOn helpers; source mutual equations were also read. All six prior full public blocks and prior source identities match exactly. The aggregate's pre-existing unused-variable replay warning is retained. All actual failed strict attempts/source variants remain preserved and are not counted as passes. Review capture v1 stopped on an oversized cut boundary; its script and explicit correction to actual109line CheckedSyntax source are preserved separately. This was an evidence-capture failure, not a Lean check.

Read the WHOLE final13983B note lean/notes-current-checked-arity-origins.md SHA128d83304e09f3a7d48c77f9b317e5ba68e649643dda5e1647d6222c7e3b247c, plus all nine exact inserted status regions. Eight status regions are identical; FINDINGS contains that same region plus its explicit constructor/Haskell boundary. Removing each insertion recovers prior bytes literally. Historical document bodies were not reread or mislabeled as whole-source snapshots. Current claims state all genuine source checks, rich receipt gates and remaining query/local-reduction/cache/exposure/history resource gaps. No new Haskell source or test result is claimed. The separate KBO candidate remains source-assessed and unintegrated; no new Haskell defect follows from this Lean boundary.

The existing conditional ResourceHistoryWithArity acceptance observer remains unchanged. This checkpoint does NOT derive arity-certified histories from the bare finite producer, universal Ranges, unconditional whole enumerator acceptance/coverage, convergence, or physical Haskell correctness. Full native query creation and actual sibling/callback/recursive resource propagation remain next work. H6 remains the old strongest global finite-tree construction theorem. Source/public/source-validation/document receipts support this exact scope.

Publication condition: this report and all live preflight checks must exist before the immutable checkpoint archive is created. Frozen-byte portable verification and committed-byte verification must then pass before publication. This review does not claim those future archive/commit/push steps have already run.

CLEAR / FROZEN for this bounded final source/public/docs review. All whole identities/cuts/actual checks are sealed. No repo edit, build, Lean execution, Git, network or board action was performed by this reviewer. Previous frozen areas remain untouched. No further writes to this review bundle after its seal.
'''
(R/'report.txt').write_text(report)
idx=json.loads((R/'source-index.json').read_text());checks=0
for rec in idx['sources']:
 original=Path(rec['source']).read_bytes();assert ident(original)=={k:rec[k] for k in ['bytes','sha256']};checks+=1
 if 'snapshot' in rec:assert Path(rec['snapshot']).read_bytes()==original;checks+=1
 for c in rec['cuts']:
  b=b''.join(original.splitlines(keepends=True)[c['first_line']-1:c['last_line']]);assert ident(b)=={k:c[k] for k in ['bytes','sha256']};assert Path(c['snapshot']).read_bytes()==b;checks+=1
for x in json.loads((R/'document-inverses.json').read_text())['nine_exact_inverses']:
 b=Path(x['source']).read_bytes();o,n=x['offset'],x['removed_bytes'];assert b[:o]+b[o+n:]==Path(x['prior_source']).read_bytes();checks+=1
# Reconfirm all recorded raw outputs against the exact actual report records.
for s in json.loads((R/'strict-attempts.json').read_text()):
 report=json.loads((R/'actual-checks'/s['check']/'report.json').read_text());b=(R/'actual-checks'/s['check']/'raw.log').read_bytes();assert ident(b)=={k:report[k] for k in ['bytes','sha256']};checks+=1
(R/'OPEN.json').rename(R/'historical-OPEN.json')
js(R/'verification-final.json',{'status':'pass','checked_at':now,'source_records':len(idx['sources']),'literal_cuts':sum(len(s['cuts']) for s in idx['sources']),'byte_checks':checks,'entire_old_body_contract':True,'six_old_signature_blocks_byte_exact':True,'nine_document_inverses':True,'scope':'final source/public/current documentation; future archive/publication checks not claimed'})
files={str(p.relative_to(R)):ident(p.read_bytes()) for p in sorted(R.rglob('*')) if p.is_file() and p.name not in ['pins.json','FROZEN']}
js(R/'pins.json',{'schema':'exact whole payload files','files':files})
seal={'status':'CLEAR / FROZEN','frozen_at':now,'payload_count':len(files),'exact_file_count':len(files)+2,'pins_bytes':(R/'pins.json').stat().st_size,'pins_sha256':ident((R/'pins.json').read_bytes())['sha256'],'report_sha256':ident((R/'report.txt').read_bytes())['sha256'],'source_index_sha256':ident((R/'source-index.json').read_bytes())['sha256'],'source_records':len(idx['sources']),'literal_cuts':sum(len(s['cuts']) for s in idx['sources']),'byte_checks':checks,'source_head':'6f380cee25b1d13caef617907264ecff1cb28c39','new_sources':7,'new_source_lines':1158,'new_theorems':36,'printed_definitions':8,'public_signatures':42,'scope':'final seven-source/public/docs claim review; archive publication verification remains Root next step'}
js(R/'FROZEN',seal)
print(json.dumps({**seal,'FROZEN_sha256':ident((R/'FROZEN').read_bytes())['sha256']},indent=2))
