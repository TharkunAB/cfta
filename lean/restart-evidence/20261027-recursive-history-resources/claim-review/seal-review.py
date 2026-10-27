from pathlib import Path
import json,hashlib,re,datetime,difflib
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-recursive-history-resources-20261027');out=area/'claim-review';assert not(out/'FROZEN.json').exists()
def sha(b):return hashlib.sha256(b).hexdigest()
def put(rel,b):
 p=out/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b if isinstance(b,bytes) else b.encode());return p
state=json.loads((out/'review-state.json').read_text());sources=state['sources'];cuts=state['cuts'];evidence=state['evidence']
def evidence_file(p,rel=None):
 b=p.read_bytes();snap=rel or f'evidence/{p.relative_to(area)}';put(snap,b);evidence.append({'path':str(p),'source':str(p),'snapshot':snap,'bytes':len(b),'sha256':sha(b)})
def whole(p,snap,scope):
 b=p.read_bytes();put(snap,b);sources.append({'path':str(p),'source':str(p),'snapshot':snap,'bytes':len(b),'sha256':sha(b),'read_scope':scope})
def literal_cut(p,a,z,snap):
 b=p.read_bytes();assert 1<=a<=z<=len(b.splitlines());cut=b''.join(b.splitlines(True)[a-1:z]);put(snap,cut);cuts.append({'path':str(p),'source':str(p),'snapshot':snap,'start':a,'end':z,'source_sha256':sha(b),'bytes':len(cut),'sha256':sha(cut)})
# Final authoritative validators and actual reports. No check is rerun.
for name in ['modules.json','document-validation.json','public-validation.json','source-validation.json','native-summary.json','public-declarations.json','public-definitions.json','strict-checks.json']:
 evidence_file(area/name)
assert len(json.loads((area/'modules.json').read_text()))==18
native=json.loads((area/'native-summary.json').read_text());assert native['status']=='pass';assert native['large_generated_overflow'].startswith('unexecuted')
report_dirs=['strict-audit-final-1','public-readback-final-1']+[c['name'] for c in native['checks']]
for d in report_dirs:
 p=area/d;report=json.loads((p/'report.json').read_text());raw=(p/'raw.log').read_bytes();assert len(raw)==report['bytes'] and sha(raw)==report['sha256']
 assert report['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 for n in ['report.json','raw.log']:evidence_file(p/n)
 if d.startswith('strict-audit'):
  b=(p/'MicroCFTA/Audit.lean').read_bytes();assert sha(b)==report['source_sha256'];assert b==(root/'lean/MicroCFTA/Audit.lean').read_bytes()
 if d=='public-readback-final-1':
  evidence_file(p/'public.lean');assert sha((p/'public.lean').read_bytes())==report['source_sha256']
  assert report['exit_code']==0
for c in native['checks']:
 assert c=={'name':c['name'],**json.loads((area/c['name']/'report.json').read_text())}
# Exact full old theorem + axiom blocks remain equal, without reusing a Boolean result alone.
evidence_file(area/'prior-public-readback/raw.log')
raw=(area/'public-readback-final-1/raw.log').read_text();prior=(area/'prior-public-readback/raw.log').read_text();pv=json.loads((area/'public-validation.json').read_text())
assert len(raw.encode())==pv['bytes']==283619 and sha(raw.encode())==pv['sha256']=='c6025b59b1cb093fbb72febe79b522d7479085ebf2d42ee172007e11bec10cc8'
assert all(x not in raw for x in ['⋯','...','sorryAx'])
ns=json.loads((area/'public-declarations.json').read_text());defs=json.loads((area/'public-definitions.json').read_text());pub=(area/'public-readback-final-1/public.lean').read_text()
assert len(ns)==34 and len(defs)==5 and len(re.findall(r'^#check ',pub,re.M))==34 and len(re.findall(r'^#print axioms ',pub,re.M))==34
sets=re.findall(r'depends on axioms:\s*\[([^]]*)\]',raw,re.S);assert len(sets)==34
used={a.strip() for group in sets for a in group.split(',')};assert used=={'propext','Classical.choice','Quot.sound'}
def block(text,n):
 a=text.index('MicroCFTA.'+n);z=text.index(']',text.index('depends on axioms:',a))+1;return text[a:z]
blocks=[]
for i,n in enumerate(ns[-3:]):
 old=block(prior,n);new=block(raw,n);assert old==new;put(f'public-regions/prior-{i+1}.txt',old);put(f'public-regions/current-{i+1}.txt',new);blocks.append({'name':n,'bytes':len(new.encode()),'sha256':sha(new.encode()),'full_signature_and_axiom_block_identical':True})
for n in ['SourcePruningEnumerationRecursive.finite_history_complete','SourcePruningEnumerationRecursive.run_finite_complete_resources_with_history','SourcePruningEnumerationRecursive.ResourceHistory.isolated_boundary','SourcePruningEnumerationRecursive.run_finite_complete_resources_isolated']:
 put('public-regions/'+n.split('.')[-1]+'.txt',block(raw,n))
put('public-region-comparison.json',json.dumps({'status':'PASS','all34_axiom_reports':34,'axioms':sorted(used),'old_blocks':blocks,'scope':'complete selected proof interfaces and old blocks; other repeated large packets checked by source identity/readback counts rather than reread in full'},indent=2)+'\n')
# Literal inserted regions only. Historical bodies are compared byte-for-byte, not copied again.
rows=json.loads((area/'document-validation.json').read_text());preservation=[];common=None
for r in rows:
 p=root/r['path'];b=p.read_bytes();assert len(b)==r['bytes'] and sha(b)==r['sha256']
 if 'offset' in r:
  off=r['offset'];size=r['inserted_bytes'];c=b[off:off+size]
  if common is None:common=c
  assert len(common)==1787 and c.startswith(common)
  oldpath=area/'prior-documents'/r['path'];old=oldpath.read_bytes();assert old==b[:off]+b[off+size:]
  snap=f'document-regions/{r["path"]}';put(snap,c)
  start=b[:off].count(b'\n')+1;end=start+c.count(b'\n')-1
  assert b''.join(b.splitlines(True)[start-1:end])==c
  cuts.append({'path':str(p),'source':str(p),'snapshot':snap,'start':start,'end':end,'source_sha256':sha(b),'bytes':len(c),'sha256':sha(c)})
  preservation.append({'path':str(p),'source_sha256':sha(b),'bytes':len(b),'offset':off,'inserted_bytes':size,'inserted_sha256':sha(c),'baseline_source':str(oldpath),'baseline_bytes':len(old),'baseline_sha256':sha(old),'removed_insert_equals_baseline':True,'read_scope':'inserted region only; historical body byte comparison, no prose reread or whole copy'})
 else:
  whole(p,f'inputs/{r["path"]}','whole final corrected current note')
assert len(preservation)==9 and all(x['inserted_sha256']==sha(common) for x in preservation if not x['path'].endswith('FINDINGS.md'))
assert next(x for x in preservation if x['path'].endswith('FINDINGS.md'))['inserted_bytes']==3555
put('document-preservation.json',json.dumps({'status':'PASS','common_prefix_bytes':len(common),'common_prefix_sha256':sha(common),'nine_identical_common_prefixes':True,'documents':preservation},indent=2)+'\n')
# Retain the one reviewed prose correction without labeling reconstructed bytes as a fresh readback.
note=root/'lean/notes-current-recursive-history-resources.md';new=note.read_text();fixed='Finalizer preservation is an output conditional on its actual success.';old='Conditional finalizer success is a conclusion, not an admission.'
assert new.count(fixed)==1 and old not in new
initial=new.replace(fixed,old);assert len(initial.encode())==15061 and sha(initial.encode())=='17fa96abf8513259e00a9d32449faa761f8a1de1b9f64c9af772b476c785e080'
put('revisions/reviewed-note-before-precision.md',initial);put('revisions/note-precision.diff',''.join(difflib.unified_diff(initial.splitlines(True),new.splitlines(True),fromfile='reviewed-initial-note',tofile='final-corrected-note')))
put('revisions/note-correction-provenance.json',json.dumps({'initial_sha256':sha(initial.encode()),'final_sha256':sha(new.encode()),'initial_preservation':'reconstructed from the announced unique literal replacement; hash matches the initially read note/document-validation identity','correction':'Clarify conditional preservation output; no finalizer success theorem is claimed.','theorem_sources_changed':False},indent=2)+'\n')
# Native primary code and source cuts supporting the limited witness claims.
w=area/'upstream-kbo-review/witness/kbo-int-weights.hs';whole(w,'inputs/upstream-kbo-witness.hs','whole actual witness source; actual run reports/logs preserved, not re-executed')
for rel,scope,spans in [('specftacular/test/Golden.hs','six cases, both check modes and execution settings; lines1-161 read',[(29,127),(142,158)]),('specftacular/src/Specftacular/Rewriting.hs','public order type, actual rewriting order check, Int weight and recurrence/comparator blocks only',[(145,169),(272,312),(658,684),(698,742)])]:
 p=root/rel;whole(p,'inputs/'+rel,scope)
 for a,z in spans:literal_cut(p,a,z,'native-cuts/'+p.stem+f'.{a}-{z}.hs')
# The source statistics use exact line and public-declaration counts.
modules=json.loads((out/'review-modules.json').read_text());count_lines=count_theorems=count_data=0
for n in modules:
 b=(root/'lean/MicroCFTA'/f'{n}.lean').read_bytes();s=b.decode();count_lines+=len(s.splitlines());count_theorems+=len(re.findall(r'^theorem ',s,re.M));count_data+=len(re.findall(r'^(?:def|inductive|structure) ',s,re.M));assert not re.search(r'\b(?:sorry|admit|native_decide|axiom)\b',s);assert 'set_option' not in s
assert (len(modules),count_lines,count_theorems,count_data)==(18,3226,31,5)
put('final-statistics.json',json.dumps({'status':'PASS','modules':18,'lines':3226,'new_public_theorems':31,'new_data_declarations':5,'aggregate_jobs':4139,'theorem_dependencies':79423,'source_strict_zero_output':18,'strict_audit_output_bytes':56,'public_signatures_including_3_old':34,'public_data_declarations':5,'public_readback_bytes':283619,'public_readback_sha256':sha(raw.encode()),'final_note_bytes':len(new.encode()),'final_note_sha256':sha(new.encode()),'new_proof_source_forbidden_tokens_absent':True},indent=2)+'\n')
# A concise claim verdict distinguishes completed operational composition from open semantics.
report='''CLEAR — Final recursive-history-resources checkpoint claim review

The eighteen exact checked modules support the corrected current note and all nine inserted status regions. Original resource admission now derives one sufficient work bound, a stable actual finite-depth result, the full prior OutcomeResources, and ResourceHistory for each emitted output at that same bound+extra. finite_history_complete closes the stronger induction from depth zero. The public producer has no remaining Complete/CompleteWithHistory premise. Original Packet, full Memos, Fits, guard carrier, mass/reservation and actual selector contracts remain. Histories may vary with extra fuel; no fixed universal trace is claimed.

Ordinary histories retain actual prefix execution and PrefixValid, the actual entry singleton, the same entered captured cache, aggregate Post/full local Memos, actual invocation/head completion, full returned Memos and CompletedHeadReceipt, original/updated callback admission, actual false recording and smaller-depth tail. Local head bounds and callback seed/mass ceilings remain attached to their own actual endpoints. The next sibling uses the actual post-hook caller and full Memos, while its captured enumeration input is restored. No equality of full memo tables is inferred from equal query projections. Empty/rejected/unsupported/stuck branches keep exact observations. Outputs emitted before a later stop retain their own histories; no Safe guarantee for the current rejected/stopped cache is added.

ResourceHistory.isolated_boundary requires the ACTUAL restart decision, an ORIGINAL IsolatedPending marker, its decoded native handle and recursiveBoundary fact. It derives that the marker differs from any selected target and transports isolation/decode through the same actual prefixes, ordinary entry, completed heads and either callback result. The finite corollary invokes the genuine resource producer once and retains its entire packet. Its grouped old history forall lies outside the appended isolation conclusion; a literal old-producer projection comparison is retained. Every emitted output still contains the original marker and cannot be fully Discharged. This does not remove runtime outputs or establish rendering failure for an unrelated root. Local creation/opaque-suffix results do not yet attach every inside-head created marker to the remaining ResourceHistory.

The final note correctly leaves Canonical/fresh-arity/retention gates, backward assignment composition, recursive rendering acceptance, coverage and physical Haskell correspondence open. Existing Packet carries Stratified order but no Canonical or backward semantic history. H6 remains the strongest global exact construction theorem. Full H6 and both captured-renderer signature-plus-axiom blocks compare byte-for-byte with the preserved prior readback. The eighteen proof additions do not claim stronger global language semantics or a CFTA runtime repair.

Evidence matches: eighteen source strict checks pass with literal empty logs; strict Audit passes with its 56-byte informational dependency line. Aggregate build passes 4139 jobs/79423 dependencies and replays one unchanged older unused-input warning. Installed readback is 283619 bytes, SHA c6025b59b1cb093fbb72febe79b522d7479085ebf2d42ee172007e11bec10cc8: 34 full signatures (31 new plus 3 old), five data declarations, no elision, and only propext/Classical.choice/Quot.sound. Source totals are 3226 lines. Counts, raw hashes and actual immutable source inputs were checked without running a compiler.

Native claims stay bounded. The actual public nonnegative Int-map witness reports a>b but app c a<app c b and accepts a local contextual rewrite. It refutes unrestricted context closure, not equation truth, a rewrite cycle, or default generated-overflow execution. computed 8 only reports the small 1,3,...,511 recurrence. Large generated overflow remains unexecuted. The six golden signatures run in both modes and pass after an explicit existing GMP library path fixes the first linker failure; the first witness attempt failed due hidden packages and its corrected attempt passed. Reports retain these failures. Tests do not certify formal source correspondence. Imported Specftacular code is a separate upstream scope.

The sole prose issue was corrected: finalizer PRESERVATION is an output conditional on actual success; finalizer success itself is not proved. The final note is pinned; the initially reviewed wording and exact directional correction are retained separately. All nine historical status-document bodies are byte-identical after removing their exact inserted regions. Their prose was not reread or copied wholesale. Prior frozen bundles remain untouched. Fourteen new-source reads reuse prior exact sealed identities; the remaining new sources and crucial current contracts were read directly. Public-readback counts/all axiom reports and selected complete interfaces were checked; repeated large old packets were not all independently reread. Native source review is limited to the named literal spans. All read scopes are explicit. This review used no build, compiler, Git, network, board or repository mutation.
'''
put('report.txt',report)
# Archive initial OPEN state unchanged. This final index is authoritative.
final={'version':1,'status':'CLEAR','sources':sources,'cuts':cuts,'evidence':evidence,'documentation_preservation':'document-preservation.json','public_preservation':'public-region-comparison.json','statistics':'final-statistics.json','source_commit':'324a2c527e003fc5c19ce4332b4c4b1ac53254d2','pending':[],'scope':'TEMP-only source/data claim review; no compiler/build/Git/network/repository mutation'}
put('source-pins.json',json.dumps(final,indent=2)+'\n')
for x in sources+cuts+evidence:
 b=(out/x['snapshot']).read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256']
 if x in cuts:
  live=Path(x['source']).read_bytes();assert sha(live)==x['source_sha256'];assert b''.join(live.splitlines(True)[x['start']-1:x['end']])==b
 else:assert Path(x['source']).read_bytes()==b
files={str(p.relative_to(out)):{'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())} for p in sorted(out.rglob('*')) if p.is_file() and p not in [out/'pins.json',out/'FROZEN.json']}
put('pins.json',json.dumps({'version':1,'files':files},indent=2)+'\n')
frozen={'version':1,'status':'FROZEN','created':datetime.datetime.now().astimezone().isoformat(),'payload_count':len(files),'pins_count':len(files),'exact_file_count':len(files)+2,'pins_bytes':(out/'pins.json').stat().st_size,'pins_sha256':sha((out/'pins.json').read_bytes()),'report_sha256':sha((out/'report.txt').read_bytes()),'source_index_sha256':sha((out/'source-pins.json').read_bytes()),'source_count':len(sources),'cut_count':len(cuts),'cut_lines':sum(x['end']-x['start']+1 for x in cuts),'reviewed_modules':18,'strict_source_successes':18,'source_commit':final['source_commit'],'final_note_sha256':sha(new.encode())}
put('FROZEN.json',json.dumps(frozen,indent=2)+'\n');assert len([p for p in out.rglob('*') if p.is_file()])==len(files)+2
print(json.dumps({'directory':str(out),**frozen,'FROZEN_sha256':sha((out/'FROZEN.json').read_bytes())},indent=2))
