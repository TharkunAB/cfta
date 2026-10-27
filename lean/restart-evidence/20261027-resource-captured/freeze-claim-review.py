from pathlib import Path
from datetime import datetime
import json,hashlib,re,difflib
repo=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-resource-captured-20261027');out=area/'claim-review';assert not (out/'FROZEN.json').exists()
def sha(b):return hashlib.sha256(b).hexdigest()
def put(rel,b):
 p=out/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
def dump(rel,o):put(rel,(json.dumps(o,indent=2,ensure_ascii=False)+'\n').encode())
def pin(p,rel,role,scope):
 b=p.read_bytes();put(rel,b);return dict(path=str(p),source=str(p),snapshot=rel,bytes=len(b),sha256=sha(b),role=role,read_scope=scope)
sources=[];cuts=[];docs=[];evidence=[];checked=[]
mods=json.loads((area/'modules.json').read_text());checks=json.loads((area/'strict-checks.json').read_text());assert len(mods)==8 and len(checks)==9
for name in mods:
 p=repo/'lean/MicroCFTA'/(name+'.lean');b=p.read_bytes();folder=area/checks[name];r=json.loads((folder/'report.json').read_text());raw=(folder/'raw.log').read_bytes()
 assert r['exit_code']==0 and r['source_sha256']==sha(b) and raw==b'' and r['sha256']==sha(raw)
 assert (folder/'MicroCFTA'/p.name).read_bytes()==b
 assert '-DwarningAsError=true' in r['command'] and '-Dlinter.all=true' in r['command']
 sources.append(pin(p,'inputs/lean/MicroCFTA/'+p.name,'new installed theorem module','public statement and relevant proof route reviewed; prior unchanged draft/proof comparisons reused'))
 checked.append(dict(module=name,strict=checks[name],sha256=sha(b),exact_input=True,raw_empty=True))
 lines=b.splitlines(keepends=True);start=next(i for i,l in enumerate(lines) if l.startswith(b'theorem '));end=start
 while b':=' not in lines[end]:end+=1
 part=b''.join(lines[start:end+1]);rel=f'cuts/{name}--public-contract.lean';put(rel,part)
 cuts.append(dict(path=str(p),source=str(p),snapshot=rel,start=start+1,end=end+1,source_sha256=sha(b),bytes=len(part),sha256=sha(part)))
assert sum(x['bytes'] for x in sources)>0
assert sum(len((repo/'lean/MicroCFTA'/(n+'.lean')).read_bytes().splitlines()) for n in mods)==1194
for name,expected in [('SourceCurrentColdFiniteWarmCalls','e4665b0bb522ec88f1925fe6bc360b76e9e4bdfbe6192210ac708a3097a20cc5'),('SourcePruningEnumerationCapturedRendering','18a81a7cdf0b208021f9ad5097e616270ad6001dbc75b08a7901352d5e174386')]:
 p=repo/'lean/MicroCFTA'/(name+'.lean');assert sha(p.read_bytes())==expected
 sources.append(pin(p,'inputs/lean/MicroCFTA/'+p.name,'unchanged global source','whole-file identity; no new global proof claim'))
metadata=json.loads((area/'document-validation.json').read_text());common=None;newNote=None;oldmeta=[]
for d in metadata:
 p=repo/d['path'];b=p.read_bytes();assert len(b)==d['bytes'] and sha(b)==d['sha256']
 if 'offset' in d:
  start=d['offset'];end=start+d['inserted_bytes'];part=b[start:end]
  if common is None:common=part
  assert part==common and len(part)==1597
  prior=area/'prior-documents'/d['path'];baseline=prior.read_bytes();assert b[:start]+b[end:]==baseline
  rel='documents/prefixes/'+d['path'];put(rel,part)
  docs.append(dict(path=str(p),source=str(p),snapshot=rel,source_bytes=len(b),source_sha256=sha(b),byte_start=start,byte_end_exclusive=end,bytes=len(part),sha256=sha(part),read_scope='literal inserted region only; historical prose not reread',prior_source=str(prior),prior_sha256=sha(baseline),prior_bytes=len(baseline),removal_exact=True))
 else:
  newNote=b;assert sha(b)=='209c3d6ed528464f4b908050d8074f0c97c0f973c03b44de9b60270f76b68b18'
  docs.append(pin(p,'documents/'+d['path'],'corrected final note','whole initial and corrected note reviewed'))
assert len(docs)==10
put('documents/common-prefix.md',common)
# Recover the exact initially reviewed prose from the corrected copy and verify its already observed hash.
a=b"derived from original finite resource admission. Original Stratified dependency\norder, discharge, actual rendering at that receipt's reached heap and successful\nchecks of its returned residuals\n"
b=b"derived from original finite resource admission. Discharge, actual rendering\nat that receipt's reached heap and successful checks of its returned residuals\n"
c=b"original Stratified dependency order, Discharged, ACTUAL flat rendering at that\nsame reached heap and checks of every actual returned residual. The original\norder is an explicit premise. The completion packet transports that order.\nrender_assignment constructs the assignment at the\n"
d=b"Discharged, ACTUAL flat rendering at that same reached heap and checks of every\nactual returned residual. render_assignment constructs the assignment at the\n"
assert newNote.count(a)==newNote.count(c)==1
oldNote=newNote.replace(a,b).replace(c,d);assert len(oldNote)==11658 and sha(oldNote)=='05bddc58c92baf9291e7209713282f651ed0217a6a754ecb6dbdbc347e9272ed'
pnew=b'Original Stratified dependency order, discharge, actual rendering and checked\nresiduals construct an assignment and prove acceptance at the original captured\nedge and parent. No desired\n'
pold=b'Discharge, actual rendering and checked residuals construct an assignment and\nprove acceptance at the original captured edge and parent. No desired\n'
assert common.count(pnew)==1
oldPrefix=common.replace(pnew,pold);assert len(oldPrefix)==1559
put('provenance/pre-order-clarification/note.md',oldNote);put('provenance/pre-order-clarification/prefix.md',oldPrefix)
put('provenance/order-clarified-note.md',newNote);put('provenance/order-clarified-prefix.md',common)
for label,old,new in [('note',oldNote,newNote),('prefix',oldPrefix,common)]:
 forward=''.join(difflib.unified_diff(old.decode().splitlines(keepends=True),new.decode().splitlines(keepends=True),fromfile='before/'+label,tofile='after/'+label))
 inverse=''.join(difflib.unified_diff(new.decode().splitlines(keepends=True),old.decode().splitlines(keepends=True),fromfile='after/'+label,tofile='before/'+label))
 put('provenance/'+label+'-forward.patch',forward.encode());put('provenance/'+label+'-inverse.patch',inverse.encode())
dump('provenance/correction.json',dict(status='resolved before final freeze',issue='initial Stratified dependency-order premise omitted from strongest prose and common prefix',source='lean/MicroCFTA/SourceFlatPruningCapturedResourceRendering.lean',old_note_sha256=sha(oldNote),new_note_sha256=sha(newNote),old_prefix_sha256=sha(oldPrefix),new_prefix_sha256=sha(common),preservation_method='exact inverse of the two note substitutions and one prefix substitution; reconstructed initial note matches the SHA256 recorded during its whole initial reading',theorem_sources_unchanged=True))
# Compare all four earlier public signatures against the preserved local previous readback.
current=(area/'public-readback-final/raw.log').read_bytes();previous=(area/'prior-public-readback/raw.log').read_bytes()
public=json.loads((area/'public-validation.json').read_text());assert public['status']=='pass' and public['no_elision'] and public['bytes']==len(current) and public['sha256']==sha(current)
assert set(public['axioms'])=={'propext','Classical.choice','Quot.sound'} and public['theorem_signatures_and_axiom_checks']==12 and public['definitions']==0
priorChecks=[]
def extract(raw,name):
 text=raw.decode();fq='MicroCFTA.'+name;match=re.search('^'+re.escape(fq)+r'(?=\s|$)',text,re.M);assert match,name
 ax=text.index("'"+fq+"' depends on axioms:",match.start());return text[match.start():ax].encode()
for name in public['unchanged_prior_signatures']:
 old=extract(previous,name);new=extract(current,name);assert old==new,name
 rel='public-contracts/'+name+'.txt';put(rel,new)
 priorChecks.append(dict(declaration=name,signature_snapshot=rel,bytes=len(new),sha256=sha(new),byte_identical=True,old_log_sha256=sha(previous),current_log_sha256=sha(current)))
assert len(priorChecks)==4
dump('prior-signature-comparison.json',dict(status='pass',baseline=str(area/'prior-public-readback/raw.log'),signatures=priorChecks))
renderName='SourceFlatPruningCapturedEdge.render_sound_current_resources';render=extract(current,renderName).decode()
for term in ['Stratified','Discharged','Canonical','freshArity','retained','pendingResiduals']:
 assert term in render,term
for folder in checks.values():
 report=json.loads((area/folder/'report.json').read_text());raw=(area/folder/'raw.log').read_bytes();assert report['exit_code']==0 and report['bytes']==len(raw) and report['sha256']==sha(raw)
 assert report['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 for n in ['report.json','raw.log']:evidence.append(pin(area/folder/n,'evidence/'+folder+'/'+n,'actual strict evidence','report/source/raw and effective memory-limit validation'))
for folder in ['build-aggregate-final','public-readback-final']:
 r=json.loads((area/folder/'report.json').read_text());raw=(area/folder/'raw.log').read_bytes();assert r['exit_code']==0 and r['bytes']==len(raw) and r['sha256']==sha(raw)
 for n in ['report.json','raw.log']:evidence.append(pin(area/folder/n,'evidence/'+folder+'/'+n,'actual aggregate or installed evidence','report and structural validation; public eight current/four prior contracts correlated, no claim of manually rereading every expanded byte'))
for folder in ['public-readback-final','prior-public-readback']:
 for n in ['public.lean','raw.log','report.json']:
  p=area/folder/n
  if p.exists() and not any(e['source']==str(p) for e in evidence):evidence.append(pin(p,'evidence/'+folder+'/'+n,'actual public request or preserved baseline','full request and exact previous-signature comparison'))
for n in ['modules.json','strict-checks.json','source-validation.json','public-validation.json','public-declarations.json','public-definitions.json','source-commits.json','source-head.txt','document-validation.json','document-paths.json']:
 p=area/n;evidence.append(pin(p,'evidence/'+n,'current checkpoint control','actual control correlated with pinned sources and outputs'))
aggregate=(area/'build-aggregate-final/raw.log').read_text();assert '4087' in aggregate and '79148' in aggregate
now=datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
report=f'''[{now}] FINAL CLEAR after one prose correction. Independent claim review of source head c4c12f9f7acef2bb76fd01c3f1920b64b23bbbd9.

The initial strongest rendering claim omitted original Stratified dependency order. The actual theorem requires it separately from resource admission. Root corrected both note passages and all nine common prefixes before this freeze. The final note is 11822 bytes with SHA256 209c3d6ed528464f4b908050d8074f0c97c0f973c03b44de9b60270f76b68b18. It now says initial order is an explicit premise and completion only transports that order. No theorem changed. The exact initial note is preserved with its previously observed SHA256, the corrected copies, and forward/inverse textual deltas. No unresolved claim issue remains.

The new local result concerns one actual completed captured step. Original Context/Ready, actual stored and decoded parent, realization, selected membership, native indexes, pending inputs, allowed/projected arity and seed/Fits/original reservation/carrier give a sufficient work bound before any related flat input. An actual complete receipt at that bound identifies the same old completed result and related exact endpoint. Canonical, inherited nonterminal shape, fresh projected arity and per-child retention remain explicit language gates. The bound does not force completion instead of a valid stopping result.

The neutral selected/captured proof retains its old backward conclusion. Own suspension preserves the held captured payload; child Protects carries it to the actual middle cache. Finalize writes the same produced fragment at that middle cache and reached heap. Its fragment equation and neutral semantics restore the original pending native handle and suspended restrictions. Common sums and maxima identify actual result/cache/Caller/query fields. Full Memos stay with the actual Post witness; query equality is not used to invent equality of full memo tables. Rejection is not assigned Safe or accepted-fragment semantics.

Traversal resources retain the entire original packet, including history and final Fits/carrier, and append the exact completed-result assignment iff. The neutral resource induction derives current head ranges from original resources at actual reached states and threads Post/full Memos, Safe, realization, Fits and the remaining reservation to the suffix. Its reservation counts each bucket length plus one and retains duplicate occurrences. It does not assume universal future ranges or successful subcalls as original admission.

The rendering consumer additionally requires original Stratified dependency order, reached-cache Discharged, actual flat rendering at that receipt's own reached native heap, and semantic checks of every returned residual. It constructs an assignment; it assumes neither desired Satisfies nor old rendering success. It proves acceptance by the original captured edge and parent, original/completed/rendered state satisfaction, the exact fragment/term equation and unchanged rendered flat core. These are conditional single-step results. Whole recursive-input acceptance, pruning coverage and parked-constraint recovery remain open. Done does not imply Discharged, and physical union-find/container or machine bounds are not inferred from Related.

The corrected note was read whole and the nine corrected 1597-byte inserted regions were read. They are identical. Removing each region exactly reproduces its preserved prior document bytes. Historical document prose was not reread or copied. The note and common prefix now state the necessary local conditions and retain the unchanged global H6, full-recursion, semantic-history and Haskell correspondence limits. They make no new Haskell-defect or native-test claim.

All eight installed module identities match their passing strict snapshots and literal empty raw logs. The sources contain 1194 lines and eight public theorems. Nine strict checks include Audit; actual aggregate evidence records 4087 jobs and 79148 dependency checks, with the inherited unused-input warning preserved. Installed readback is 99843 bytes, SHA256 0d07920c193e527081e8630e4cdbe302eb8f5ea3d51fca531ba07d6c1f420579. It covers 12 full signatures/axiom lists and no runtime definitions. Four earlier signatures were independently compared byte-for-byte with the preserved local previous readback, including same-line binders. All four match. The only reported axioms are propext, Classical.choice and Quot.sound, with no elision. Source contracts and relevant expanded signature gates were correlated; no separate manual reading of every expanded-output byte is claimed. No check was rerun by this reviewer.

H6 source remains e4665b0bb522ec88f1925fe6bc360b76e9e4bdfbe6192210ac708a3097a20cc5. CapturedRendering remains 18a81a7cdf0b208021f9ad5097e616270ad6001dbc75b08a7901352d5e174386. The note's verification totals match actual reports. This review changes only its temporary bundle and preserves every earlier frozen bundle. It infers no future archive, seal or publication.
'''
put('report.txt',report.encode())
dump('validation.json',dict(status='pass',strict_sources=checked,new_source_lines=1194,new_public_theorems=8,strict_checks=9,old_signatures_exact=4,identical_prefixes=9,prefix_removal_exact=True,order_omission_resolved=True,new_note_sha256=sha(newNote)))
dump('source-pins.json',dict(version=1,status='FINAL CLEAR',observed_at=now,sources=sources,cuts=cuts,documents=docs,evidence=evidence,correction='provenance/correction.json',public_signature_comparison='prior-signature-comparison.json',read_scope='eight current theorem contracts and relevant proof routes; initial/corrected whole note and common status regions; exact final/previous public signature correlation; evidence as labeled'))
for record in sources+evidence:
 b=Path(record['source']).read_bytes();assert sha(b)==record['sha256'] and (out/record['snapshot']).read_bytes()==b
entries=[]
for p in sorted(out.rglob('*')):
 if p.is_file():entries.append(dict(path=str(p.relative_to(out)),bytes=p.stat().st_size,sha256=sha(p.read_bytes())))
dump('pins.json',dict(version=1,count=len(entries),pins=entries));b=(out/'pins.json').read_bytes()
dump('FROZEN.json',dict(status='FINAL CLEAR after resolved order-premise omission',payload_count=len(entries),file_count=len(entries)+2,pins_bytes=len(b),pins_sha256=sha(b),report_sha256=sha((out/'report.txt').read_bytes()),source_pins_sha256=sha((out/'source-pins.json').read_bytes()),sources=len(sources),new_modules=8,cuts=len(cuts),cut_lines=sum(x['end']-x['start']+1 for x in cuts),documents=len(docs),evidence=len(evidence)))
print((out/'FROZEN.json').read_text());print('FROZEN_SHA256',sha((out/'FROZEN.json').read_bytes()))
