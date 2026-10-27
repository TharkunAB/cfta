from pathlib import Path
import hashlib,json,re,datetime
A=Path('/tmp/mcfta-history-checked-origins-20261027');W=Path('/home/tritlo/Code/mcfta');R=A/'origin-checkpoint-review'
assert not (R/'FROZEN').exists()
def ident(b): return {'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def js(p,d): p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(d,indent=2)+'\n')
idx={'schema':'whole sources and explicit literal cuts','cut_convention':'one-based inclusive; splitlines(keepends=True); trailing original LF retained','sources':[]}
def add(p,dest,reviewed,cuts=()):
 b=p.read_bytes();q=R/dest;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b)
 rec={'source':str(p),'snapshot':str(q),**ident(b),'scope':'whole identity; semantic read scope stated separately','reviewed_scope':reviewed,'cuts':[]};ls=b.splitlines(keepends=True)
 for a,z,purpose in cuts:
  assert 1<=a<=z<=len(ls)
  c=b''.join(ls[a-1:z]);out=R/'literal-cuts'/f'{len(idx["sources"]):03}-{p.stem}-{a}-{z}.txt';out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(c)
  rec['cuts'].append({'first_line':a,'last_line':z,'snapshot':str(out),**ident(c),'scope':'literal cut','purpose':purpose})
 idx['sources'].append(rec);return b
modules=json.loads((A/'modules.json').read_text());checks=json.loads((A/'strict-checks.json').read_text())
if isinstance(checks,list): checks={x['module']:x['check'] for x in checks}
cutmap={
 'SourcePruningEnumerationAllocatedOriginArity':[(23,73,'actual checked constructor'),(75,92,'actual rejection'),(102,120,'actual Parent construction'),(139,189,'actual Post and selected identity')],
 'SourcePruningEnumerationArityOrigins':[(23,67,'key-dependent Fits and Heap; checked syntax'),(73,141,'exact constructors, bind and binder request'),(143,242,'real ordered raw build prefixes'),(244,331,'coherent encoding and actual reconstruction')],
 'SourcePruningEnumerationCheckedSyntaxOrigins':[(18,64,'Cached and actual accepted check derive source resource'),(66,116,'checked syntax conversion and actual initial build')],
 'SourcePruningEnumerationAllocatedOriginHeap':[(27,60,'exact requested key and full-table preservation'),(62,115,'actual checked/rejected receipt consumers')],
 'SourcePruningEnumerationArityHeapHead':[(25,56,'same actual head caller and explicit current Heap')],
 'SourcePruningEnumerationNativeCheckedOriginArity':[(26,78,'real ready branch derives projected Fits'),(80,126,'entire old accepted packet plus Fits'),(128,197,'same actual rich physical receipt and ordered raw child Walk')],
 'SourcePruningEnumerationNativeBodyOriginArity':[(26,94,'actual first instruction and rich tail Trace'),(96,158,'both accepted and sentinel actual full endpoints')]}
linecount=0;sourceids=[]
for m in modules:
 p=W/'lean/MicroCFTA'/f'{m}.lean';b=add(p,f'whole-inputs/{m}.lean','WHOLE final source read; local191 additionally bound to sealed exact strict2 review',cutmap[m]);linecount+=len(b.splitlines());sourceids.append({'module':m,**ident(b),'lines':len(b.splitlines())})
 check=checks[m] if isinstance(checks[m],str) else checks[m]['check']
 snap=A/check/'MicroCFTA'/p.name;assert snap.read_bytes()==b
 report=json.loads((A/check/'report.json').read_text());raw=(A/check/'raw.log').read_bytes();assert report['exit_code']==0 and raw==b'' and report['source_sha256']==ident(b)['sha256']
assert linecount==1158
for m,cuts in {
 'SourceEqualityNativeDemandAcceptedReceipt':[(62,88,'literal entire old body_produced admission/result')],
 'SourceEqualityNativeDemandAcceptedReadback':[(59,88,'actual raw done yields ordered child Walk and exact full constructor endpoint')],
 'SourceCurrentAllocatedNativePhysicalTraceCompletion':[(31,38,'Trace records actual current Inputs'),(91,110,'rich receipt includes trace/final Good; one-way done erasure')]
}.items():
 p=W/'lean/MicroCFTA'/f'{m}.lean';add(p,f'original-inputs/{p.name}','Focused literal cuts read; accepted receipt source WHOLE additionally read',cuts)
# Exact contract preservation: remove only the added Fits and normalize explicit State qualification.
o=(W/'lean/MicroCFTA/SourceEqualityNativeDemandAcceptedReceipt.lean').read_text();n=(W/'lean/MicroCFTA/SourcePruningEnumerationNativeCheckedOriginArity.lean').read_text()
o=o[o.index('theorem body_produced '):].split(' := by',1)[0]
n=n[n.index('theorem accepted_body_produced '):].split(' := by',1)[0]
suffix=' ∧\n      SourcePruningEnumerationArityOrigins.Fits built.1.entry.key.constraint built.1.children.length';assert n.endswith(suffix)
recovered=n[:-len(suffix)].replace('theorem accepted_body_produced ','theorem body_produced ').replace('SourceEqualityNativeDemand.State width','State width');assert recovered==o
(R/'contract-comparison').mkdir(exist_ok=True);(R/'contract-comparison/old.txt').write_text(o);(R/'contract-comparison/recovered.txt').write_text(recovered)
js(R/'contract-comparison/result.json',{'status':'pass','literal_equal':True,'old_contract':ident(o.encode()),'changes_only':['new theorem name','explicit qualification of native State width','appended returned-row Fits'],'old_producer_calls':n.count('SourceEqualityNativeDemandAcceptedReceipt.body_produced') if False else (W/'lean/MicroCFTA/SourcePruningEnumerationNativeCheckedOriginArity.lean').read_text().count('SourceEqualityNativeDemandAcceptedReceipt.body_produced')})
# Preserve all actual strict attempts, including failed sources. Failed source identities are history, not final proof claims.
attempts=[]
for p in sorted(A.glob('strict-*/report.json')):
 report=json.loads(p.read_text());raw=p.parent/'raw.log';assert ident(raw.read_bytes())=={k:report[k] for k in ['bytes','sha256']}
 for x in [p,raw]+sorted((p.parent/'MicroCFTA').glob('*.lean')):
  add(x,f'actual-checks/{p.parent.name}/{str(x.relative_to(p.parent))}','WHOLE report/raw identity checked; failure diagnostics focused and retained, not all cascades semantically reread')
 attempts.append({'check':p.parent.name,'exit_code':report['exit_code'],'raw':ident(raw.read_bytes()),'source_sha256':report.get('source_sha256')})
js(R/'strict-attempts.json',attempts)
for check in ['build-audit-final-1','public-readback-final-1']:
 for name in ['report.json','raw.log']+(['public.lean'] if check.startswith('public') else []):
  p=A/check/name;cuts=[]
  if name=='raw.log' and check.startswith('public'):
   ls=p.read_bytes().splitlines(keepends=True);starts=[i+1 for i,l in enumerate(ls) if re.match(rb'^(?:def |inductive )?MicroCFTA\.[A-Za-z0-9_.]+(?:\s|$)',l)]
   for i,a in enumerate(starts):cuts.append((a,starts[i+1]-1 if i+1<len(starts) else len(ls),'WHOLE exact public signature/axiom block or printed definition'))
   assert len(starts)==50
  b=add(p,f'actual-checks/{check}/{name}','WHOLE final output/check script/report read; public read in four contiguous chunks covering1-1661',cuts)
  if name=='raw.log':
   report=json.loads((A/check/'report.json').read_text());assert report['exit_code']==0 and ident(b)=={k:report[k] for k in ['bytes','sha256']}
# Compare all six old full signature/axiom blocks to literal prior public readback.
oldpub=add(A/'prior-public-readback/raw.log','public/prior-full-readback.log','Identity and six complete signature/axiom blocks compared; other older declarations not reread')
newpub=(A/'public-readback-final-1/raw.log').read_bytes()
def blocks(b):
 matches=list(re.finditer(rb'^(?:def |inductive )?MicroCFTA\.([A-Za-z0-9_.]+)(?:\s|$)',b,re.M));return {m.group(1).decode():b[m.start():matches[i+1].start() if i+1<len(matches) else len(b)] for i,m in enumerate(matches)}
oldb,newb=blocks(oldpub),blocks(newpub);pubval=json.loads((A/'public-validation.json').read_text());oldmatches=[]
for name in pubval['unchanged_prior_signatures']:
 assert oldb[name]==newb[name];oldmatches.append({'declaration':name,**ident(newb[name]),'literal_equal':True})
js(R/'old-public-comparison.json',{'status':'pass','full_six_old_signature_axiom_blocks':oldmatches})
# Current old source equality is independently checked without claiming a new semantic read of old modules.
prior=json.loads((A/'prior-strong-sources.json').read_text());oldsource=[]
for d in prior:
 b=(W/d['path']).read_bytes();assert ident(b)=={k:d[k] for k in ['bytes','sha256']};oldsource.append({**d,'current_byte_identity':True})
js(R/'old-source-comparison.json',oldsource)
for p in [A/x for x in ['modules.json','strict-checks.json','public-declarations.json','public-definitions.json','public-validation.json','source-validation.json','source-head.txt','prior-strong-sources.json']]:add(p,f'metadata/{p.name}','WHOLE current metadata read and underlying checks validated')
for p in [A/'arity-origin-review/native-worker/v4-to-v5.diff',A/'arity-origin-review/native-worker/hygiene-comparison.json',A/'arity-origin-review/native-body/v2-to-v3.diff']:
 add(p,f'revision-evidence/{p.parent.name}-{p.name}','WHOLE final semantic-neutral revision delta read')
# Source invariant reviews remain sealed; bind only exact review summaries/index/seals here.
for sub in ['origin-contract-review','origin-propagation-review','history-origin-transport-review']:
 for name in ['report.txt','FROZEN','source-index.json']:
  p=A/sub/name
  if p.exists():add(p,f'previous-local-reviews/{sub}/{name}','Bounded prior review evidence identity; no writes to frozen bundle')
# Whole current note and only inserted regions of the nine historical documents.
docval=json.loads((A/'document-validation.json').read_text());inverses=[];regions=[]
for d in docval:
 p=W/d['path'];b=p.read_bytes();assert ident(b)=={k:d[k] for k in ['bytes','sha256']}
 if 'offset' not in d:
  add(p,'documents/'+p.name,'WHOLE final current note read',[(1,len(b.splitlines()),'entire current note')]);continue
 off,n=d['offset'],d['inserted_bytes'];region=b[off:off+n];priorp=A/'prior-documents'/d['path'];old=priorp.read_bytes();assert b[:off]+b[off+n:]==old
 first=b[:off].count(b'\n')+1;last=first+len(region.splitlines())-1;assert b''.join(b.splitlines(keepends=True)[first-1:last])==region
 out=R/'document-cuts'/d['path'];out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(region)
 rec={'source':str(p),**ident(b),'scope':'whole document identity only; no whole snapshot; only inserted region reviewed','reviewed_scope':'literal inserted region only; historical body not reread','cuts':[{'first_line':first,'last_line':last,'snapshot':str(out),**ident(region),'scope':'literal cut; inserted region','purpose':'complete new checkpoint status; exact byte inverse checked'}]};idx['sources'].append(rec)
 inverses.append({'source':str(p),'prior_source':str(priorp),'prior_identity':ident(old),'current_identity':ident(b),'offset':off,'removed_bytes':n,'removed_identity':ident(region),'literal_prior_recovered':True});regions.append(region)
assert len(inverses)==9
standard=regions[0]
assert all(x==standard for i,x in enumerate(regions) if i!=2);assert regions[2].startswith(standard)
js(R/'document-inverses.json',{'status':'pass','nine_exact_inverses':inverses,'eight_identical_status_regions':True,'FINDINGS_status_then_extra_boundary_paragraph':True})
for name in ['document-validation.json','document-paths.json']:add(A/name,f'metadata/{name}','WHOLE document identity and insertion map read')
js(R/'source-index.json',idx)
js(R/'source-identities.json',sourceids)
js(R/'OPEN.json',{'status':'CLEAR / FINAL CHECKS BOUND; awaiting final seal','recorded_at':datetime.datetime.now().astimezone().isoformat(),'source_head':(A/'source-head.txt').read_text().strip(),'new_modules':7,'lines':1158,'public_theorems':36,'public_definitions':8,'old_signature_blocks_unchanged':6,'old_contract_literal_bytes':2501})
print(json.dumps({'status':'captured','source_records':len(idx['sources']),'literal_cuts':sum(len(x['cuts']) for x in idx['sources']),'source_lines':linecount,'public_bytes':len(newpub),'old_contract':ident(o.encode()),'docs':len(inverses)},indent=2))
