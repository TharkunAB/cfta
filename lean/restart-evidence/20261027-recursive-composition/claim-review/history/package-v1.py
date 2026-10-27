from pathlib import Path
import json, hashlib, datetime, re
repo=Path('/home/tritlo/Code/mcfta')
area=Path('/tmp/mcfta-recursive-composition-20261027')
out=area/'claim-review'
sha=lambda b:hashlib.sha256(b).hexdigest()
def write(dest,b):
    p=out/dest;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
def js(dest,x):write(dest,(json.dumps(x,indent=2,ensure_ascii=False)+'\n').encode())
sources=[];cuts=[];evidence=[];documents=[]
def source(rel, spans, whole=True, scope='full reviewed source'):
    p=repo/rel;b=p.read_bytes();s={'path':str(p),'source':str(p),'bytes':len(b),'sha256':sha(b),'read_scope':scope}
    if whole:s['snapshot']='inputs/'+rel;write(s['snapshot'],b)
    sources.append(s);lines=b.splitlines(keepends=True)
    for start,end in spans:
        assert 1<=start<=end<=len(lines),(rel,start,end,len(lines))
        data=b''.join(lines[start-1:end]);dest=f'cuts/{p.stem}--{start}-{end}.lean';write(dest,data)
        cuts.append({'path':str(p),'source':str(p),'snapshot':dest,'start':start,'end':end,'source_sha256':sha(b),'bytes':len(data),'sha256':sha(data)})
    return b
inputs=[
('SourcePruningEnumerationHookInvocation',[(38,79),(148,156)]),
('SourcePruningEnumerationOrdinaryInvocation',[(27,50),(86,98)]),
('SourcePruningEnumerationOutputHistory',[(27,70),(174,186)]),
('SourcePruningEnumerationPrefixCanonicalHistory',[(109,126),(201,232)]),
('SourcePruningEnumerationObservedFramesLanguage',[(19,28),(66,75)]),
('SourcePruningEnumerationCapturedIncoming',[(27,34),(60,86)]),
('SourcePruningEnumerationIsolatedPending',[(20,31),(37,39),(51,56),(62,63)]),
('SourceFlatPruningRecursiveOutputHistory',[(43,50),(58,77),(86,120)])]
validation=json.loads((area/'source-validation.json').read_text())
checked={r['module']:r for r in validation['strict_checks']}
actual_lines=0
for name,spans in inputs:
    b=source('lean/MicroCFTA/'+name+'.lean',spans);actual_lines+=len(b.splitlines())
    v=checked[name];assert len(b)==v['bytes'] and sha(b)==v['sha256']
    assert b==(area/'installed-sources/lean/MicroCFTA'/(name+'.lean')).read_bytes()
    assert b==(area/v['check']/'MicroCFTA'/(name+'.lean')).read_bytes()
    assert not re.search(rb'\b(sorry|axiom|native_decide|maxHeartbeats)\b',b)
assert actual_lines==1136
source('lean/MicroCFTA/SourceFlatPruningRecursiveOutputCompletion.lean',[(61,91)],True,'original retained producer header/conclusion and its producer call read')
source('lean/MicroCFTA/SourcePruningEnumerationRecursivePacket.lean',[(21,40)],True,'whole original Packet fields read; no modification')
source('lean/MicroCFTA/SourcePruningEnumerationRecursive.lean',[(65,82),(89,127)],False,'actual callback/resume/run runtime spans; prior frozen independent review reused')
source('lean/MicroCFTA/SourcePruningEnumerationNativeContinuations.lean',[(47,81)],False,'actual ordered post-hook sibling runtime; prior frozen independent review reused')
source('lean/MicroCFTA/SourcePruningEnumerationNativeOrdinaryContinuations.lean',[(20,34)],False,'actual entered-core framing and ordinary runtime; prior frozen independent review reused')
globals_expected={
'SourceCurrentColdFiniteWarmCalls':'e4665b0bb522ec88f1925fe6bc360b76e9e4bdfbe6192210ac708a3097a20cc5',
'SourcePruningEnumerationCapturedRendering':'18a81a7cdf0b208021f9ad5097e616270ad6001dbc75b08a7901352d5e174386',
'SourceFlatPruningCapturedResourceRendering':'73cba61e74141a8d2dc932eadf14372926b6318d0ceded73b774ec1c6fea57ef'}
for name,digest in globals_expected.items():
    b=source('lean/MicroCFTA/'+name+'.lean',[],False,'unchanged global boundary identity; full prior signature/axiom-list byte comparison below, no new whole proof audit')
    assert sha(b)==digest and b==(area/'installed-sources/lean/MicroCFTA'/(name+'.lean')).read_bytes()
audit=source('lean/MicroCFTA/Audit.lean',[(1,8)],False,'only new imports and checked source identity; no whole aggregate source audit')
assert audit==(area/'strict-aggregate-final/MicroCFTA/Audit.lean').read_bytes()==(area/'installed-sources/lean/MicroCFTA/Audit.lean').read_bytes()
def ev(p,role):
    p=Path(p);assert p.is_relative_to(area)
    b=p.read_bytes();dest='evidence/'+str(p.relative_to(area));write(dest,b)
    evidence.append({'path':str(p),'source':str(p),'snapshot':dest,'bytes':len(b),'sha256':sha(b),'role':role})
def report_check(check,success=True,empty=None):
    d=area/check;r=json.loads((d/'report.json').read_text());raw=(d/'raw.log').read_bytes()
    assert r['bytes']==len(raw) and r['sha256']==sha(raw)
    assert (r['exit_code']==0)==success
    if empty is not None:assert (raw==b'')==empty
    for rel in ['report.json','raw.log']:ev(d/rel,'actual final check evidence'if success else'preserved failed earlier check; not a passing result')
    return r
for name,_ in inputs:
    r=report_check(checked[name]['check'],True,True)
    assert r['source_sha256']==checked[name]['sha256']
    assert '-DwarningAsError=true'in r['command'] and '-Dlinter.all=true'in r['command']
    assert r['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
report_check('strict-aggregate-final',True,False)
assert (area/'strict-aggregate-final/raw.log').read_bytes()==b'Checked axiom dependencies of 79258 MicroCFTA theorems.\n'
report_check('build-aggregate-final',True,False)
assert b'4102 jobs' in (area/'build-aggregate-final/raw.log').read_bytes()
r=report_check('public-readback-final-2',True,False)
ev(area/'public-readback-final-2/public.lean','exact final installed readback program')
assert r['source_sha256']==sha((area/'public-readback-final-2/public.lean').read_bytes())
pub=(area/'public-readback-final-2/raw.log').read_bytes()
assert len(pub)==104359 and sha(pub)=='480ed1a9c648d82b10bff902e37b4a35ddbecdffa81d05be2fd9ad8ceef6c512'
assert not any(s in pub for s in ['⋯'.encode(),b'...',b'sorryAx'])
old=(area/'prior-public-readback/raw.log').read_bytes();ev(area/'prior-public-readback/raw.log','preserved prior installed full readback for signature and axiom-list equality')
pv=json.loads((area/'public-validation.json').read_text())
def sigblock(b,key):
    k=key.encode();m=re.search(rb'^'+re.escape(k)+rb'(?=\s|$)',b,re.M);assert m,key
    start=m.start();ax=b.index(b"'"+k+b"' depends on axioms:",start);end=b.index(b']',ax)+1
    return b[start:end],start,end
comparisons=[]
for key in pv['unchanged_prior_signatures']:
    previous,ps,pe=sigblock(old,key);current,cs,ce=sigblock(pub,key);assert previous==current,key
    comparisons.append({'name':key,'byte_identical':True,'bytes':len(current),'sha256':sha(current),'prior_start':ps,'prior_end_exclusive':pe,'current_start':cs,'current_end_exclusive':ce})
js('checks/unchanged-public-signatures.json',comparisons)
# Keep already produced failed states. No check is rerun.
for check in ['strict-hook-invocation-1','strict-ordinary-invocation-1','strict-output-history-1','strict-prefix-canonical-history-1','strict-observed-frames-language-1','strict-captured-incoming-1','strict-captured-incoming-2','public-readback-final']:
    report_check(check,False)
for rel in ['modules.json','strict-checks.json','source-validation.json','source-commits.json','public-validation.json','document-validation.json','published-base.txt']:
    ev(area/rel,'final current source/prose/validation record; source commits are recorded, not executed by this review')
# Retain immutable earlier proposal/review controls without changing their bundles.
for bundle in ['selected-canonical-draft','output-history-review','semantic-producer-review']:
    for rel in ['report.txt','source-pins.json','pins.json','FROZEN.json']:
        p=area/bundle/rel
        if p.exists():ev(p,'immutable earlier proposal or source-review control; original bundle unchanged')
for record in json.loads((area/'document-validation.json').read_text()):
    p=repo/record['path'];b=p.read_bytes();assert len(b)==record['bytes'] and sha(b)==record['sha256']
    item={'path':str(p),'source':str(p),'source_bytes':len(b),'source_sha256':sha(b)}
    if 'offset'in record:
        start=record['offset'];end=start+record['inserted_bytes'];data=b[start:end]
        assert len(data)==1709 and sha(data)=='17ec31b2d15d45bd80ef3a30a26d4eab224a4aa3fe1ed841c85e94e6466238af'
        prior=area/'prior-documents'/record['path'];prior_bytes=prior.read_bytes();assert b[:start]+b[end:]==prior_bytes
        dest='documents/prefixes/'+record['path'];write(dest,data)
        item.update({'snapshot':dest,'byte_start':start,'byte_end_exclusive':end,'bytes':len(data),'sha256':sha(data),'prior_source':str(prior),'prior_bytes':len(prior_bytes),'prior_sha256':sha(prior_bytes),'removal_exact':True,'read_scope':'literal inserted region read; historical remainder compared as bytes only'})
    else:
        assert len(b)==14916 and sha(b)=='6088c912c024871fe7d57c03f95f6543cffd456efa096a81a3185b40fc0101bf'
        dest='documents/'+record['path'];write(dest,b);item.update({'snapshot':dest,'bytes':len(b),'sha256':sha(b),'read_scope':'whole new note read'})
    documents.append(item)
js('checks/source-and-document-verification.json',{'status':'PASS source/data comparisons only','new_source_lines':actual_lines,'source_commits_recorded':['95f1db14b884560c171541274b24a1d532cdeed5','075898b5d81a4ad54a75339711727db522f62b06'],'new_source_strict_installed_equal':True,'eight_new_strict_logs_empty':True,'audit_strict_raw_bytes':56,'aggregate_jobs':4102,'aggregate_dependencies':79258,'three_prior_signature_and_axiom_lists_identical':True,'nine_prefixes_identical':True,'nine_exact_removals':True,'new_builds_or_checks_executed':False,'prose_corrections_requested':[]})
js('source-pins.json',{'version':1,'status':'FINAL CLEAR CLAIM REVIEW','observed_at':datetime.datetime.now().astimezone().isoformat(),'sources':sources,'cuts':cuts,'documents':documents,'evidence':evidence,'read_scope':'report.txt; full eight new sources and used contracts, exact prior review reuse, only new prose regions','limits':'Necessary operation history and local conditional invariants; no whole recursive acceptance, converse, coverage, global isolation persistence or physical Haskell certification.'})
# Validate literal source/cut/document inputs immediately before sealing.
for s in sources:
    b=Path(s['source']).read_bytes();assert len(b)==s['bytes'] and sha(b)==s['sha256']
    if 'snapshot'in s:assert (out/s['snapshot']).read_bytes()==b
for c in cuts:assert (out/c['snapshot']).read_bytes()==b''.join(Path(c['source']).read_bytes().splitlines(keepends=True)[c['start']-1:c['end']])
for d in documents:
    b=Path(d['source']).read_bytes();assert sha(b)==d['source_sha256']
    if 'byte_start'in d:assert (out/d['snapshot']).read_bytes()==b[d['byte_start']:d['byte_end_exclusive']]
for e in evidence:assert (out/e['snapshot']).read_bytes()==Path(e['source']).read_bytes()
files=[p for p in sorted(out.rglob('*')) if p.is_file() and p not in {out/'pins.json',out/'FROZEN.json'}]
pins={'version':1,'pins':[{'path':str(p.relative_to(out)),'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())}for p in files]};js('pins.json',pins)
pr=(out/'pins.json').read_bytes()
f={'status':'FROZEN FINAL CLEAR CLAIM REVIEW','pins_count':len(files),'pins_bytes':len(pr),'pins_sha256':sha(pr),'source_count':len(sources),'source_whole_snapshots':sum('snapshot'in s for s in sources),'cut_count':len(cuts),'cut_lines':sum(c['end']-c['start']+1 for c in cuts),'document_count':len(documents),'evidence_count':len(evidence),'report_sha256':sha((out/'report.txt').read_bytes()),'source_pins_sha256':sha((out/'source-pins.json').read_bytes()),'new_checks_executed':False};js('FROZEN.json',f)
for x in pins['pins']:
    b=(out/x['path']).read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256']
assert len(files)+2==sum(p.is_file()for p in out.rglob('*'))
print(json.dumps(f,indent=2));print('FROZEN SHA256',sha((out/'FROZEN.json').read_bytes()));print('Exact files',len(files)+2)
