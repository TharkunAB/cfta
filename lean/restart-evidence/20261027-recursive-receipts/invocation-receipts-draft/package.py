from pathlib import Path
import json,hashlib,datetime,re
repo=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-recursive-receipts-20261027');out=area/'invocation-receipts-draft'
sha=lambda b:hashlib.sha256(b).hexdigest()
def write(dest,b):
 p=out/dest;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
def js(dest,x):write(dest,(json.dumps(x,indent=2,ensure_ascii=False)+'\n').encode())
sources=[];cuts=[];evidence=[]
def add(name,spans=None,declarations=None,scope='used contract and proof read'):
 p=repo/'lean/MicroCFTA'/(name+'.lean');b=p.read_bytes();text=b.decode();dest='inputs/lean/MicroCFTA/'+name+'.lean';write(dest,b)
 sources.append({'path':str(p),'source':str(p),'snapshot':dest,'bytes':len(b),'sha256':sha(b),'read_scope':scope})
 parts=list(spans or [])
 for kind,key in declarations or []:
  pos=text.index(kind+' '+key);end=text.index(' := by',pos)+len(' := by')
  parts.append((text[:pos].count('\n')+1,text[:end].count('\n')+1))
 lines=b.splitlines(keepends=True)
 for start,end in parts:
  assert 1<=start<=end<=len(lines),(name,start,end,len(lines))
  raw=b''.join(lines[start-1:end]);dest=f'cuts/{name}--{start}-{end}.lean';write(dest,raw)
  cuts.append({'path':str(p),'source':str(p),'snapshot':dest,'start':start,'end':end,'source_sha256':sha(b),'bytes':len(raw),'sha256':sha(raw)})
 return text
helper_name='SourcePruningEnumerationInvocationReceipts';wrapper_name='SourcePruningEnumerationSiblingInvocationResources'
helper=add(helper_name,declarations=[('theorem','alternatives_finite_invocation_receipts')],scope='whole new helper and all actual Invocation branch proofs read')
wrapper=add(wrapper_name,declarations=[('theorem','alternatives_finite_complete_resources_with_invocations'),('theorem','alternatives_finite_complete_invocation_resources')],scope='whole new wrapper and finite closure read')
head=add('SourcePruningEnumerationHeadAdmission',[(41,67),(71,102)], [('theorem','head_finite_complete_resources_with_receipt')],scope='whole completed-head API and actual producer wrapper read; separate peer owned its drafting/checks')
invocation=add('SourcePruningEnumerationHookInvocation',[(38,68)],scope='actual Invocation constructors and output provenance proof read; same fixed captured cache')
old=add('SourcePruningEnumerationFiniteSiblingResources',declarations=[('theorem','alternatives_finite_complete_resources')],scope='whole original sibling admission, output and head/suffix proof read')
add('SourcePruningEnumerationFiniteHeadResources',declarations=[('theorem','head_finite_complete_resources')],scope='original head/callback contract and reached-endpoint proof read')
add('SourcePruningEnumerationFiniteContract',[(28,48)],scope='whole original Complete contract read')
add('SourcePruningEnumerationFiniteResources',declarations=[('theorem','finite_complete')],scope='whole finite depth induction and original public wrapper read')
add('SourcePruningEnumerationFiniteReservation',[(192,199),(222,245)],scope='used HeadReserved/ScanReserved and exact head/tail APIs read; unrelated forecast proofs not freshly audited')
add('SourcePruningEnumerationNativeContinuations',[(47,81)],scope='actual ordered runtime read; general unrelated theorem suffix not freshly audited')
add('SourcePruningEnumerationRecursivePacket',[(21,35),(43,48)],scope='whole Packet, captured_post and receipt_packet contracts read')
for name,digest in [(helper_name,'43465dd399c14aceb04839f5b0a01ea89fbba8d2234b2b8305c5f008c93e3bc8'),(wrapper_name,'89c15015714c17272711c5e60891d8f1286427588fcfdc54491d705533c9b380')]:
 b=(out/(name+'.lean')).read_bytes();assert sha(b)==digest and b==(repo/'lean/MicroCFTA'/(name+'.lean')).read_bytes()
 assert not re.search(rb'\b(sorry|axiom|native_decide|maxHeartbeats)\b',b)
# Exact old admission and entire old output prefix are retained.
def decl(text,name):
 pos=text.index('theorem '+name);return text[pos:text.index(' := by',pos)]
def bodyless(text,name):return decl(text,name)[len('theorem '+name):]
old_decl=bodyless(old,'alternatives_finite_complete_resources')
helper_decl=bodyless(helper,'alternatives_finite_invocation_receipts')
old_admission=old_decl[:old_decl.index('    ∃ (bound :')]
helper_admission=helper_decl[:helper_decl.index('    ∃ bound :')]
assert old_admission==helper_admission
wrapper_decl=bodyless(wrapper,'alternatives_finite_complete_resources_with_invocations')
assert wrapper_decl.startswith(old_decl+' ∧\n')
rich=helper_decl[helper_decl.index('    ∃ bound : Nat, ∀ extra'):]
rich=rich.replace('    ∃ bound : Nat, ∀ extra','    (∀ extra',1)+')'
assert wrapper_decl[len(old_decl+' ∧\n'):]==rich
closed=bodyless(wrapper,'alternatives_finite_complete_invocation_resources')
recursive='''    (recursive : SourcePruningEnumerationRecursive.Complete (bits := bits) holeKey fits admits graph templates
      checkEmpty edgesOf stop order formulas solver recursiveFuel)
'''
assert wrapper_decl.count(recursive)==1 and closed==wrapper_decl.replace(recursive,'')
assert helper.count('SourcePruningEnumerationNativeHookResources.head_finite_complete_resources_with_receipt')==1
assert helper.count('hookPost.trans prefixPost')==2
assert helper.count('Post.refl packet.context')==2
assert wrapper.count('    alternatives_finite_complete_resources holeKey')==1
assert wrapper.count('    alternatives_finite_invocation_receipts holeKey')==1
assert wrapper.count('(SourcePruningEnumerationRecursive.finite_complete holeKey')==1
for name,txt in [('old-admission.txt',old_admission),('helper-admission.txt',helper_admission),('old-full-declaration.txt',old_decl),('retained-wrapper-prefix.txt',wrapper_decl[:len(old_decl)]),('rich-family.txt',rich),('wrapper-with-induction.txt',wrapper_decl),('finite-closed-wrapper.txt',closed)]:write('contracts/'+name,(txt+'\n').encode())
js('contracts/comparison.json',{'status':'PASS literal source comparisons; no new compiler','helper_original_admission_exact':True,'wrapper_entire_old_declaration_prefix_exact':True,'wrapper_final_rich_family_exact':True,'finite_corollary_removes_only_Complete_input':True,'old_sibling_producer_calls':1,'rich_helper_calls_in_wrapper':1,'finite_complete_instantiations':1,'aggregate_Post':'scan original Caller to actual headCaller/full headMemos','actual_query_input':'headMemos.query','common_work_fuel':'scanBound+receiptBound+extra, including both callback/resume fuel occurrences','source_only_runtime_unchanged':True})
def ev(p,role):
 p=Path(p);assert p.is_relative_to(area);b=p.read_bytes();dest='evidence/'+str(p.relative_to(area));write(dest,b)
 evidence.append({'path':str(p),'source':str(p),'snapshot':dest,'bytes':len(b),'sha256':sha(b),'role':role})
checks=[('strict-invocation-receipts-1',helper_name,False),('strict-invocation-receipts-2',helper_name,False),('strict-invocation-receipts-3',helper_name,True),('strict-sibling-resources-1',wrapper_name,True),('strict-sibling-resources-2',wrapper_name,True),('strict-head-admission-2','SourcePruningEnumerationHeadAdmission',True)]
for check,name,success in checks:
 d=area/check;r=json.loads((d/'report.json').read_text());raw=(d/'raw.log').read_bytes();src=(d/'MicroCFTA'/(name+'.lean')).read_bytes()
 assert (r['exit_code']==0)==success and r['bytes']==len(raw) and r['sha256']==sha(raw) and r['source_sha256']==sha(src)
 if success:
  assert raw==b'' and '-DwarningAsError=true'in r['command'] and '-Dlinter.all=true'in r['command']
  assert r['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 if check in ['strict-invocation-receipts-3','strict-sibling-resources-2','strict-head-admission-2']:
  assert src==(repo/'lean/MicroCFTA'/(name+'.lean')).read_bytes()
 for rel in ['report.json','raw.log','MicroCFTA/'+name+'.lean']:ev(d/rel,'actual Root final or earlier successful strict evidence'if success else'retained failing earlier strict evidence; not a pass')
js('source-pins.json',{'version':1,'status':'FINAL CLEAR SOURCE REVIEW; ROOT STRICT RESULTS BOUND','observed_at':datetime.datetime.now().astimezone().isoformat(),'sources':sources,'cuts':cuts,'evidence':evidence,'drafts':[{'path':name+'.lean','bytes':(out/(name+'.lean')).stat().st_size,'sha256':sha((out/(name+'.lean')).read_bytes())}for name in [helper_name,wrapper_name]],'new_checks_executed':False,'limits':'Full original finite resource gates remain; rich actual head histories do not derive semantic gates, backward acceptance, render existence or whole-path isolation persistence. No aggregate/publication assertion.'})
for s in sources:assert (out/s['snapshot']).read_bytes()==Path(s['source']).read_bytes()
for c in cuts:assert (out/c['snapshot']).read_bytes()==b''.join(Path(c['source']).read_bytes().splitlines(keepends=True)[c['start']-1:c['end']])
for e in evidence:assert (out/e['snapshot']).read_bytes()==Path(e['source']).read_bytes()
files=[p for p in sorted(out.rglob('*'))if p.is_file()and p not in {out/'pins.json',out/'FROZEN.json'}]
js('pins.json',{'version':1,'pins':[{'path':str(p.relative_to(out)),'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())}for p in files]});raw=(out/'pins.json').read_bytes()
f={'status':'FROZEN FINAL CLEAR SOURCE REVIEW WITH ROOT STRICT EVIDENCE','pins_count':len(files),'pins_bytes':len(raw),'pins_sha256':sha(raw),'source_count':len(sources),'source_whole_snapshots':len(sources),'cut_count':len(cuts),'cut_lines':sum(c['end']-c['start']+1 for c in cuts),'evidence_count':len(evidence),'new_module_count':2,'new_public_theorems':3,'report_sha256':sha((out/'report.txt').read_bytes()),'source_pins_sha256':sha((out/'source-pins.json').read_bytes()),'new_checks_executed':False};js('FROZEN.json',f)
for record in json.loads(raw)['pins']:
 b=(out/record['path']).read_bytes();assert len(b)==record['bytes'] and sha(b)==record['sha256']
assert len(files)+2==sum(p.is_file()for p in out.rglob('*'))
print(json.dumps(f,indent=2));print('FROZEN SHA256',sha((out/'FROZEN.json').read_bytes()));print('Exact files',len(files)+2)
