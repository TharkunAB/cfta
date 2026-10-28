from pathlib import Path
import hashlib,json
R=Path('/home/tritlo/Code/mcfta'); B=Path('/tmp/mcfta-accepted-prefix-20261028'); O=B/'startup-model-review'
assert not (O/'FROZEN.json').exists()
sha=lambda b:hashlib.sha256(b).hexdigest()
def put(p,b):
 p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
 return {'path':str(p),'bytes':len(b),'sha256':sha(b)}
def dump(p,v):return put(p,(json.dumps(v,indent=2)+'\n').encode())
records={s['source']:s for s in json.loads((O/'source-index.json').read_text())['sources']}
def add(p,spans,scope,dest=None):
 p=Path(p); b=p.read_bytes();lines=b.splitlines(keepends=True)
 rel=p.relative_to(R) if p.is_relative_to(R) else Path('stage')/p.relative_to(B)
 rec={'source':str(p),'whole':put(dest or O/'sources'/rel,b),'cuts':[],'reviewed_scope':scope}
 for first,last in spans:
  assert 1<=first<=last<=len(lines),(p,first,last,len(lines))
  cut=put(O/'cuts'/rel/(str(first)+'-'+str(last)+'.txt'),b''.join(lines[first-1:last]));cut.update(first_line=first,last_line=last);rec['cuts'].append(cut)
 records[str(p)]=rec
 return b
L=R/'lean/MicroCFTA'
add(L/'SourcePruningEnumerationPrefixCoverage.lean',[(18,76),(78,105),(115,148),(303,360),(420,470)],'WHOLE final 472-line source and all four public statements read. Actual original policies, native Mu/Union exposure, literal read/action/write endpoints and same assignment were reviewed; no future model is an admission.')
add(L/'SourcePruningEnumerationPrefixModels.lean',[(26,57),(58,100)],'WHOLE 102-line final source read. Entire original three-family canonical prefix declaration recovers after grouping; old producer once, uniform bound before original semantic observer.')
add(L/'SourcePruningEnumerationPrefixCanonicalHistory.lean',[(201,241)],'WHOLE 241-line old source read. Exact final old canonical prefix declaration recovered independently from the new model theorem.')
add(L/'SourcePruningEnumerationDischargeBoundary.lean',[(36,74),(76,97),(107,132),(151,187),(188,218)],'WHOLE final 220-line source and five public statements read. DONE is not Discharged; nonrecursive pending condition is explicit. Original-admission recursive startup singleton family is not an executed physical Haskell witness.')
# Recover the whole old prefix theorem declaration, including its original name.
a=(L/'SourcePruningEnumerationPrefixCanonicalHistory.lean').read_text(); n=(L/'SourcePruningEnumerationPrefixModels.lean').read_text()
a=a[a.index('theorem packet_prefix_complete_semantics_canonical'):].split(':= by',1)[0].rstrip()
n=n[n.index('theorem packet_prefix_complete_semantics_canonical_models'):].split(':= by',1)[0].rstrip()
part=n.split(') ∧\n      ∀ extra selected,',1)[0]
part=part.replace('theorem packet_prefix_complete_semantics_canonical_models','theorem packet_prefix_complete_semantics_canonical',1).replace('      ((∀ extra selected,','      (∀ extra selected,',1)
assert part==a and len(a.encode())==2466
put(O/'root-review/entire-original-prefix-declaration.txt',a.encode());put(O/'root-review/recovered-original-prefix-declaration.txt',part.encode())
dump(O/'root-review/prefix-contract-comparison.json',{'status':'pass','scope':'Entire old declaration including theorem name, every binder, bound and all three result families. Pre-proof whitespace trimmed. Only theorem rename, one result grouping and semantic appendix removed.','bytes':len(a.encode()),'sha256':sha(a.encode()),'byte_identical':True,'new_admission':False,'old_producer_calls':(L/'SourcePruningEnumerationPrefixModels.lean').read_text().split(':= by',1)[1].count(':= packet_prefix_complete_semantics_canonical\n')})
# Preserve every actual current command and source snapshot, including four failed checks.
commands=json.loads((B/'actual-commands.json').read_text()); assert len(commands)==14
checks=[]
for entry in commands:
 name=entry['name'];p=B/name;r=json.loads((p/'report.json').read_text());raw=(p/'raw.log').read_bytes()
 assert r==entry['report'] and len(raw)==r['bytes'] and sha(raw)==r['sha256']
 assert r['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 if 'source_sha256' in r:
  checked=Path(r['command'][-1]);assert sha(checked.read_bytes())==r['source_sha256']
 for f in sorted(p.rglob('*')):
  if f.is_file() and f.suffix in {'.lean','.json','.log','.txt'}:
   dest=O/'checks'/name/f.relative_to(p)
   add(f,[],'Actual Root check input/report/raw output preserved. Report/source/raw hash and measured 4 GiB memory.max/high with zero swap verified. Historical failed bodies retained; final source proof reviewed separately.',dest)
 checks.append({'name':name,'exit_code':r['exit_code'],'raw_bytes':len(raw),'raw_sha256':sha(raw),'source_sha256':r.get('source_sha256')})
assert sum(x['exit_code']!=0 for x in checks)==4
for f in sorted((B/'root-drafts').rglob('*')):
 if f.is_file() and f.suffix in {'.lean','.json','.txt'}:add(f,[],'Immutable Root source revision/contract provenance. Historical draft identity retained; not a claim that every superseded proof was independently reread.',O/'lineage/root-drafts'/f.relative_to(B/'root-drafts'))
# Independent literal old readback prefix and new full appendix verification.
old=(B/'prior-public-readback/raw.log').read_bytes(); current=(B/'public-readback-1/raw.log').read_bytes(); appendix=(B/'new-public-blocks.txt').read_bytes()
assert len(old)==1213984 and current==old+appendix and len(current)==1292203 and len(appendix)==78219
assert sha(current)=='d69e320cb852a354647a64dec18fd3aaa5da747cf84793bc085d6bf8dee6d25c'
assert sha(appendix)=='b829f22b64d451afd763390c670c71587d436f92aa98cbe721feb1a76f85eca5'
assert len(appendix.splitlines())==1008
add(B/'new-public-blocks.txt',[],'ALL 1008 lines and 14 complete new public theorem/axiom blocks read. No new definition. Root source statements and native/semantic scope were checked.')
add(B/'prior-public-readback/raw.log',[],'Preserved whole prior installed readback used ONLY for byte-exact prefix comparison. No claim that all 309 older theorem bodies/signatures were reread this turn.')
for rel in ['actual-commands.json','root-contract-comparisons.json','source-validation.json','public-validation.json','public-prefix-comparison.json','preservation-validation.json','source-head.txt','source-commits.json','source-stats.json','modules.json','strict-checks.json','audit-import-insertion.json','new-public-declarations.json','public-definitions.json','document-validation.json','document-paths.json']:
 add(B/rel,[],'WHOLE current final validation/provenance data read or verified for the report; claims remain limited to the actual current contracts and checks.')
for f in sorted((B/'root-contract-recovery').rglob('*')):
 if f.is_file():add(f,[],'Root independent literal old-contract recovery; compared to this reviewer\'s independently recovered startup/prefix/callback originals.')
# Final note is whole-read. Large historical status bodies are preserved by inverse insertion.
note=R/'lean/notes-current-accepted-prefix-models.md'
nb=add(note,[(1,30),(69,111),(112,150)],'WHOLE final 13050-byte note read. Scope, genuine policies, deliberate recursive truncation, open global coverage, validation counts and Haskell non-defect wording checked.')
assert len(nb)==13050 and sha(nb)=='8b5a1616979d4e7404f82fa666e7a745567ed4da635493be7b365829d50c02e0'
documents=[];common=None
for z in json.loads((B/'document-validation.json').read_text()):
 if 'offset' not in z:continue
 p=R/z['path'];b=p.read_bytes();start=z['offset'];end=start+z['inserted_bytes'];insertion=b[start:end];prior=(B/'prior-documents'/z['path']).read_bytes()
 assert len(b)==z['bytes'] and sha(b)==z['sha256']
 assert len(prior)==z['old_bytes'] and sha(prior)==z['old_sha256']
 assert b[:start]+b[end:]==prior and prior[:start]+insertion+prior[start:]==b
 if z['path']=='FINDINGS.md':
  assert common is not None and insertion.startswith(common)
 elif common is None:common=insertion
 else:assert insertion==common
 prev=put(O/'documents/prior'/z['path'],prior);ins=put(O/'documents/insert'/z['path'],insertion)
 cut=dict(ins,byte_start=start,byte_end=end)
 records[str(p)]={'source':str(p),'bytes':len(b),'sha256':sha(b),'cuts':[cut],'reconstruction':{'offset':start,'prior':prev,'insert':ins},'reviewed_scope':'ALL exact current inserted bytes read. Whole prior body copied only for exact inverse reconstruction; no whole historical-body reading claim.'}
 documents.append({'path':z['path'],'offset':start,'inserted_bytes':len(insertion),'inserted_sha256':sha(insertion),'inverse_old_bytes':len(prior),'inverse_old_sha256':sha(prior),'current_sha256':sha(b),'exact_inverse':True})
assert len(documents)==9 and len(common)==2510
# Commit the current source-index only after all captures and comparisons pass.
dump(O/'source-index.json',{'sources':list(records.values())})
dump(O/'review-validation.json',{'status':'pass','source_head':(B/'source-head.txt').read_text().strip(),'current_commands':14,'failed_attempts':4,'checks':checks,'all_current_checks_measured_4GiB_memory_max_high_swap_zero':True,'new_public_blocks':14,'new_public_lines':1008,'new_public_bytes':len(appendix),'new_public_sha256':sha(appendix),'old_public_exact_prefix_bytes':len(old),'public_bytes':len(current),'public_sha256':sha(current),'documents':documents,'common_insertions':8,'common_insertion_bytes':len(common),'common_insertion_sha256':sha(common),'note_bytes':len(nb),'note_sha256':sha(nb),'source_identities':len(records),'literal_cuts':sum(len(s['cuts']) for s in records.values()),'no_reviewer_compiler_build_Git_native_network_board_or_repository_write':True})
print(json.dumps({'status':'pass','sources':len(records),'cuts':sum(len(s['cuts']) for s in records.values()),'checks':len(checks),'failed_checks':sum(x['exit_code']!=0 for x in checks),'doc_inverses':len(documents),'note_bytes':len(nb),'old_prefix_bytes':len(old),'new_public_bytes':len(appendix)},indent=2))
