from pathlib import Path
import hashlib,json
R=Path('/home/tritlo/Code/mcfta');B=Path('/tmp/mcfta-native-partial-output-20261028');O=B/'program-origin-review';L=R/'lean/MicroCFTA'
assert not(O/'FROZEN.json').exists()
sha=lambda b:hashlib.sha256(b).hexdigest()
def put(p,b):
 p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b);return {'path':str(p),'bytes':len(b),'sha256':sha(b)}
def dump(p,x):return put(p,(json.dumps(x,indent=2)+'\n').encode())
records={s['source']:s for s in json.loads((O/'source-index.json').read_text())['sources']}
def add(p,spans,scope,dest=None):
 p=Path(p);b=p.read_bytes();ls=b.splitlines(keepends=True);rel=p.relative_to(R) if p.is_relative_to(R) else Path('stage')/p.relative_to(B)
 rec={'source':str(p),'whole':put(dest or O/'sources'/rel,b),'cuts':[],'reviewed_scope':scope}
 for a,z in spans:
  assert 1<=a<=z<=len(ls),(p,a,z,len(ls))
  c=put(O/'cuts'/rel/(str(a)+'-'+str(z)+'.txt'),b''.join(ls[a-1:z]));c.update(first_line=a,last_line=z);rec['cuts'].append(c)
 records[str(p)]=rec;return b
add(L/'SourcePruningEnumerationSelectedValue.lean',[(18,34),(36,94)],'WHOLE final96-line standalone worker and first strictPASS read. Exactly one actual Mu unfold; Union exposes actual rows then makeNode; actual full native heap/least-language semantics retained. No Caller/Memos/Post or driver integration.')
add(R/'cfta/src/Data/CFTA/Enumeration.hs',[(468,479),(885,903)],'Only actual expandable classification and selected Mu/Union enumerateOutUVarWith branches read for source connection. Other incidental regions were inspected narrowly; no whole-module reading/execution or physical implementation certification claimed.')
commands=json.loads((B/'actual-commands.json').read_text());assert len(commands)==17
checks=[]
for entry in commands:
 d=B/entry['name'];r=json.loads((d/'report.json').read_text());raw=(d/'raw.log').read_bytes();assert r==entry['report']
 assert len(raw)==r['bytes'] and sha(raw)==r['sha256']
 assert r['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 if 'source_sha256' in r:assert sha(Path(r['command'][-1]).read_bytes())==r['source_sha256']
 for p in sorted(d.rglob('*')):
  if p.is_file() and p.suffix in {'.lean','.json','.log','.txt'}:add(p,[],'Actual Root command/source/report/full raw retained and hashes verified. Current17-command count excludes inherited prior-public receipt. Root ran every compiler/build.',O/'checks'/entry['name']/p.relative_to(d))
 checks.append({'name':entry['name'],'exit_code':r['exit_code'],'raw_bytes':len(raw),'raw_sha256':sha(raw),'source_sha256':r.get('source_sha256')})
assert sum(c['exit_code']!=0 for c in checks)==5
prior=(B/'prior-public-readback/raw.log').read_bytes();appendix=(B/'new-public-blocks.txt').read_bytes();whole=(B/'public-readback-1/raw.log').read_bytes()
assert len(prior)==1292203 and whole==prior+appendix and len(whole)==1329075
assert len(appendix)==36872 and len(appendix.splitlines())==469
assert sha(whole)=='08e37eb0ddd0f9032a3f2fb9a8368e5e4c0bdbb7e22bde80ee83ef248c65bc13'
assert sha(appendix)=='44a27ef0302330e156b4eae437003fffff6a23af789ccb4dfdd31570a5debdb2'
add(B/'new-public-blocks.txt',[],'ALL469 lines and all nine complete new theorem/axiom blocks plus all three public runtime definitions read. Final source interfaces/observers reviewed.')
add(B/'prior-public-readback/raw.log',[],'Whole prior installed readback preserved solely for exact1292203-byte prefix comparison. No claim that every older theorem was reread.')
for rel in ['actual-commands.json','source-head.txt','source-stats.json','source-validation.json','public-validation.json','public-prefix-comparison.json','preservation-validation.json','modules.json','strict-checks.json','root-contract-comparisons.json','audit-import-insertion.json','new-public-declarations.json','public-definitions.json','document-validation.json','document-paths.json']:
 add(B/rel,[],'WHOLE final current validation/provenance data read or verified. No future archive/publication or unreviewed historical semantic certification inferred.')
for p in sorted((B/'root-drafts').rglob('*')):
 if p.is_file() and p.suffix in {'.lean','.json','.txt','.patch'}:add(p,[],'Immutable Root lineage source/delta retained. Current final proof sources, actual failed diagnostics and relevant exact repairs reviewed.',O/'lineage/root-final'/p.relative_to(B/'root-drafts'))
# The final note must exist and be read before this capture is run.
validation=json.loads((B/'document-validation.json').read_text());newnotes=[d for d in validation if 'offset' not in d];assert len(newnotes)==1
n=newnotes[0];note=R/n['path'];nb=add(note,[],'WHOLE final current note read. Operational partial output versus observer-only models, source-position/type-origin limitations and standalone selected-value status reviewed.')
assert len(nb)==n['bytes'] and sha(nb)==n['sha256']
docs=[];common=None
for d in validation:
 if 'offset' not in d:continue
 p=R/d['path'];current=p.read_bytes();priorDoc=(B/'prior-documents'/d['path']).read_bytes();a=d['offset'];z=a+d['inserted_bytes'];insert=current[a:z]
 assert len(current)==d['bytes'] and sha(current)==d['sha256']
 assert len(priorDoc)==d['old_bytes'] and sha(priorDoc)==d['old_sha256']
 assert current[:a]+current[z:]==priorDoc and priorDoc[:a]+insert+priorDoc[a:]==current
 if d['path']=='FINDINGS.md':assert common is not None and insert.startswith(common)
 elif common is None:common=insert
 else:assert insert==common
 pr=put(O/'documents/prior'/d['path'],priorDoc);ins=put(O/'documents/insert'/d['path'],insert)
 records[str(p)]={'source':str(p),'bytes':len(current),'sha256':sha(current),'cuts':[dict(ins,byte_start=a,byte_end=z)],'reconstruction':{'offset':a,'prior':pr,'insert':ins},'reviewed_scope':'ALL current exact inserted bytes read. Prior whole body copied only for exact inverse reconstruction; no whole historical-body reading claim.'}
 docs.append({'path':d['path'],'offset':a,'inserted_bytes':len(insert),'inserted_sha256':sha(insert),'old_bytes':len(priorDoc),'old_sha256':sha(priorDoc),'current_sha256':sha(current),'exact_inverse':True})
assert len(docs)==9
dump(O/'source-index.json',{'sources':list(records.values())})
dump(O/'review-validation.json',{'status':'pass','source_head':(B/'source-head.txt').read_text().strip(),'source_identities':len(records),'literal_cuts':sum(len(s['cuts']) for s in records.values()),'commands':checks,'current_command_count':17,'failed_attempts':5,'all_commands_measured_memory_max_high_4GiB_swap_zero':True,'old_public_prefix_bytes':1292203,'new_public_bytes':len(appendix),'new_public_lines':469,'new_public_sha256':sha(appendix),'public_bytes':len(whole),'public_sha256':sha(whole),'document_inverses':docs,'common_insertion_bytes':len(common),'common_insertion_sha256':sha(common),'whole_note_bytes':len(nb),'whole_note_sha256':sha(nb)})
print(json.dumps({'status':'pass','sources':len(records),'cuts':sum(len(s['cuts']) for s in records.values()),'documents':len(docs),'note_bytes':len(nb),'commands':len(checks),'failures':5},indent=2))
