from pathlib import Path
import hashlib,json,re,datetime
repo=Path('/home/tritlo/Code/mcfta'); area=Path('/tmp/mcfta-flat-native-branches-20261027'); out=area/'final-claim-review'
out.mkdir(exist_ok=True)
sha=lambda b:hashlib.sha256(b).hexdigest()
def readj(p):return json.loads(p.read_text())
def put(rel,data):
 p=out/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data);return rel
def jput(rel,data):return put(rel,(json.dumps(data,indent=2,ensure_ascii=False)+'\n').encode())
def info(b):return dict(bytes=len(b),sha256=sha(b))
sources=[];cuts=[];evidence=[];documents=[];now=datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
modules=readj(area/'modules.json')
expected=['e6621547d0f0cef824555d228b95c4dd42c9eac57798afeca342c631ef99a7c0','0800a6e254956406c4889bb031a0325817e60ef375a523dc4408f2e9375fbff4','b177c3399f128d73935d91ff802ffb13fb7f6445ad8b80d3c75f4a7956c6f0b3','1593c3459d75481081ed02d90ca9f7ba7122960c04b8e38eac39b1590104381b','7a2f77f6342315034cb9e5f80d9ea5b7b4dbbbb09857cbd960d892ed24a010df','1d6d608d840a75a2a6522d535fd594b2744f0a266d8ccc365b97c975e44ba3db','46950513ea0aacb33c41a606be23df3d19bdc00f5445fb94977ad5737ba1e698','ba13b125431796b0b05dd5b8cc9203d684cf5257da2746249a80f841221a5d08']
texts={}
def snapshot(p,role,scope='whole source reviewed'):
 b=p.read_bytes(); rel=str(p.relative_to(repo)) if p.is_relative_to(repo) else str(p.relative_to(area)); dest=('inputs/' if p.is_relative_to(repo) else 'evidence/')+rel
 put(dest,b); row=dict(path=str(p),source=str(p),repository_path=rel if p.is_relative_to(repo) else None,snapshot=dest,**info(b),lines=len(b.splitlines()),role=role,read_scope=scope);sources.append(row);texts[p.name]=b;return row
for name,h in zip(modules,expected):
 row=snapshot(repo/'lean/MicroCFTA'/f'{name}.lean','new checked module');assert row['sha256']==h,(name,row['sha256'])
for name in ['SourcePruningEnumerationNativeBranchCompletion','SourcePruningEnumerationNativeOrdinary','EnumerationFlatNativeIndex','EnumerationFlatCached']:
 snapshot(repo/'lean/MicroCFTA'/f'{name}.lean','existing admission or cache relation API','focused defining declarations and original completion header reviewed')
def cut(name,start,end,meaning):
 p=repo/'lean/MicroCFTA'/f'{name}.lean';b=p.read_bytes();ls=b.splitlines(keepends=True);assert 1<=start<=end<=len(ls);data=b''.join(ls[start-1:end]);dest=f'cuts/{name}-{start}-{end}.lean';put(dest,data);cuts.append(dict(path=str(p),source=str(p),source_sha256=sha(b),start=start,end=end,inclusive=True,snapshot=dest,**info(data),meaning=meaning))
def decl(name,token,header=False):
 p=repo/'lean/MicroCFTA'/f'{name}.lean';ls=p.read_text().splitlines(keepends=True);starts=[i for i,l in enumerate(ls) if re.match(r'^(?:private |noncomputable )?(?:def|abbrev|inductive|structure|theorem) '+re.escape(token)+r'(?:\s|\{|:)',l)];assert len(starts)==1,(name,token,starts);s=starts[0];e=s
 if header:
  while ':= by' not in ls[e]:e+=1
 else:
  e=s+1
  while e<len(ls) and not re.match(r'^(?:/--|/\-!|namespace |end |(?:private |noncomputable )?(?:def|abbrev|inductive|structure|theorem) )',ls[e]):e+=1
  e-=1
 while e>s and not ls[e].strip():e-=1
 cut(name,s+1,e+1,token+(' exact declaration header' if header else ' focused declaration'))
for name,tokens in {
 'SourceFlatPruningEntry':['enter','enter_replays'],
 'SourceFlatPruningNativeBranches':['advance','run','OrderedRelated','ReceiptsRelated','ResultRelated'],
 'SourceFlatPruningNativeOrdinary':['run'],
 'SourceFlatPruningNativeContinuations':['HookResult','HookResultRelated','StopRelated','ResultRelated','run'],
 'SourceFlatPruningNativeOrdinaryContinuations':['run'],
 'SourceFlatPruningNativeReceiptValidity':['Indexed','cache_of_related','of_related','processed'],
 'EnumerationFlatNativeIndex':['Correct','correct_of_related'],
 'EnumerationFlatCached':['Related']}.items():
 for token in tokens:decl(name,token,header=(token in ['enter_replays','correct_of_related']))
comparisons=[]
def header(name):
 text=(repo/'lean/MicroCFTA'/f'{name}.lean').read_text();start=text.index('theorem complete_with_history');end=text.index(' := by',start);return text[start:end]
def norm(t):
 for prefix in ['SourcePruningEnumerationNativeBranchCompletion.','SourcePruningEnumerationNativeBranches.','SourcePruningEnumerationNativeOrdinary.']:t=t.replace(prefix,'')
 return re.sub(r'\s+','',t)
for suffix in ['NativeBranchCompletion','NativeOrdinary']:
 old='SourcePruningEnumeration'+suffix;new='SourceFlatPruning'+('NativeOrdinaryCompletion' if suffix=='NativeOrdinary' else suffix)
 a=header(old);b=header(new);assert norm(b).startswith(norm(a)),suffix
 comparisons.append(dict(old=old,new=new,normalization='Whitespace removal and qualification normalization for the opened old NativeBranchCompletion, NativeBranches and NativeOrdinary namespaces only',old_header_bytes=len(a.encode()),normalized_old_sha256=sha(norm(a).encode()),retained=True))
 decl(old,'complete_with_history',True);decl(new,'complete_with_history',True)
jput('contract-retention.json',comparisons)
checks=[]
def evid(rel,scope):
 p=area/rel;b=p.read_bytes();dest='evidence/'+rel;put(dest,b);row=dict(path=str(p),source=str(p),snapshot=dest,**info(b),read_scope=scope);evidence.append(row);return b
for module,folder in readj(area/'strict-checks.json').items():
 report=readj(area/folder/'report.json');raw=(area/folder/'raw.log').read_bytes();source=repo/'lean/MicroCFTA'/f'{module}.lean';inputpath=area/folder/'MicroCFTA'/f'{module}.lean';assert report['exit_code']==0 and report['sha256']==sha(raw) and report['bytes']==len(raw);assert inputpath.read_bytes()==source.read_bytes();assert report['source_sha256']==sha(source.read_bytes());assert '-DwarningAsError=true' in report['command'] and '-Dlinter.all=true' in report['command'];assert report['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 if module!='Audit':assert not raw
 evid(folder+'/report.json','full report validated against actual strict input/live source/raw');evid(folder+'/raw.log','whole output checked');checks.append(dict(module=module,folder=folder,source_sha256=sha(source.read_bytes()),source_snapshot_equal=True,raw_bytes=len(raw)))
for folder in ['aggregate','installed-public']:
 r=readj(area/folder/'report.json');b=(area/folder/'raw.log').read_bytes();assert r['exit_code']==0 and r['sha256']==sha(b) and r['bytes']==len(b);evid(folder+'/report.json','full report and raw identity validated');evid(folder+'/raw.log','whole aggregate output reviewed' if folder=='aggregate' else 'structural signature/axiom/definition validation and focused readback, not a manual reading of every expanded expression')
public=(area/'installed-public/raw.log').read_bytes();pv=readj(area/'public-validation.json');assert info(public)==dict(bytes=pv['readback_bytes'],sha256=pv['sha256']);assert len(readj(area/'public-declarations.json'))==17 and len(readj(area/'public-definitions.json'))==21
for n in readj(area/'public-declarations.json')+readj(area/'public-definitions.json'):assert n.encode() in public,n
assert pv['axioms']==['Classical.choice','Quot.sound','propext']
for rel in ['modules.json','strict-checks.json','public-declarations.json','public-definitions.json','public-validation.json','source-commits.json','source-head.txt','source-validation.json','document-validation.json','document-paths.json','installed-public/public.lean']:
 evid(rel,'whole control data reviewed/validated; exact names and source identities retained')
aggregate=(area/'aggregate/raw.log').read_text();assert '4042' in aggregate and '78840' in aggregate
note=repo/'lean/notes-current-flat-native-branches.md';row=snapshot(note,'final generated current note','whole final note reviewed');assert row['bytes']==9729 and row['sha256']=='65a93c5f359391e59565b953736d0b90f7e7f79a953c42f1446219bb4cd6e950'
prefix=None
for row in readj(area/'document-validation.json'):
 if 'offset' not in row:continue
 p=repo/row['path'];b=p.read_bytes();assert info(b)==dict(bytes=row['bytes'],sha256=row['sha256']);a=row['offset'];z=a+row['inserted_bytes'];fragment=b[a:z]
 if prefix is None:prefix=fragment;put('documents/common-prefix.txt',fragment)
 assert fragment==prefix
 old=(area/'prior-documents'/row['path']).read_bytes();assert b[:a]+b[z:]==old
 dest='documents/prefixes/'+row['path'];put(dest,fragment);documents.append(dict(path=str(p),source=str(p),repository_path=row['path'],source_bytes=len(b),source_sha256=sha(b),offset=a,end_offset_exclusive=z,snapshot=dest,**info(fragment),start=b[:a].count(b'\n')+1,end=b[:z].count(b'\n'),inclusive=True,read_scope='only inserted literal prefix reviewed; old document bytes compared mechanically, not read or copied',old_bytes=len(old),old_sha256=sha(old),old_bytes_preserved=True))
assert len(documents)==9
newlines=sum(len((repo/'lean/MicroCFTA'/f'{n}.lean').read_bytes().splitlines()) for n in modules);assert newlines==1153
jput('validation.json',dict(status='CLEAR',checked_at=now,strict=checks,new_module_lines=newlines,theorems=17,new_theorems=15,definitions=21,aggregate_jobs=4042,dependency_checks=78840,public_readback=info(public),prefixes_identical=9,historical_bytes_preserved=True,builds_performed_by_reviewer=False))
report=f'''[{now}] FINAL CLEAR. No source, admission, or claim defect was found in the eight final flat-native sibling modules and the generated current note. This review reuses the completed whole-source peer reading, then binds the final source identities, receipt consumer, installed readback controls, current note and nine identical inserted status prefixes. Repository sources were not changed. No Lean, native, Git or network operation was run for this review.

The actual Entry worker reads and decodes the flat pending slot. enter_replays consumes the same successful old singleton. It does not claim equality for arbitrary insufficient old lookup fuel. The plain sibling worker preserves order and duplicates. Every alternative starts from the same captured enumeration cache. Each continuable actual head supplies the next native Caller and Queries. The suffix receives the full middle Memos and Post.context from that head. Keeps transports the captured cache facts at the reached native heap. Query equality is not used to infer equality of full memo tables.

Both complete_with_history wrappers retain their entire old admission and output prefixes. Literal header comparisons permit only whitespace and opened-name qualification normalization. The branch wrapper derives coupled old and flat executions by induction. The ordinary wrapper uses one SelectedEntry producer and one coupled branch producer. The same entered core, flags, waiting map and RenderStable receipt identify the initial framed cache. Bounds precede the universal related flat input. Each adequate actual flat endpoint remains existential for that run. No future flat observation, desired final cache or fixed flat forest across bounds is an input.

The receipt consumer has the correct scope. Indexed certifies an actual recovered cache at that receipt's own literal native heap. It is True when no cache is present. cache_of_related needs full Cached.Related and the original CacheValid witness. It does not use a core relation alone. of_related transfers the retained Admitted packet. A stopped cache can be certified through the admitted raw-empty case. Faults, missing results and nonempty stopped rows are not promoted to admission. processed follows the ordered receipt relation and original membership admission. Neither this result nor a valid rejection implies Safe.

The hook-aware runtime invokes a completed head's hook before its suffix. That suffix uses the actual post-hook Caller and Queries and restores the captured enumeration cache. Stopped outputs, reasons and optional endpoints remain present. Heterogeneous OrderedRelated and output/reason relations support the actual payload universes. The shared generic HookResult fixes the earlier type mismatch. Identity equations cover all inputs and bounds. They do not supply completion or correspondence for a concrete recursive hook. Plain Ranges follows the pre-hook head endpoint; it cannot establish post-hook or subtree admission.

The final note and status prefixes state these limits accurately. The strongest H6 and captured-rendering results remain unchanged. Initial allocation histories, semantic request ranges, recursive resource transport, language coverage and pruning contracts remain separate work. There is no new whole-enumeration or Haskell acceptance claim. No Haskell source changed and no native rerun is reported.

Existing evidence binds nine successful strict checks, including Audit, and {newlines} new source lines. All eight module logs are empty. Audit emits its dependency message. Aggregate Audit reports 4042 jobs and 78840 dependency checks and retains the earlier unused-input warning. Installed readback contains 17 theorem signatures, including two unchanged global declarations, and 21 definitions, with only propext, Classical.choice and Quot.sound. Public readback was checked structurally with focused source/readback correlation; this report does not claim a manual reading of every expanded expression. The exact final note, nine prefixes, source snapshots, focused declarations and actual report/raw identities are pinned. Historical status bodies were compared mechanically after prefix removal and were not copied into this bundle. No future archive, publication or push is inferred.
'''
put('report.txt',report.encode())
jput('source-pins.json',dict(version=1,status='FINAL CLEAR',observed_at=now,sources=sources,cuts=cuts,documents=documents,evidence=evidence,contract_retention='contract-retention.json',validation='validation.json',scope='No builds, Git, network or repository edits; no entire historical status document copies'))
# Recheck every whole snapshot and literal inclusive cut against current original bytes.
for row in sources+evidence:
 b=Path(row['source']).read_bytes();assert info(b)==dict(bytes=row['bytes'],sha256=row['sha256']);assert (out/row['snapshot']).read_bytes()==b
for row in cuts:
 b=Path(row['source']).read_bytes();assert sha(b)==row['source_sha256'];assert b''.join(b.splitlines(keepends=True)[row['start']-1:row['end']])==(out/row['snapshot']).read_bytes()
files=sorted(p for p in out.rglob('*') if p.is_file());payloads=[dict(path=str(p.relative_to(out)),**info(p.read_bytes())) for p in files];jput('pins.json',dict(version=1,files=payloads));pin=(out/'pins.json').read_bytes();jput('FROZEN.json',dict(version=1,status='FINAL CLEAR',observed_at=now,payload_count=len(payloads),exact_file_count=len(payloads)+2,pins_bytes=len(pin),pins_sha256=sha(pin),sources=len(sources),new_modules=len(modules),new_module_lines=newlines,cuts=len(cuts),cut_lines=sum(r['end']-r['start']+1 for r in cuts),document_prefixes=9,evidence_files=len(evidence),report_sha256=sha((out/'report.txt').read_bytes()),source_pins_sha256=sha((out/'source-pins.json').read_bytes()),no_Lean_native_Git_network_execution=True))
for p in out.rglob('*'):
 if p.is_file():p.chmod(0o444)
print(json.dumps(dict(path=str(out),report=info((out/'report.txt').read_bytes()),source_pins=info((out/'source-pins.json').read_bytes()),pins=info((out/'pins.json').read_bytes()),frozen=info((out/'FROZEN.json').read_bytes()),controls=readj(out/'FROZEN.json')),indent=2))
