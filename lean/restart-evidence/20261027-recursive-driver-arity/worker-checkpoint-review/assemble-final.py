from pathlib import Path
import json,hashlib,re,subprocess
A=Path('/tmp/mcfta-recursive-driver-arity-20261027');R=Path('/home/tritlo/Code/mcfta');C=A/'worker-checkpoint-review'
def sha(b):return hashlib.sha256(b).hexdigest()
def j(p):return json.loads(p.read_text())
def dump(p,x):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(x,indent=2)+'\n')
def put(base,rel,b):p=base/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
def copy(base,records,p,rel,scope='Evidence identity checked'):
 b=p.read_bytes();put(base,rel,b);r={'source_path':str(p),'copy':rel,'bytes':len(b),'sha256':sha(b),'review_scope':scope};records.append(r);return r
mods=j(A/'modules.json');stats=j(A/'source-statistics.json');strict=j(A/'strict-checks.json');newnames=j(A/'new-public-declarations.json');allnames=j(A/'public-declarations.json');oldnames=j(A/'prior-public-declarations.json')
raw=(A/'public-readback-final-2/raw.log').read_bytes();oldraw=(A/'prior-public-readback/raw.log').read_bytes()
def blocks(b,names):
 lines=b.splitlines(keepends=True);pat=re.compile(rb'^MicroCFTA\.('+b'|'.join(re.escape(x.encode()) for x in names)+rb')(?=\s|\{)');starts=[]
 for i,l in enumerate(lines):
  m=pat.match(l)
  if m:starts.append((i,m.group(1).decode()))
 assert len(starts)==len(names),(len(starts),len(names))
 result={}
 for i,name in starts:
  tail=b''.join(lines[i:]);end=re.search(rb"'MicroCFTA\."+re.escape(name.encode())+rb"' depends on axioms: \[[^\]]*\]\n",tail)
  assert end,name
  block=tail[:end.end()];result[name]=(i+1,i+len(block.splitlines()),block)
 return result
B=blocks(raw,allnames);O=blocks(oldraw,oldnames)
assert len(B)==157 and len(newnames)==19 and len(O)==138
for name in oldnames:assert B[name][2]==O[name][2],name
axioms=re.findall(rb"'MicroCFTA\.([^']+)' depends on axioms: \[([^\]]*)\]",raw)
assert len(axioms)==157
for name,ax in axioms:assert set(x.strip() for x in ax.decode().split(',')) <= {'propext','Classical.choice','Quot.sound'},name
assert b'\xe2\x80\xa6' not in raw and b'...' not in raw
expected='4c3280871e59276730981c1b5208fe701e00b2cb100e4e9a474bf613503c04e9';assert len(raw)==525632 and sha(raw)==expected
records=[]
# Current proof sources are exact reviewed drafts, installed files and actual strict snapshots.
source_result=[]
for m in mods:
 p=R/'lean/MicroCFTA'/f'{m}.lean';b=p.read_bytes();s=next(s for s in stats['sources'] if s['module']==m)
 assert len(b)==s['bytes'] and len(b.splitlines())==s['lines'] and sha(b)==s['sha256']
 check=A/strict[m];rep=j(check/'report.json');cb=(check/'raw.log').read_bytes();snap=(check/'MicroCFTA'/f'{m}.lean').read_bytes()
 assert b==snap and rep['source_sha256']==sha(b) and rep['exit_code']==0 and cb==b'' and rep['bytes']==0 and rep['sha256']==sha(cb)
 assert rep['cgroup_limits']['memory.max']=='4294967296' and rep['cgroup_limits']['memory.swap.max']=='0'
 copy(C,records,p,'sources/'+p.name,'Whole source reviewed in the three independent proof bundles; installed bytes checked again')
 for sub in ('report.json','raw.log'):
  copy(C,records,check/sub,f'evidence/{strict[m]}/{sub}','Actual Root strict PASS; reviewer did not run compiler')
 source_result.append({'module':m,'bytes':len(b),'lines':len(b.splitlines()),'sha256':sha(b),'strict':strict[m]})
assert sum(x['lines'] for x in source_result)==2071 and len(source_result)==17
texts=[(R/'lean/MicroCFTA'/f'{m}.lean').read_text() for m in mods]
assert sum(len(re.findall(r'^theorem ',s,re.M)) for s in texts)==19
for t in texts:
 assert not re.search(r'^(?:def|structure|inductive|axiom) ',t,re.M)
 assert not re.search(r'\b(?:sorry|admit|native_decide)\b|set_option\s+(?:maxHeartbeats|linter\.|warningAsError)',t)
# Every prior source is checked against its published pin. Copies are provenance, not a claim of rereading proofs.
prior=[]
for x in j(A/'prior-strong-sources.json'):
 p=R/x['path'];b=p.read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256']
 copy(C,records,p,'prior-sources/'+p.name,'Published-byte preservation only; focused public contracts separately read')
 prior.append({'path':x['path'],'bytes':len(b),'sha256':sha(b),'unchanged':True})
assert len(prior)==63
# Literal Audit inverse.
audit=(R/'lean/MicroCFTA/Audit.lean').read_bytes();undo=audit
for m in mods:
 line=f'import MicroCFTA.{m}\n'.encode();assert undo.count(line)==1;undo=undo.replace(line,b'',1)
assert undo==(A/'original-Audit.lean').read_bytes()
copy(C,records,R/'lean/MicroCFTA/Audit.lean','sources/Audit.lean','Only added 17 import lines checked; remaining bytes exact')
copy(C,records,A/'original-Audit.lean','prior-sources/Audit.lean','Original whole bytes for exact inverse')
# Every final/failure raw report is retained without implying it passed.
check_result=[]
checknames=['audit-final-1','strict-audit-final-1','public-readback-final-1','public-readback-final-2','prior-public-readback','build-positive-foundations-1','build-positive-driver-1','build-history-rendering-arity-1']
for cn in checknames:
 p=A/cn;rep=j(p/'report.json');b=(p/'raw.log').read_bytes();assert rep['bytes']==len(b) and rep['sha256']==sha(b)
 assert rep['exit_code']==(1 if cn=='public-readback-final-1' else 0)
 if cn!='prior-public-readback':assert rep['cgroup_limits']['memory.max']=='4294967296' and rep['cgroup_limits']['memory.swap.max']=='0'
 for q in ('report.json','raw.log','public.lean'):
  if (p/q).exists():copy(C,records,p/q,f'evidence/{cn}/{q}','Actual Root output; pass/failure scope retained')
 check_result.append({'check':cn,'exit_code':rep['exit_code'],'raw_bytes':len(b),'raw_sha256':sha(b)})
assert b'4232 jobs' in (A/'audit-final-1/raw.log').read_bytes() and b'80042' in (A/'strict-audit-final-1/raw.log').read_bytes()
# Full public readback and literal selected blocks.
pubrec=next(x for x in records if x['copy']=='evidence/public-readback-final-2/raw.log');pubrec['cuts']=[]
focused=['SourceCurrentColdFiniteWarmCalls.constructed_node_calls','SourcePruningEnumerationRecursive.ResourceHistoryWithArity.sound','SourcePruningEnumerationRecursive.ResourceHistoryWithArity.render_sound','SourcePruningEnumerationRecursive.run_finite_complete_resources_render_sound']
for index,name in enumerate(newnames+focused):
 a,z,b=B[name];rel=f'public-blocks/{index+1:02d}-{name.rsplit(".",1)[-1]}.txt';put(C,rel,b)
 pubrec['cuts'].append({'path':rel,'start_line':a,'end_line':z,'bytes':len(b),'sha256':sha(b),'declaration':name,'review_scope':'Complete signature and axiom set read'})
# Exact public and source preservation is derived here, separately from Root validators.
public_result={'status':'pass','new_complete_blocks_read':19,'focused_prior_complete_blocks_read':focused,'all_blocks':157,'unchanged_prior_blocks':138,'bytes':len(raw),'sha256':sha(raw),'axioms_allowed':['propext','Classical.choice','Quot.sound'],'new_public_definitions':0,'every_prior_block_byte_exact':True}
dump(C/'public-independent-validation.json',public_result)
dump(C/'source-independent-validation.json',{'status':'pass','source_head':(A/'source-head.txt').read_text().strip(),'current':source_result,'prior':prior,'prior_count':63,'audit_inverse_exact':True,'reviewer_ran_builds':False})
dump(C/'check-independent-validation.json',check_result)
# New documents are read. Previous large historical content is validated, not reread.
docs=[]
for x in j(A/'document-validation.json'):
 p=R/x['path'];b=p.read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256']
 rr=copy(C,records,p,'documents/'+x['path'],'Whole new note read' if 'offset' not in x else 'Only new insertion read; all older bytes preserved by exact inverse')
 if 'offset' in x:
  priorp=A/'prior-documents'/x['path'];priorb=priorp.read_bytes();o=x['offset'];n=x['inserted_bytes'];cut=b[o:o+n];undo=b[:o]+b[o+n:];assert undo==priorb
  rel='document-insertions/'+x['path'];put(C,rel,cut)
  copy(C,records,priorp,'prior-documents/'+x['path'],'Byte inverse only; older historical prose not reread')
  docs.append({'document_source_path':str(p),'whole_bytes':len(b),'whole_sha256':sha(b),'offset':o,'inserted_bytes':n,'region_copy':rel,'region_sha256':sha(cut),'prior_sha256':sha(priorb),'inverse_byte_exact':True,'review_scope':'Full insertion read'})
 else:docs.append({'document_source_path':str(p),'whole_bytes':len(b),'whole_sha256':sha(b),'review_scope':'Whole new note read'})
assert len(docs)==10 and sum('inverse_byte_exact'in x for x in docs)==9
note=next(x for x in docs if 'inverse_byte_exact' not in x);assert note['whole_bytes']==11832 and note['whole_sha256']=='6528e33f825ae08c5b17044350d2e1a290aa44b90226daf2955ab5738bbd571a'
dump(C/'document-independent-validation.json',{'status':'pass','documents':docs})
# Root validation, original parser/harness failures and declared source boundary.
for rel in ['modules.json','new-public-declarations.json','public-declarations.json','prior-public-declarations.json','public-definitions.json','source-statistics.json','source-validation.json','public-validation.json','document-paths.json','document-validation.json','prior-strong-sources.json','public-import-repair.json','overlay-environment-repair.json','source-commits-finite-driver.json','source-commits-history-render.json','source-commit-audit.json','final-upstream-refresh.json','source-head.txt']:
 copy(C,records,A/rel,'root-evidence/'+rel,'Root provenance and declared scope; independent identities checked above')
# Include strict failures used by all source reviews, so no attempt is hidden by the checkpoint.
for cn in ['strict-finitearityeffects-1','strict-history-post-1','strict-finitehistoryrenderingarity-1','strict-finitehistoryrenderingarity-2']:
 for p in sorted((A/cn).rglob('*')):
  if p.is_file():copy(C,records,p,'evidence/'+cn+'/'+str(p.relative_to(A/cn)),'Retained actual failed attempt; no success claim')
copy(C,records,Path('/tmp/mcfta-document-recursive-driver-arity.py'),'root-evidence/document-generator.py','Document generator retained; not executed by this reviewer')
dump(C/'source-pins-final.json',{'sources':records})
# Final integration addenda and evidence for the three existing independent review bundles.
groups=[('callback-head-scan-independent-review',mods[:7],newnames[:8],'build-positive-foundations-1'),('driver-step-independent-review',mods[7:13],newnames[8:15],'build-positive-driver-1'),('history-render-independent-review',mods[13:],newnames[15:],'build-history-rendering-arity-1')]
for folder,modules,names,build in groups:
 D=A/folder;initial=j(D/'source-pins-initial.json')['sources'];rs=list(initial)
 for module in modules:
  p=R/'lean/MicroCFTA'/f'{module}.lean';copy(D,rs,p,'final-installed/'+p.name,'Installed source matches independently reviewed draft and final strict snapshot')
 pr=copy(D,rs,A/'public-readback-final-2/raw.log','final-context/public-raw.log','Full final public output retained; all relevant listed blocks read');pr['cuts']=[]
 for i,name in enumerate(names):
  a,z,b=B[name];rel=f'final-context/public-blocks/{i+1:02d}-{name.rsplit(".",1)[-1]}.txt';put(D,rel,b);pr['cuts'].append({'path':rel,'start_line':a,'end_line':z,'bytes':len(b),'sha256':sha(b),'declaration':name})
 for cn in [build,'public-readback-final-2','audit-final-1','strict-audit-final-1']:
  for sub in ['report.json','raw.log']:
   if cn=='public-readback-final-2' and sub=='raw.log':continue
   copy(D,rs,A/cn/sub,f'final-context/{cn}/{sub}','Actual installed/public/Audit evidence validated in checkpoint review')
 copy(D,rs,R/'lean/notes-current-recursive-driver-arity.md','final-context/notes-current-recursive-driver-arity.md','Whole final note read')
 # Literal new regions are pinned as document regions, not mistaken for whole source files.
 for x in docs:
  if 'region_copy'in x:put(D,'final-context/'+x['region_copy'],(C/x['region_copy']).read_bytes())
 for filename in ['public-independent-validation.json','source-independent-validation.json','document-independent-validation.json','check-independent-validation.json']:
  copy(D,rs,C/filename,'final-context/'+filename,'Independent final identity and scope checks')
 dump(D/'source-pins-final.json',{'sources':rs})
 stamp=subprocess.check_output(['date','+%Y-%m-%d %H:%M %Z'],text=True).strip()
 last='''The later all-depth driver and joint-history proofs now discharge the smaller-depth resource IH and derive every same-output arity history from the genuine initial Heap. The initial report remains immutable as the earlier bounded review. This final addendum records installed/public integration. It does not change the old consumer scopes or initial assumptions.'''
 if folder=='history-render-independent-review':last='''The final derived history and rendering theorem is installed at its reviewed v3 bytes. The previous report remains immutable. This final addendum records the successful public and documentation integration. Its supplied history-arity observer antecedent is removed using genuine initial Heap, not a future Heap premise.'''
 report=f'''[{stamp}]\n\nCLEAR and ready to seal. All {len(modules)} relevant installed modules match the independently reviewed final drafts and actual strict snapshots. All {len(names)} relevant public signature and axiom blocks were read in full. The complete public output is retained: 157 blocks, 525632 bytes, SHA256 {expected}. All 138 prior blocks are byte exact. Only propext, Classical.choice and Quot.sound occur.\n\n{last}\n\nThe installed build {build}, full Audit (4232 jobs, 80042 dependencies), strict Audit, source identities and actual 4 GiB/zero-swap receipts were verified. No new check was run by this reviewer. Existing dependency warnings remain recorded. Earlier failed sources and raw logs remain unchanged.\n\nThe whole 11832-byte final note and all nine literal inserted status/FINDINGS regions were read. All nine document inverses retain their complete earlier bytes. The prose keeps original Packet, resource/selector/ceiling/reservation contracts, initial arity Heap and Canonical explicit. Actual own Discharged storage, renderer success, checked returned residuals and original root storage/lookup remain rendering observations. No final satisfaction, future heap, or supplied arity history is a producer input. H6 remains unchanged. Coverage, convergence, public-entry admission, withoutRedundantEdges and full Haskell correspondence remain open. No Haskell test or runtime change is claimed.\n\nThe final source index is source-pins-final.json. The checkpoint-level report and independent preservation records are in ../worker-checkpoint-review. This bounded bundle will receive its own pins.json and FROZEN.json after all intended files are present. No previous frozen area was modified.\n'''
 (D/'report-final.md').write_text(report)
print(json.dumps({'checkpoint_records':len(records),'public_new':19,'prior_exact':138,'source_priors_exact':63,'docs_exact_inverses':9,'groups_ready':[x[0] for x in groups]},indent=2))
