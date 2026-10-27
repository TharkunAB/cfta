from pathlib import Path
import json,hashlib,re
R=Path('/home/tritlo/Code/mcfta');A=Path('/tmp/mcfta-native-history-proper-20261027');O=A/'selected-history-review';H=lambda b:hashlib.sha256(b).hexdigest()
def write(p,b):p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
def cp(src,dst):
 b=src.read_bytes();write(dst,b);return {'path':str(dst),'bytes':len(b),'sha256':H(b)}
idx=json.loads((O/'source-index.json').read_text());ss=idx['sources'];by={s['source']:s for s in ss}
def srcpin(src,scope,ranges=()):
 b=src.read_bytes();s=by.get(str(src))
 if s is None:
  s={'source':str(src),'whole':cp(src,O/'final-inputs'/src.relative_to(R)),'cuts':[],'reviewed_scope':scope};ss.append(s);by[str(src)]=s
 else:assert Path(s['whole']['path']).read_bytes()==b
 for first,last,tag in ranges:
  last=min(last,len(b.splitlines()));c=b''.join(b.splitlines(keepends=True)[first-1:last]);p=O/'final-cuts'/f'{src.name}-{tag}-L{first}-L{last}.txt';write(p,c);s['cuts'].append({'path':str(p),'bytes':len(c),'sha256':H(c),'first_line':first,'last_line':last})
 return s
# Match actual installed final sources to their strict snapshots.
sv=json.loads((A/'source-validation.json').read_text());whole_reviewed={'SourcePruningEnumerationSelectedEdgeEndpointProper','SourcePruningEnumerationCapturedEdgeEndpointProper','SourcePruningEnumerationTraversalEndpointProper','SourcePruningEnumerationResourceHistoryProper','SourcePruningEnumerationInitialRenderProper','SourcePruningEnumerationHistoryReceiptProper'}
for v in sv['strict_checks']:
 src=R/'lean/MicroCFTA'/f"{v['module']}.lean";b=src.read_bytes();assert len(b)==v['bytes'] and H(b)==v['sha256']
 scope='Final installed source identity and full public contract/axiom list reviewed. Other proof bodies not independently reviewed in this bundle.'
 if v['module'] in whole_reviewed:scope='Whole final proof body read, including exact earlier-version diffs. Actual endpoints and all original admissions retained.'
 if v['module']=='Audit':scope='Final source identity and fourteen-import inverse checked; actual aggregate/strict receipts read. Historical proof body not reread.'
 srcpin(src,scope)
# Focused actual receipt/history proof cuts.
for name,ranges in {
 'SourcePruningEnumerationSelectedEdgeEndpointProper.lean':[(76,92,'stopped-and-complete'),(147,168,'resource-observer')],
 'SourcePruningEnumerationCapturedEdgeEndpointProper.lean':[(62,102,'actual-inherited-and-finalizer'),(158,179,'resource-observer')],
 'SourcePruningEnumerationResourceHistoryProper.lean':[(35,87,'history-induction')],
 'SourcePruningEnumerationInitialRenderProper.lean':[(91,108,'startup-origin')],
 'SourcePruningEnumerationHistoryReceiptProper.lean':[(80,119,'actual-entry-head-callback')]
}.items():srcpin(R/'lean/MicroCFTA'/name,'Whole proof read.',ranges)
# Recover every ENTIRE old declaration independently from the final new syntax.
old_modules={'ChildResourcesProper':'ChildResources','TraversalResourcesProper':'TraversalResources','SelectedEdgeEndpointProper':'SelectedEdgeResources','CapturedEdgeEndpointProper':'CapturedEdgeResources','NativeHeadProper':'NativeBranchResources','NativeBranchProper':'NativeBranchResources','FiniteHeadProper':'FiniteHeadResources','InitialRenderProper':'InitialRendering'}
comparisons=[]
for v in json.loads((A/'root-contract-comparisons.json').read_text()):
 short=v['module'].removeprefix('SourcePruningEnumeration');newsrc=R/'lean/MicroCFTA'/f"{v['module']}.lean";s=newsrc.read_text();newname=v['theorem'];a=s.index('theorem '+newname);decl=s[a:s.index(' := by',a)]
 oldp=A/'whole-old-contracts'/f'{short}.txt';old=oldp.read_text();oldname=re.match(r'theorem (\w+)',old).group(1)
 original=R/'lean/MicroCFTA'/f'SourcePruningEnumeration{old_modules[short]}.lean';os=original.read_text();oa=os.index('theorem '+oldname);actualold=os[oa:os.index(' := by',oa)];assert actualold==old
 renamed=decl.replace('theorem '+newname,'theorem '+oldname,1);c=next(i for i,(l,r) in enumerate(zip(renamed,old)) if l!=r);assert renamed[c]=='('
 ungrouped=renamed[:c]+renamed[c+1:];assert ungrouped.startswith(old);suffix=ungrouped[len(old):];assert suffix.startswith(') ∧\n')
 assert len(old.encode())==v['bytes'] and H(old.encode())==v['sha256']
 folder=O/'final-contracts'/short
 for label,text in [('old-entire-declaration',old),('new-entire-declaration',decl),('recovered-entire-declaration',ungrouped[:len(old)]),('new-observer-suffix',suffix)]:write(folder/f'{label}.txt',text.encode())
 first=os[:oa].count('\n')+1;last=first+actualold.count('\n');srcpin(original,'Original declaration read and recovered literally. Historical producer proof body not independently reviewed.',[(first,last,'entire-old-declaration')])
 comparisons.append({**v,'independently_recovered':True,'original_source':str(original),'normalization':'Theorem rename, one added original-packet group and appended observer only; all binders and existential witnesses included.'})
write(O/'final-contracts/comparisons.json',(json.dumps(comparisons,indent=2)+'\n').encode())
# All actual commands: complete reports/raw logs and every strict/public source snapshot.
checks=[]
for p in sorted(A.glob('*/report.json')):
 d=p.parent;v=json.loads(p.read_text());raw=d/'raw.log';b=raw.read_bytes();assert len(b)==v['bytes'] and H(b)==v['sha256']
 assert v['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
 for f in [p,raw]+list((d/'MicroCFTA').glob('*.lean'))+list(d.glob('public.lean')):
  cp(f,O/'final-checks'/d.name/f.relative_to(d))
 for f in (d/'MicroCFTA').glob('*.lean'):
  if v.get('source_sha256'):assert H(f.read_bytes())==v['source_sha256']
 checks.append({'name':d.name,'exit_code':v['exit_code'],'bytes':len(b),'raw_sha256':H(b),'source_sha256':v.get('source_sha256')})
assert len(checks)==34
fails=sorted((x['name'],x['bytes']) for x in checks if x['exit_code']!=0)
assert fails==[('native-branch-proper-strict-1',933),('native-head-proper-strict-1',1388),('selected-endpoint-proper-strict-1',8787),('selected-endpoint-proper-strict-2',1544),('traversal-endpoint-strict-1',259),('traversal-resources-proper-strict-1',1478),('traversal-resources-proper-strict-2',1607)]
write(O/'final-checks/independent-report-verification.json',(json.dumps({'commands':len(checks),'failures':fails,'reports':checks},indent=2)+'\n').encode())
old=(A/'prior-public-readback/raw.log').read_bytes();new=(A/'public-readback-1/raw.log').read_bytes();blocks=(A/'new-public-blocks.txt').read_bytes();assert new==old+blocks and len(old)==857288 and len(new)==971561 and len(blocks)==114273 and len(blocks.splitlines())==1585
assert new.count(b'depends on axioms:')==233 and blocks.count(b'depends on axioms:')==21
axioms=set()
for s in re.findall(rb'depends on axioms:\s*\[([^]]*)\]',blocks,re.S):axioms.update(x.strip().decode() for x in s.split(b',') if x.strip())
assert axioms=={'propext','Classical.choice','Quot.sound'}
cp(A/'prior-public-readback/raw.log',O/'public/old-212-blocks.log');cp(A/'new-public-blocks.txt',O/'public/new-21-blocks.txt')
write(O/'public/independent-prefix-verification.json',(json.dumps({'status':'PASS','old_blocks':212,'old_bytes':len(old),'old_sha256':H(old),'current_blocks':233,'current_bytes':len(new),'current_sha256':H(new),'new_blocks':21,'new_bytes':len(blocks),'new_lines':1585,'new_sha256':H(blocks),'axioms':sorted(axioms),'exact_prefix_and_suffix':True},indent=2)+'\n').encode())
# The final new note and all nine insertions, retaining complete original bytes.
doc_checks=[];common=None
for v in json.loads((A/'document-validation.json').read_text()):
 src=R/v['path'];b=src.read_bytes();assert len(b)==v['bytes'] and H(b)==v['sha256']
 if 'offset' not in v:
  srcpin(src,'Whole final new note read and checked against all new public contracts, actual receipts and stated scope limits.');continue
 off=v['offset'];size=v['inserted_bytes'];ins=b[off:off+size];prior=(A/'prior-documents'/v['path']).read_bytes();assert b[:off]+b[off+size:]==prior and len(prior)==v['old_bytes'] and H(prior)==v['old_sha256']
 oldcopy=cp(A/'prior-documents'/v['path'],O/'documents/prior-documents'/v['path']);ip=O/'documents/insertions'/v['path'];write(ip,ins)
 if common is None:common=ins
 assert ins.startswith(common)
 if v['path']!='FINDINGS.md':assert ins==common
 first=b[:off].count(b'\n')+1;last=first+ins.count(b'\n')-(1 if ins.endswith(b'\n') else 0);assert b''.join(b.splitlines(keepends=True)[first-1:last])==ins
 ss.append({'source':str(src),'source_bytes':len(b),'source_sha256':H(b),'cuts':[{'path':str(ip),'bytes':len(ins),'sha256':H(ins),'first_line':first,'last_line':last}],'reconstruction':{'prior':oldcopy,'insert':{'path':str(ip),'bytes':len(ins),'sha256':H(ins)},'offset':off},'reviewed_scope':'Entire new insertion read; identical common text verified. Whole old bytes preserved and inverse checked; historical prose not reread.'})
 ss.append({'source':str(A/'prior-documents'/v['path']),'whole':oldcopy,'cuts':[],'reviewed_scope':'Original whole bytes and exact current-document removal inverse; historical prose not reread.'})
 doc_checks.append({'path':v['path'],'current_bytes':len(b),'current_sha256':H(b),'offset':off,'inserted_bytes':len(ins),'inserted_sha256':H(ins),'prior_bytes':len(prior),'prior_sha256':H(prior),'exact_inverse':True})
assert len(doc_checks)==9 and len(common)==2187
write(O/'documents/independent-inverse-verification.json',(json.dumps({'status':'PASS','common_bytes':len(common),'common_sha256':H(common),'documents':doc_checks},indent=2)+'\n').encode())
# Actual imported KBO evidence: data readback, not a new runtime execution.
native=(A/'kbo-context-and-generated-1/raw.log').read_text();rows=[tuple(map(int,x)) for x in re.findall(r'^\((\d+),Just (\d+),(\d+)\)$',native,re.M)];assert len(rows)==64 and [r[0] for r in rows]==list(range(64));assert all(a==b==2**(i+1)-1 for i,a,b in rows)
for expected in ['("leafComparison",GT)','("sameApplicationContextComparison",GT)','("localRewriteAcceptedInContext",True)']:assert expected in native
write(O/'final-metadata/native-data-check.json',(json.dumps({'status':'PASS','source':'kbo-context-and-generated-1/raw.log','all_64_recorded_rows_equal_exact_integer_recurrence':True,'index63':rows[-1],'context_comparisons':'GT/GT','actual_local_rewrite':True,'new_runtime_execution':False},indent=2)+'\n').encode())
srcpin(R/'specftacular/src/Specftacular/Rewriting.hs','Only Natural/lazy-map definitionWeight/definitionWeights source cuts and imported identity reviewed; no whole Haskell proof or independent runtime execution.',[(676,716,'natural-and-shared-weights')])
# Audit import inverse, using the preserved original.
v=json.loads((A/'audit-import-insertion.json').read_text());audit=(R/'lean/MicroCFTA/Audit.lean').read_bytes();prior=(A/'prior-sources/Audit.lean').read_bytes();off=v['insertion_offset'];assert audit[:off]+audit[off+v['bytes']:]==prior
write(O/'final-metadata/audit-inverse-verification.json',(json.dumps({'status':'PASS','prior_bytes':len(prior),'prior_sha256':H(prior),'inserted_bytes':v['bytes'],'current_bytes':len(audit),'current_sha256':H(audit)},indent=2)+'\n').encode())
for n in ['actual-commands.json','source-validation.json','public-validation.json','public-prefix-comparison.json','preservation-validation.json','document-validation.json','document-paths.json','root-contract-comparisons.json','audit-import-insertion.json','source-head.txt','source-commits.json','published-base.txt','modules.json','strict-checks.json','new-public-declarations.json','prior-strong-sources.json','prior-lean-sources.json','prior-haskell-sources.json','integration.json','helper-attempts.txt','public-catalog-correction.txt']:
 cp(A/n,O/'final-metadata'/n)
write(O/'source-index.json',(json.dumps(idx,indent=2)+'\n').encode())
print(json.dumps({'status':'CAPTURED','source_records':len(ss),'literal_cuts':sum(len(x.get('cuts',[])) for x in ss),'actual_commands':len(checks),'failed_commands':len(fails),'whole_old_contracts':len(comparisons),'document_inverses':len(doc_checks),'public_prefix_exact':True},indent=2))
