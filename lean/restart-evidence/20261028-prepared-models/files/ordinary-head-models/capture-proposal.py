from pathlib import Path
import hashlib,json
R=Path('/home/tritlo/Code/mcfta');O=Path('/tmp/mcfta-prepared-models-20261028/ordinary-head-models')
def h(b):return hashlib.sha256(b).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def save(p,b):
 p.parent.mkdir(parents=True,exist_ok=True)
 if p.exists():assert p.read_bytes()==b
 else:p.write_bytes(b)
 return {'path':str(p),'bytes':len(b),'sha256':h(b)}
index={'sources':[]}
plans={
'SourcePruningEnumerationPreparedFiniteHeadResources':[(1,170)],
'SourcePruningEnumerationFiniteHeadCoverage':[(1,205)],
'SourcePruningEnumerationNativeHeadCoverage':[(1,201)],
'SourcePruningEnumerationCapturedEdgeCoverage':[(1,291)],
'SourcePruningEnumerationSelectedEdgeCoverage':[(1,165)],
'SourcePruningEnumerationSelectedEdgeAdmission':[(1,111)],
'SourcePruningEnumerationFinalize':[(1,155)],
'SourcePruningEnumerationFinalizeLanguage':[(1,105)],
'SourcePruningEnumerationCapturedEdge':[(1,36)],
'SourcePruningEnumerationNativeBranches':[(1,28)],
'EnumerationFrame':[(476,488)],
'SourcePruningEnumerationRecursiveReservation':[(156,224)]}
for name,spans in plans.items():
 p=R/'lean/MicroCFTA'/f'{name}.lean';b=p.read_bytes();lines=b.splitlines(keepends=True);short=h(b)[:12]
 rec={'source':str(p),'whole':save(O/'sources'/f'{name}.{short}.whole',b),'cuts':[],'read_scope':'Literal indicated contracts/proofs used for source-only draft. Whole identity retained; whole-proof review claimed only if literal cut spans entire module.'}
 for lo,hi in spans:
  hi=min(hi,len(lines));bb=b''.join(lines[lo-1:hi]);rec['cuts'].append({**save(O/'cuts'/f'{name}.{short}.L{lo}-L{hi}.txt',bb),'first_line':lo,'last_line':hi})
 index['sources'].append(rec)
dump(O/'source-index.json',index)
old=(O/'contracts/old-entire-declaration.txt').read_bytes();recovered=(O/'contracts/recovered-entire-declaration.txt').read_bytes();assert old==recovered
variants=[]
for d in ['v1','v2']:
 p=O/f'drafts/{d}/SourcePruningEnumerationPreparedFiniteHeadCoverage.lean';b=p.read_bytes();variants.append({'variant':d,'path':str(p),'bytes':len(b),'lines':len(b.splitlines()),'sha256':h(b),'status':'SOURCE-ONLY at creation; actual Root compiler status must be retained separately'})
dump(O/'contracts/proposal-comparison.json',{'status':'entire original declaration recovered exactly after theorem rename, one result grouping pair and removal of appended semantic observer','original_bytes':len(old),'original_sha256':h(old),'new_admissions':[],'witnesses':['bound','receipt','middleCaller','saved','middleMemos','middleInventory'],'runtime_changes':[],'variant_declarations_identical':variants[0]['path'] and (Path(variants[0]['path']).read_text().split(' := by\n')[0]==Path(variants[1]['path']).read_text().split(' := by\n')[0]),'variants':variants})
print(json.dumps({'sources':len(index['sources']),'cuts':sum(len(s['cuts']) for s in index['sources']),'original_declaration_bytes':len(old),'original_sha256':h(old)}))
