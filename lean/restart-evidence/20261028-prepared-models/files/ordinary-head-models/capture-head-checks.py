from pathlib import Path
import json,hashlib,difflib
A=Path('/tmp/mcfta-prepared-models-20261028');O=A/'ordinary-head-models';R=Path('/home/tritlo/Code/mcfta')
def h(b):return hashlib.sha256(b).hexdigest()
def save(p,b):
 p.parent.mkdir(parents=True,exist_ok=True)
 if p.exists():assert p.read_bytes()==b,p
 else:p.write_bytes(b)
 return {'path':str(p),'bytes':len(b),'sha256':h(b)}
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
index=json.loads((O/'source-index.json').read_text())
def pin(p,spans,scope):
 b=p.read_bytes();short=h(b)[:12];same=next((r for r in index['sources'] if r['source']==str(p) and r['whole']['sha256']==h(b)),None)
 if same:return
 lines=b.splitlines(keepends=True);rec={'source':str(p),'whole':save(O/'sources'/f'{p.name}.{short}.whole',b),'cuts':[],'read_scope':scope}
 for lo,hi in spans:
  hi=min(hi,len(lines));rec['cuts'].append({**save(O/'cuts'/f'{p.name}.{short}.L{lo}-L{hi}.txt',b''.join(lines[lo-1:hi])),'first_line':lo,'last_line':hi})
 index['sources'].append(rec)
checks=[]
for name in ['head-models-v1','head-models-v2','head-models-v3']:
 d=A/name;rep=json.loads((d/'report.json').read_text());b=(d/'raw.log').read_bytes();assert len(b)==rep['bytes'] and h(b)==rep['sha256']
 sources=list((d/'MicroCFTA').glob('*.lean'));assert len(sources)==1 and h(sources[0].read_bytes())==rep['source_sha256']
 for p in [d/'report.json',d/'raw.log',*sources]:save(O/'evidence'/name/p.relative_to(d),p.read_bytes())
 checks.append({'name':name,**rep})
root=R/'lean/MicroCFTA/SourcePruningEnumerationPreparedFiniteHeadCoverage.lean';rootBytes=root.read_bytes()
assert rootBytes==(A/'head-models-v3/MicroCFTA'/root.name).read_bytes()
q=O/'drafts/root-head-v3'/root.name;save(q,rootBytes)
v2=(O/'drafts/v2'/root.name).read_text();s=rootBytes.decode();save(O/'drafts/head-v2-to-root-v3.diff',''.join(difflib.unified_diff(v2.splitlines(keepends=True),s.splitlines(keepends=True),fromfile='head-v2',tofile='root-head-v3')).encode())
old=(O/'contracts/old-entire-declaration.txt').read_text();binder=old[old.index('    (recursive :'):old.index('    (inventory :')]
new=s[s.index('theorem head_finite_complete_resources_accepting\n'):s.index(' := by\n',s.index('theorem head_finite_complete_resources_accepting\n'))]
marker=') ∧\n      ∀ (ambient :';assert marker in new
rec=new[:new.index(marker)].replace('theorem head_finite_complete_resources_accepting\n','theorem head_finite_complete_resources\n',1).replace('      ((∀ extra,','      (∀ extra,',1)
rec=rec.replace('    (inventory : Inventory)\n',binder+'    (inventory : Inventory)\n',1)
assert rec==old
save(O/'contracts/root-head-v3-recovered-entire-declaration.txt',rec.encode())
dump(O/'contracts/root-head-v3-contract-comparison.json',{'status':'PASS exact full original declaration recovery after restoring discharged Complete binder and removing only semantic observer/grouping/name suffix','old_bytes':len(old.encode()),'old_sha256':h(old.encode()),'removed_binder':binder,'new_admissions':[],'all_old_witnesses_and_return_fields_retained':True,'root_checked_source_sha256':h(rootBytes)})
pin(root,[(1,len(s.splitlines()))],'Owned v2 proof read and exact Root v3 change reviewed: import finite resource theorem, discharge Complete locally, preserve all returned fields and observer.')
for name,scope in [
 ('SourcePruningEnumerationFiniteSiblingCoverage','WHOLE reference proof read for actual indexed event induction.'),
 ('SourcePruningEnumerationPreparedFiniteSiblingResources','WHOLE existing resource contract and induction read; exact old declaration recovered.'),
 ('SourcePruningEnumerationContinuationInvocation','WHOLE generic actual completed-prefix invocation helper read.'),
 ('SourcePruningEnumerationPreparedFiniteResources','WHOLE new-worker finite induction and direct resource theorem read.')]:
 p=R/'lean/MicroCFTA'/f'{name}.lean';pin(p,[(1,len(p.read_bytes().splitlines()))],scope)
dump(O/'source-index.json',index)
dump(O/'checked-head-status.json',{'status':'Root head v1 FAIL 187B unknown completed; owned v2 strict PASS; strengthened Root v3 strict PASS','checks':checks,'current_installed_source':str(root),'current_sha256':h(rootBytes),'sibling_status':'SOURCE-ONLY candidate sibling-v2 pending Root compiler; no result inferred from head check'})
print((A/'head-models-v1/raw.log').read_text());print(json.dumps({'source_records':len(index['sources']),'literal_cuts':sum(len(s['cuts']) for s in index['sources']),'head_root_v3_sha256':h(rootBytes)}))
