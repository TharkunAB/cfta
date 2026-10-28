from pathlib import Path
import json,hashlib,difflib
root=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA');o=Path('/tmp/mcfta-prepared-composition-20261028/sibling-origins')
def sha(b):return hashlib.sha256(b).hexdigest()
old=(root/'SourcePruningEnumerationPreparedFiniteReceiptModels.lean').read_text();new=(o/'drafts/v1/SourcePruningEnumerationPreparedFiniteReceiptOrigins.lean').read_text()
a=old.index('theorem receipt_finite_complete_resources_models\n');z=old.index(' := by',a);orig=old[a:z]
a=new.index('theorem receipt_finite_complete_resources_origins\n');z=new.index(' := by',a);candidate=new[a:z]
group=candidate.index('            (Packet formulas solver next actual final metadata afterCache ∧')+12;end=candidate.index('\n      | _ => True',group);depth=0;close=None
for i in range(group,end):
 if candidate[i]=='(':depth+=1
 elif candidate[i]==')':
  depth-=1
  if depth==0:close=i;break
assert close is not None and candidate[close+1:].startswith(' ∧\n            (∀ ')
recovered=(candidate[:group]+candidate[group+1:close]+candidate[end:]).replace('theorem receipt_finite_complete_resources_origins\n','theorem receipt_finite_complete_resources_models\n',1)
assert recovered==orig
(o/'cuts/entire-original-receipt-model-declaration.lean').write_text(orig);(o/'cuts/entire-receipt-model-declaration-recovered.lean').write_text(recovered)
(o/'receipt-contract-comparison-v1.json').write_text(json.dumps({'scope':'ENTIRE old receipt_models declaration, all original admissions, fuel/outcome witnesses, every operational/resource/model field, and same completed-branch recorded/callbackCore existentials; proof excluded','bytes':len(orig.encode()),'sha256':sha(orig.encode()),'identical':True,'allowed_transforms':['Undo theorem name','Remove only inner retained-completed-body grouping plus appended origins iff and origin-policy semantic observer'],'old_producer_calls_in_new_proof':new[new.index(' := by'):].count('receipt_finite_complete_resources_models ')},indent=2)+'\n')
idx=json.loads((o/'source-index.json').read_text())
for name,spans,scope in [
 ('SourcePruningEnumerationPreparedFiniteReceiptModels.lean',[(1,133),(134,198)],'WHOLE old actual receipt-model producer and its complete contract read; one fixed resource outcome aligned with actual recording/core witnesses.'),
 ('SourcePruningEnumerationPolicyOrigins.lean',[(1,104),(170,212)],'Actual original structural-subtree policy and false-recording/callback transport laws read in these focused cuts; other current parts unreviewed.')]:
 p=root/name;b=p.read_bytes();lines=b.splitlines(keepends=True);dest=o/'sources'/name;dest.write_bytes(b);cuts=[]
 for first,last in spans:
  last=min(last,len(lines));cp=o/'cuts'/f'{p.stem}-L{first}-L{last}.lean';cb=b''.join(lines[first-1:last]);cp.write_bytes(cb);cuts.append({'path':str(cp.relative_to(o)),'bytes':len(cb),'sha256':sha(cb),'first_line':first,'last_line':last})
 idx['sources'].append({'source':str(p),'whole':{'path':str(dest.relative_to(o)),'bytes':len(b),'sha256':sha(b)},'cuts':cuts,'scope':scope})
(o/'source-index.json').write_text(json.dumps(idx,indent=2)+'\n')
print(len(orig.encode()),sha(orig.encode()))
