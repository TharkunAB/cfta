from pathlib import Path
import hashlib,json
own=Path(__file__).parent
repo=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA')
out=own/'contracts';out.mkdir(exist_ok=True)
def sha(d):return hashlib.sha256(d).hexdigest()
def declaration(module,name):
 s=(repo/(module+'.lean')).read_text();a=s.index('theorem '+name);z=s.index(' := by',a);return s[a:z]
def remove_appended_group(s):
 a=s.index('    ∃ ');e=s.index('\n',a)+1;head=s[:e];body=s[e:]
 assert body.startswith('      (')
 depth=0;j=None
 for i in range(6,len(body)):
  c=body[i]
  if c=='(':depth+=1
  elif c==')':
   depth-=1
   if depth==0:j=i;break
 assert j is not None and body[j+1:].startswith(' ∧\n'),body[j+1:j+70]
 return head+body[:6]+body[7:j],body[j+1:]
def write(label,old,new,recovered,mapping,scope):
 assert recovered==old,(label,len(old),len(recovered))
 for tag,txt in [('original',old),('extended',new),('recovered',recovered)]:
  (out/(label+'.'+tag+'.txt')).write_text(txt)
 return {'id':label,'status':'pass','scope':scope,'mapping':mapping,'old_bytes':len(old.encode()),'old_sha256':sha(old.encode()),'new_bytes':len(new.encode()),'new_sha256':sha(new.encode()),'recovered_bytes':len(recovered.encode()),'recovered_sha256':sha(recovered.encode()),'entire_declaration_byte_equal':True}
records=[]
old=declaration('SourcePruningEnumerationSelectedPreparation','complete')
new=declaration('SourcePruningEnumerationSelectedOrdinaryDispatch','complete')
r,app=remove_appended_group(new);r=r.replace('SourcePruningEnumerationSelectedPreparation.run','run')
records.append(write('ordinary-retains-preparation',old,new,r,['Remove only appended actual-branch family and its outer group.','Reverse the qualification of the old preparation run.'],'Entire explicit original theorem declaration, including admissions and all existential result fields. Execution needs extra standard DecidableEq instances in the enclosing new module.'))
old=declaration('SourcePruningEnumerationSelectedPreparationResources','complete_resources')
new=declaration('SourcePruningEnumerationSelectedDispatch','complete_resources')
r,app=remove_appended_group(new);r=r.replace('SourcePruningEnumerationSelectedPreparation.run','run')
records.append(write('combined-retains-preparation-resources',old,new,r,['Remove only appended actual-branch family and its outer group.','Reverse the qualification of the old preparation run.'],'Entire explicit original preparation-resource declaration, including all admissions, witnesses, model packet and derived original-profile forecast.'))
old=declaration('SourcePruningEnumerationSelectedPreparation','complete')
new=declaration('SourcePruningEnumerationSelectedPreparationResources','complete_resources')
r,app=remove_appended_group(new)
r=r.replace('theorem complete_resources\n','theorem complete\n',1)
added='\n    (profile : SourceCurrentAllocatedNativeResourceForecast.Profile)\n    (fits : SourceCurrentConstrainedCapGeneratedQueryResources.Fits profile caller.checked)'
assert added+' :' in r
r=r.replace(added+' :',' :',1)
records.append(write('preparation-resources-retains-preparation',old,new,r,['Remove only appended derived Fits/mass group.','Remove the stated original profile and Fits admission.','Reverse theorem-name extension.'],'Entire prior theorem declaration recovered. The resource extension deliberately adds an ORIGINAL-input profile/Fits admission; it does not add prepared endpoint Fits.'))
old=declaration('SourcePruningEnumerationSelectedOpaqueDispatch','opaque_complete')
new=declaration('SourcePruningEnumerationSelectedOpaqueModels','opaque_complete_models')
r,app=remove_appended_group(new);r=r.replace('theorem opaque_complete_models\n','theorem opaque_complete\n',1)
records.append(write('opaque-models-retains-opaque',old,new,r,['Remove only appended universal semantic observer and its outer group.','Reverse theorem-name extension.'],'Entire original opaque declaration, unchanged admission and actual stable finalization packet; operational witnesses precede all models.'))
old=declaration('SourcePruningEnumerationSelectedValueCaller','complete')
new=declaration('SourcePruningEnumerationSelectedValueResources','complete_resources')
r,app=remove_appended_group(new)
r=r.replace('theorem complete_resources (profile : Profile)\n','theorem complete\n',1)
r=r.replace('(closed : value.free = []) (fits : Fits profile before.checked) :','(closed : value.free = []) :',1)
a=r.index('    ∃ ');e=r.index('\n',a)+1;body=r[e:].splitlines(keepends=True)
r=r[:e]+body[0]+''.join(line[2:] for line in body[1:])
records.append(write('caller-resources-retains-caller',old,new,r,['Remove only appended normalized Fits/result mass and outer group.','Reverse the two-space result-continuation indentation introduced by grouping.','Remove the stated original profile/Fits inputs.','Reverse theorem-name extension.'],'Entire prior Caller.complete declaration recovered; resource input is on the original caller.'))
(out/'comparison.json').write_text(json.dumps({'status':'pass','records':records,'scope_note':'Comparisons are text identities of explicit declarations. They do not assert namespace or implicit instance lists are byte-identical. No Lean execution occurred in this script.'},indent=2)+'\n')
print(json.dumps([(r['id'],r['old_bytes'],r['old_sha256'])for r in records],indent=2))
