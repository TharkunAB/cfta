from pathlib import Path
import json,hashlib
repo=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA');own=Path('/tmp/mcfta-prepared-composition-20261028/selector-admission');area=own.parent
def declaration(path,name):
 s=path.read_text();i=s.index('theorem '+name);j=s.index(' := by',i);return s[i:j]
def inverse(text,new,old,prepared):
 text=text.replace('theorem '+new,'theorem '+old,1)
 marker='\n      ∀ (whole : Language.Term Symbol) (assignment : Nat → Language.Term Symbol),'
 a,b=text.rsplit(marker,1);assert a.endswith(') ∧');text=a[:-len(') ∧')]
 left='      (((PrefixValid' if prepared else '      ((PrefixValid'
 right='      ((PrefixValid' if prepared else '      (PrefixValid'
 assert text.count(left)==1;text=text.replace(left,right,1)
 if prepared:
  marker='\n            ∀ (whole : Language.Term Symbol) (assignment : Nat → Language.Term Symbol),'
  a,b=text.split(marker,1);assert a.endswith(') ∧');a=a[:-len(') ∧')]
  i=b.index('\n    | _ => True');text=a+b[i:]
  left='            (((((∀ extra,';right='            ((((∀ extra,'
  assert text.count(left)==1;text=text.replace(left,right,1)
 return text
records=[]
for newFile,oldFile,newName,oldName,prepared in [
 ('SourcePruningEnumerationPrefixCheckpointOrigins','SourcePruningEnumerationPrefixCheckpointModels','packet_prefix_complete_resources_origins','packet_prefix_complete_resources_models',False),
 ('SourcePruningEnumerationPreparedPrefixOrigins','SourcePruningEnumerationPreparedPrefixModels','packet_prefix_preparation_complete_origins','packet_prefix_preparation_complete_models',True)]:
 new=declaration(repo/(newFile+'.lean'),newName);old=declaration(repo/(oldFile+'.lean'),oldName)
 recovered=inverse(new,newName,oldName,prepared);assert recovered==old
 stem='prepared-prefix' if prepared else 'prefix';out=own/'contracts/prefix'/f'{stem}-strict-boundary-recovered.txt';out.write_text(recovered)
 rec={'new_source':str(repo/(newFile+'.lean')),'new_theorem':newName,'old_source':str(repo/(oldFile+'.lean')),'old_theorem':oldName,'old_declaration_bytes':len(old.encode()),'old_declaration_sha256':hashlib.sha256(old.encode()).hexdigest(),'exact_recovery':True,'parentheses_policy':'Delete only exact new observer suffixes and their four designated boundary parentheses. No global parentheses erasure; retain all old internal conjunction grouping.'}
 if prepared:
  bad=declaration(area/'prefix-origins/drafts/v1'/(newFile+'.lean'),newName)
  try:badRecovered=inverse(bad,newName,oldName,True)
  except (AssertionError,ValueError):badRecovered=None
  assert badRecovered!=old;rec['failed_v1_rejected_by_strict_inverse']=True
 records.append(rec)
(own/'contracts/prefix/strict-boundary-retention.json').write_text(json.dumps({'status':'PASS','records':records,'scope':'Source grouping check; actual final printed Lean grouping is reviewed separately.'},indent=2)+'\n')
print(json.dumps(records,indent=2))
