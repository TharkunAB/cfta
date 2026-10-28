from pathlib import Path
import hashlib,json,difflib
base=Path('/tmp/mcfta-prepared-composition-20261028/prefix-origins')
repo=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA')
def dec(t,name):
 start=t.index('theorem '+name)
 return t[start:t.index(' := by',start)]
def ident(data):return {'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
def check(label,oldname,newname,oldfile,newfile,remove):
 original=dec(oldfile.read_text(),oldname)
 actual=dec(newfile.read_text(),newname)
 recovered=remove(actual.replace(newname,oldname,1))
 if original!=recovered:
  raise AssertionError(''.join(difflib.unified_diff(original.splitlines(True),recovered.splitlines(True))))
 (base/'contracts'/f'{label}-recovered-final-declaration.txt').write_text(recovered)
 (base/'contracts'/f'{label}-old-final-declaration.txt').write_text(original)
 body=newfile.read_text().split(' := by',1)[1] if label=='prepared-prefix' else newfile.read_text().split('theorem '+newname,1)[1].split(' := by',1)[1]
 assert body.count(':= '+oldname+'\n')==1,body
 report={'status':'PASS','old_source':str(oldfile),'new_source':str(newfile),'whole_old_declaration':ident(original.encode()),'whole_new_declaration':ident(actual.encode()),'recovered':ident(recovered.encode()),'recovery':'Direct inverse from actual new declaration. Restore theorem name; remove only appended AssignmentOrigins iff groups and their outer grouping parentheses.','original_producer_calls':1,'new_operational_admissions':0,'same_assignment_and_actual_witnesses':True}
 (base/'contracts'/f'{label}-final-comparison.json').write_text(json.dumps(report,indent=2)+'\n')
 return report

def prefix(t):
 s='''          | _ => False) ∧
      ∀ (whole : Language.Term Symbol) (assignment : Nat → Language.Term Symbol),
        match observed with
        | .parked _ (some after) _ | .narrowed _ _ _ _ _ (some after) _ _ =>
            SourcePruningEnumerationOrigins.AssignmentOrigins whole after.core.counter assignment ↔
              SourcePruningEnumerationOrigins.AssignmentOrigins whole before.core.counter assignment
        | _ => True'''
 assert t.count(s)==1
 return t.replace(s,'          | _ => False',1).replace('      ((PrefixValid','      (PrefixValid',1)

def preparation(t):
 end='''    | _ => True) ∧
      ∀ (whole : Language.Term Symbol) (assignment : Nat → Language.Term Symbol),
        match observed with
        | .parked _ (some after) _ | .narrowed _ _ _ _ _ (some after) _ _ =>
            SourcePruningEnumerationOrigins.AssignmentOrigins whole after.core.counter assignment ↔
              SourcePruningEnumerationOrigins.AssignmentOrigins whole before.core.counter assignment
        | _ => True'''
 inner='''            ambient result (assignment selected)) ∧
            ∀ (whole : Language.Term Symbol) (assignment : Nat → Language.Term Symbol),
              SourcePruningEnumerationOrigins.AssignmentOrigins whole entered.core.counter assignment ↔
                SourcePruningEnumerationOrigins.AssignmentOrigins whole before.core.counter assignment'''
 assert t.count(end)==1 and t.count(inner)==1
 t=t.replace(end,'    | _ => True',1).replace(inner,'            ambient result (assignment selected)',1)
 t=t.replace('      (((PrefixValid','      ((PrefixValid',1)
 t=t.replace('            (((((∀ extra','            ((((∀ extra',1)
 return t
reports=[check('prefix','packet_prefix_complete_resources_models','packet_prefix_complete_resources_origins',repo/'SourcePruningEnumerationPrefixCheckpointModels.lean',base/'drafts/v3/SourcePruningEnumerationPrefixCheckpointOrigins.lean',prefix),check('prepared-prefix','packet_prefix_preparation_complete_models','packet_prefix_preparation_complete_origins',repo/'SourcePruningEnumerationPreparedPrefixModels.lean',base/'drafts/v2/SourcePruningEnumerationPreparedPrefixOrigins.lean',preparation)]
print(json.dumps(reports,indent=2))
