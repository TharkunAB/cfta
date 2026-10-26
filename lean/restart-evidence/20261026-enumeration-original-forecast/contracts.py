from pathlib import Path
import hashlib,json,re
root=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA'); area=Path('/tmp/mcfta-enumeration-original-forecast-20261026')
def signature(file, name):
    text=(root/file).read_text(); a=text.index('theorem '+name); return text[a:text.index(' := by',a)]
def normal(text): return re.sub(r'\s+','',text)
old=signature('SourcePruningEnumerationOrdinaryHookResources.lean','ordinary_zero_complete_resources')
new=signature('SourcePruningEnumerationOrdinaryForecastResources.lean','ordinary_zero_complete_forecast')
old=old[old.index('      (∀ extra, ExceptT.run'):].strip()
a=new.index('      ((∀ extra, ExceptT.run')+7
new=new[a:new.index(') ∧\n      cost scs',a)]
assert old==new
pairs={'ordinary':(old,new)}
old=signature('SourcePruningEnumerationPrefixResources.lean','packet_prefix_complete_resources')
new=signature('SourcePruningEnumerationExpansionAdmission.lean','packet_prefix_complete_reservation')
old=old[old.index('      PrefixValid'):].strip()
old=old.replace('Resources profile property','Resources seed.2 (fun guard => guard ∈ seed.1)')
a=new.index('      (PrefixValid')+7
new=new[a:new.index(') ∧\n      (match observed',a)]
new=new.replace('SourcePruningEnumerationSelectedStep.Resources','Resources')
assert normal(old)==normal(new)
pairs['prefix']=(old,new)
old=signature('SourcePruningEnumerationPrefixAdmission.lean','narrowed_admission')
new=signature('SourcePruningEnumerationExpansionAdmission.lean','narrowed_ordinary_reservation')
a=old.index('          Post formulas');old=old[a:old.index('\n    | _ => True',a)].strip()
old=old.replace('suspendedBound','SourcePruningEnumerationPrefixAdmission.suspendedBound').replace('headProfile profile','headProfile seed.2').replace('Heap property','Heap (fun guard => guard ∈ seed.1)')
a=new.index('          (Post formulas')+11
new=new[a:new.index(') ∧\n          ∀ entry',a)]
assert normal(old)==normal(new)
pairs['admission']=(old,new)
folder=area/'contract-evidence';folder.mkdir(exist_ok=True)
report={}
for label,(old,new) in pairs.items():
    norm=normal(old);report[label]={'characters':len(norm),'bytes':len(norm.encode()),'sha256':hashlib.sha256(norm.encode()).hexdigest(),'exact_without_whitespace':True,'byte_identical_before_normalization':old==new}
    (folder/(label+'-earlier.txt')).write_text(old+'\n');(folder/(label+'-retained.txt')).write_text(new+'\n')
(folder/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
