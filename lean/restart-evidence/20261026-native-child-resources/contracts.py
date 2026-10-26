from pathlib import Path
import json,hashlib
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-native-child-resources-20261026')
contracts={}
for name in ['complete_with_fragments','complete']:
    old=(root/'lean/MicroCFTA/SourcePruningEnumerationChildCompletion.lean').read_text();new=(root/'lean/MicroCFTA/SourcePruningEnumerationChildResources.lean').read_text()
    old=old[old.index('theorem '+name+'\n'):].split(' := by\n',1)[0];new=new[new.index('theorem '+name+'_resources\n'):].split(' := by\n',1)[0]
    old=old[old.index('    ∃ (r n p h k'):].replace('Caller width','Caller (bits + 2)')
    new=new[new.index('    ∃ (r n p h k'):].split(' ∧\n      Fits (',1)[0]
    assert old==new,name
    contracts['SourcePruningEnumerationChildCompletion.'+name]=dict(retained_characters=len(old),output_sha256=hashlib.sha256(old.encode()).hexdigest())
    (area/(name+'-original-output.txt')).write_text(old+'\n')
p=area/'old-contracts.json'
if p.exists():assert json.loads(p.read_text())==contracts
p.write_text(json.dumps(contracts,indent=2)+'\n');print(json.dumps(contracts,indent=2))
