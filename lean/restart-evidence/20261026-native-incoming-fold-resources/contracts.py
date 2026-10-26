from pathlib import Path
import json,hashlib
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-native-incoming-fold-resources-20261026')
contracts={}
for module,newmodule in [('SourcePruningEnumerationCachedDispatch','SourcePruningEnumerationDispatchResources'),('SourcePruningEnumerationCachedFoldCompletion','SourcePruningEnumerationCachedFoldResources')]:
    old=(root/'lean/MicroCFTA'/f'{module}.lean').read_text();new=(root/'lean/MicroCFTA'/f'{newmodule}.lean').read_text()
    old=old[old.index('theorem complete\n'):].split(' := by\n',1)[0];new=new[new.index('theorem complete_resources\n'):].split(' := by\n',1)[0]
    old=old[old.index('    ∃ (fuel p h'):].replace('Caller width','Caller (bits + 2)').replace('Checked width','Checked (bits + 2)')
    new=new[new.index('    ∃ (fuel p h'):].split(' ∧\n      Fits (',1)[0]
    assert old==new,module
    contracts[module]=dict(retained_characters=len(old),output_sha256=hashlib.sha256(old.encode()).hexdigest())
    (area/(module+'-original-output.txt')).write_text(old+'\n')
p=area/'old-contracts.json'
if p.exists():assert json.loads(p.read_text())==contracts
p.write_text(json.dumps(contracts,indent=2)+'\n');print(json.dumps(contracts,indent=2))
