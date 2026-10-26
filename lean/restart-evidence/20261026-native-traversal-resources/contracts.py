from pathlib import Path
import json,hashlib
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-native-traversal-resources-20261026')
contracts={}
for old_module,new_module,names in [
    ('SourcePruningEnumerationTraversalCompletion','SourcePruningEnumerationTraversalResources',['complete_with_fragments','complete']),
    ('SourcePruningEnumerationSelectedEdge','SourcePruningEnumerationSelectedEdgeResources',['complete_with_fragments','complete']),
    ('SourcePruningEnumerationCapturedEdge','SourcePruningEnumerationCapturedEdgeResources',['complete_with_history','complete'])]:
    for name in names:
        old=(root/'lean/MicroCFTA'/f'{old_module}.lean').read_text();new=(root/'lean/MicroCFTA'/f'{new_module}.lean').read_text()
        old=old[old.index('theorem '+name+'\n'):].split(' := by\n',1)[0];new=new[new.index('theorem '+name+'_resources\n'):].split(' := by\n',1)[0]
        old=old[old.index('    ∃ (r n p h k'):].replace('Caller width','Caller (bits + 2)').replace('Result width','Result (bits + 2)')
        new=new[new.index('    ∃ (r n p h k'):].split(' ∧\n      Fits (',1)[0]
        assert old==new,(old_module,name)
        contracts[old_module+'.'+name]=dict(retained_characters=len(old),retained_bytes=len(old.encode()),output_sha256=hashlib.sha256(old.encode()).hexdigest())
        (area/(old_module+'.'+name+'-original-output.txt')).write_text(old+'\n')
p=area/'old-contracts.json'
previous=json.loads(p.read_text()) if p.exists() else {}
for name,info in previous.items():
    for key,value in info.items():assert contracts[name][key]==value
p.write_text(json.dumps(contracts,indent=2)+'\n');print(json.dumps(contracts,indent=2))
