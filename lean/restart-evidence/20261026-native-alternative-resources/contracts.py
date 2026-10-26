from pathlib import Path
import json,hashlib
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-native-alternative-resources-20261026')
contracts={}
for new_module,names in [('SourcePruningEnumerationNativeBranchResources',[('complete_with_history','complete_with_history_resources'),('complete_with_posts','complete_with_posts_resources'),('complete','complete_resources')]),('SourcePruningEnumerationNativeBranchPackets',[('complete_with_history','complete_with_packets_resources')])]:
    for old_name,new_name in names:
        old=(root/'lean/MicroCFTA/SourcePruningEnumerationNativeBranchCompletion.lean').read_text()
        new=(root/'lean/MicroCFTA'/f'{new_module}.lean').read_text()
        old=old[old.index('theorem '+old_name+'\n'):].split(' := by\n',1)[0]
        new=new[new.index('theorem '+new_name+'\n'):].split(' := by\n',1)[0]
        old=old[old.index('    ∃ (r n p h k'):]
        for name in ['Caller','Result','Receipt']:old=old.replace(name+' width',name+' (bits + 2)')
        new=new[new.index('    ∃ (r n p h k'):].split(' ∧\n      Fits (',1)[0]
        assert old==new,(new_module,new_name)
        key=new_module+'.'+new_name
        contracts[key]=dict(earlier_declaration='SourcePruningEnumerationNativeBranchCompletion.'+old_name,retained_characters=len(old),retained_bytes=len(old.encode()),output_sha256=hashlib.sha256(old.encode()).hexdigest())
        (area/(new_name+'-original-output.txt')).write_text(old+'\n')
old=(root/'lean/MicroCFTA/SourcePruningEnumerationNativeBranchResources.lean').read_text()
old=old[old.index('theorem complete_with_history_resources\n'):].split(' := by\n',1)[0]
old=old[old.index('    ∃ (r n p h k'):]
new=(root/'lean/MicroCFTA/SourcePruningEnumerationNativeBranchPackets.lean').read_text()
new=new[new.index('theorem complete_with_packets_resources\n'):].split(' := by\n',1)[0]
new=new[new.index('    ∃ (r n p h k'):].split(' ∧\n      (∀ (metadata',1)[0]
assert old==new,'entire strengthened resource output'
contracts['SourcePruningEnumerationNativeBranchPackets.strengthened_resource_packet']=dict(earlier_declaration='SourcePruningEnumerationNativeBranchCompletion.complete_with_history_resources',retained_characters=len(old),retained_bytes=len(old.encode()),output_sha256=hashlib.sha256(old.encode()).hexdigest())
(area/'strengthened-resource-output.txt').write_text(old+'\n')
p=area/'old-contracts.json'
if p.exists():
    for key,value in json.loads(p.read_text()).items():assert contracts[key]==value
p.write_text(json.dumps(contracts,indent=2)+'\n');print(json.dumps(contracts,indent=2))
