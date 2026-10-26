from pathlib import Path
import json,hashlib,re
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-native-prefix-resources-20261026')
norm=lambda s: re.sub(r'\s+','',s.replace('SourcePruningEnumerationSelectedStep.',''))
old=(root/'lean/MicroCFTA/SourcePruningEnumerationRecursiveCallback.lean').read_text().split('theorem callback_prefix_complete\n',1)[1].split(' := by',1)[0].split('    ∃ fuel result after,\n',1)[1]
new=(root/'lean/MicroCFTA/SourcePruningEnumerationCallbackResources.lean').read_text().split('theorem callback_prefix_complete_resources\n',1)[1].split(' := by',1)[0].split('    ∃ fuel result after,\n      (',1)[1].split(') ∧\n      (∀ extra, result.1 = false',1)[0]
assert norm(old)==norm(new)
contracts={'callback_complete_entire_output':dict(retained_characters=len(norm(old)),sha256=hashlib.sha256(norm(old).encode()).hexdigest())}
(area/'old-callback-output.txt').write_text(old+'\n')
old=(root/'lean/MicroCFTA/SourcePruningEnumerationRecursivePrefix.lean').read_text().split('theorem packet_prefix_complete ',1)[1].split(' := by',1)[0].split('    ∃ bound,',1)[1]
new=(root/'lean/MicroCFTA/SourcePruningEnumerationPrefixResources.lean').read_text().split('theorem packet_prefix_complete_resources\n',1)[1].split(' := by',1)[0].split('    ∃ bound,',1)[1]
prefix,rest=new.split('      let observed := ',1)
call,rest=rest.split('\n      PrefixValid',1)
valid=rest.split(' ∧\n      Resources',1)[0]
retained=prefix+'      PrefixValid'+valid.replace('observed','('+call+')')
assert norm(old)==norm(retained),(norm(old),norm(retained))
contracts['prefix_complete_entire_output']=dict(retained_characters=len(norm(old)),sha256=hashlib.sha256(norm(old).encode()).hexdigest())
(area/'old-prefix-output.txt').write_text(old+'\n')
(area/'old-contracts.json').write_text(json.dumps(contracts,indent=2)+'\n')
print(json.dumps(contracts,indent=2))
