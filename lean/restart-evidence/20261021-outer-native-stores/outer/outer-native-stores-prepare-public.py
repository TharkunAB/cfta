from pathlib import Path
import json,hashlib
here=Path(__file__).resolve().parent
source=(here/'SourceCurrentOuterNativeStores.lean').read_text()
audit=(here/'inputs/proposed-signature.lean.txt').read_text()
heads=['edge_call','node_call','descendants']
for name in heads:
    actual='theorem '+name+'\n'+source.split('theorem '+name+'\n',1)[1].split(' := by',1)[0]
    expected=('theorem '+name+'\n'+audit.split('theorem '+name+'\n',1)[1]).split('\n\n',1)[0].split('\nend MicroCFTA.',1)[0].rstrip()
    assert actual==expected,name
full=source+'''\nset_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
'''
for name in heads:
    head='MicroCFTA.SourceCurrentOuterNativeStores.'+name
    full+='#check @'+head+'\n#print '+head+'\n#print axioms '+head+'\n'
(here/'outer-native-stores-public.lean').write_text(full)
print(json.dumps({'status':'PASS','public_headers_match_proposal':True,'source_sha256':hashlib.sha256(source.encode()).hexdigest()}))
