from pathlib import Path
import hashlib,json
here=Path(__file__).resolve().parent
source=(here/'SourceCurrentOuterPrefixNativeStores.lean').read_text()
proposal=(here/'inputs/plan/proposed-signature.lean.txt').read_text()
assert source.split('theorem reached\n',1)[1].split(' := by',1)[0]==proposal.split('theorem reached\n',1)[1].split('\nend MicroCFTA.',1)[0]
full=source+"""\nset_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
"""
head='MicroCFTA.SourceCurrentOuterPrefixNativeStores.reached'
full+='#check @'+head+'\n#print '+head+'\n#print axioms '+head+'\n'
(here/'prefix-native-stores-public.lean').write_text(full)
print(json.dumps({'status':'PASS','source_sha256':hashlib.sha256(source.encode()).hexdigest(),'public_type_matches_frozen_plan':True}))
