from pathlib import Path
import hashlib,json
here=Path(__file__).resolve().parent
source=(here/'SourceCurrentOlderOwnerLineage.lean').read_text()
proposal=(here/'inputs/plan/proposed-signature.lean.txt').read_text()
header=source.split('theorem body_rank_lt\n',1)[1].split('\n := by',1)[0]
expected=proposal.split('theorem body_rank_lt\n',1)[1].split('\n\nend MicroCFTA.',1)[0]
assert header==expected
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
head='MicroCFTA.SourceCurrentOlderOwnerLineage.body_rank_lt'
full+='#check @'+head+'\n#print '+head+'\n#print axioms '+head+'\n'
(here/'older-owner-lineage-public.lean').write_text(full)
print(json.dumps({'status':'PASS','source_sha256':hashlib.sha256(source.encode()).hexdigest(),'public_header_byte_exact_old_frozen_proposal':True}))
