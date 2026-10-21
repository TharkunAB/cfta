from pathlib import Path
import hashlib
import json

here = Path(__file__).resolve().parent
source = (here / 'SourceCurrentOuterClosedInputs.lean').read_text()
full = source + '''
set_option maxRecDepth 30000
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
heads = ['NodeStored', 'InputsClosed', 'initial', 'reached']
namespace = 'MicroCFTA.SourceCurrentOuterClosedInputs.'
for head in heads:
    name = namespace + head
    full += '#check @' + name + '\n#print ' + name + '\n#print axioms ' + name + '\n'
target = here / 'outer-closed-inputs-public.lean'
assert not target.exists()
target.write_text(full)
print(json.dumps({'source_sha256': hashlib.sha256(source.encode()).hexdigest(), 'heads': heads}))
