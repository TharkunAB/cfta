from pathlib import Path
import hashlib,json,re
area=Path('/tmp/mcfta-prepared-recursive-20261028')
def digest(b):return hashlib.sha256(b).hexdigest()
folder=area/'public-readback-final';raw=(folder/'raw.log').read_bytes();receipt=json.loads((folder/'report.json').read_text());assert receipt['exit_code']==0
assert receipt['bytes']==len(raw) and receipt['sha256']==digest(raw)
assert receipt['source_sha256']==digest((folder/'public.lean').read_bytes())
assert receipt['cgroup_limits']=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
content=raw.decode();declarations=json.loads((area/'public-declarations.json').read_text());prior=(area/'prior-public-readback/raw.log').read_bytes();assert raw.startswith(prior)
axioms=re.findall(r"'MicroCFTA\.([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",content,re.S);assert [n for n,_ in axioms]==declarations
used={x.strip() for _,items in axioms for x in items.split(',') if x.strip()};assert used=={'propext','Classical.choice','Quot.sound'}
assert not any(m in content for m in ['...','⋯','…'])
definitions=json.loads((area/'public-definitions.json').read_text());printed=[n.split('.{',1)[0] for n in re.findall(r'^(?:def|inductive|structure) MicroCFTA\.([^\s:]+)',content,re.M)];assert printed==definitions
new=raw[len(prior):];(area/'new-public-blocks.txt').write_bytes(new)
report=dict(status='pass',theorem_signatures_and_axiom_checks=len(declarations),new_public_theorems=len(json.loads((area/'new-public-declarations.json').read_text())),printed_public_definitions=len(definitions),new_definitions=len(definitions)-len(json.loads((area/'prior-public-definitions.json').read_text())),axioms=sorted(used),no_elision=True,exact_prior_prefix=True,prior_bytes=len(prior),bytes=len(raw),sha256=digest(raw),new_bytes=len(new),new_sha256=digest(new))
(area/'public-validation.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
