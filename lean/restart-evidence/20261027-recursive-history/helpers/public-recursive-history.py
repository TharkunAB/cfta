from pathlib import Path
import hashlib,json,re
area=Path('/tmp/mcfta-recursive-history-20261027')
raw=(area/'public-readback-final/raw.log').read_bytes()
s=raw.decode()
declarations=json.loads((area/'public-declarations.json').read_text())
axioms=re.findall(r"'MicroCFTA\.([^']+)' depends on axioms: \[([^]]*)\]",s,re.S)
assert [name for name,_ in axioms]==declarations
used={a.strip() for _,ls in axioms for a in ls.split(',')}
assert used=={'propext','Classical.choice','Quot.sound'}
assert '...' not in s and '⋯' not in s and '…' not in s
assert len(re.findall(r'^MicroCFTA\.',s,re.M))==len(declarations)==14
old=(area/'prior-public-readback/raw.log').read_text()
def block(content,name):
    start=re.search(r'^MicroCFTA\.'+re.escape(name)+r'(?=\s|$)',content,re.M).start()
    end=content.index("'MicroCFTA."+name+"' depends on axioms:",start)
    return content[start:end]
for name in declarations[-3:]:
    assert block(s,name)==block(old,name),name
definitions=json.loads((area/'public-definitions.json').read_text())
assert re.findall(r'^def MicroCFTA\.([^ ]+) :',s,re.M)==definitions
report={'status':'pass','theorem_signatures_and_axiom_checks':14,'definitions':3,'axioms':sorted(used),'no_elision':True,'unchanged_prior_signatures':declarations[-3:],'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()}
(area/'public-validation.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
