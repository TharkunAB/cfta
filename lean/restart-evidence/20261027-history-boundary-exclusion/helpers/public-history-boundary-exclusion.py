from pathlib import Path
import hashlib
import json
import re

area = Path('/tmp/mcfta-history-boundary-exclusion-20261027')
raw = (area / 'public-readback-final-1/raw.log').read_bytes()
receipt = json.loads((area / 'public-readback-final-1/report.json').read_text())
assert receipt['exit_code'] == 0
assert receipt['bytes'] == len(raw) and receipt['sha256'] == hashlib.sha256(raw).hexdigest()
assert receipt['source_sha256'] == hashlib.sha256((area / 'public-readback-final-1/public.lean').read_bytes()).hexdigest()
assert receipt['cgroup_limits'] == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
content = raw.decode()
declarations = json.loads((area / 'public-declarations.json').read_text())
axioms = re.findall(r"'MicroCFTA\.([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", content, re.S)
assert [name for name, _ in axioms] == declarations
used = {item.strip() for _, items in axioms for item in items.split(',') if item.strip()}
assert used == {'propext', 'Classical.choice', 'Quot.sound'}
assert not any(marker in content for marker in ['...', '⋯', '…'])
signatures = content.split('\ndef MicroCFTA.', 1)[0]
assert len(re.findall(r'^MicroCFTA\.', signatures, re.M)) == len(declarations)
prior = (area / 'prior-public-readback/raw.log').read_text()


def block(text, name):
    start = re.search(r'^MicroCFTA\.' + re.escape(name) + r'(?=\s|$)', text, re.M).start()
    end = text.index("'MicroCFTA." + name + "' depends on axioms:", start)
    return text[start:text.index(']', end) + 1]


for name in declarations[-3:]:
    assert block(content, name) == block(prior, name), name
definitions = json.loads((area / 'public-definitions.json').read_text())
printed = re.findall(r'^(?:def|inductive|structure) MicroCFTA\.([^\s:]+)', content, re.M)
printed = [name.split(".{", 1)[0] for name in printed]
assert printed == definitions, printed
report = {'status': 'pass', 'theorem_signatures_and_axiom_checks': len(declarations),
    'new_public_theorems': len(declarations) - 3, 'printed_data_declarations': len(definitions),
    'axioms': sorted(used), 'no_elision': True, 'unchanged_prior_signatures': declarations[-3:],
    'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}
(area / 'public-validation.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
