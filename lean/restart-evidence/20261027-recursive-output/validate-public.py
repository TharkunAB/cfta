from pathlib import Path
import hashlib
import json
import re

area = Path('/tmp/mcfta-recursive-output-20261027')
data = (area / 'public-readback/raw.log').read_bytes()
raw = data.decode()
entries = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", raw, re.S)
assert len(entries) == 31
for declaration, names in entries:
    assert set(re.split(r',\s*', names.strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}, declaration
assert not any(marker in raw for marker in ['…', '⋯', 'error:', 'warning:'])
report = {'status': 'pass', 'theorem_signatures_and_axiom_checks': 31,
    'definitions': 8, 'axioms': ['propext', 'Classical.choice', 'Quot.sound'],
    'no_elision': True, 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}
(area / 'public-validation.json').write_text(json.dumps(report, indent=2) + '\n')
index = {str(path.parent.relative_to(area)): json.loads(path.read_text())
    for path in area.glob('*/report.json')
    if path.parent.name.startswith(('strict-', 'build-', 'public-'))}
(area / 'check-index.json').write_text(json.dumps(index, indent=2) + '\n')
print(json.dumps(report))
