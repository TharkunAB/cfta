import ast
import datetime
import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = ROOT / 'lean/restart-evidence/20261023-pair-stable-model-transport'
SOURCE = Path('/tmp/mcfta-pair-stable-model-transport-checkpoint-prep')
PREVIOUS = ROOT / 'lean/restart-evidence/20261023-original-row-reconstruction'
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

assert sha(SOURCE / 'pins.json') == '4334b8d9d90c08d0e4f371dd11a5945a1de4b65564fcfe7bd8de53c6ba750ea5'
assert sha(SOURCE / 'FROZEN.json') == '925fd222241eb1127f3752e433e725faa672b335e098ec05679ff737aa4b3ea9'
pins = json.loads((SOURCE / 'pins.json').read_text())
assert isinstance(pins, list) and len(pins) == 76
for pin in pins:
    path = SOURCE / pin['path']
    assert path.stat().st_size == pin['bytes'] and sha(path) == pin['sha256'], path
scripts = json.loads((SOURCE / 'selected-scripts.json').read_text())
total = assertions = 0
for name, pin in scripts.items():
    path = SOURCE / name
    data = path.read_bytes()
    tree = ast.parse(data)
    assert sha(path) == pin['sha256'] and len(data.splitlines()) == pin['lines']
    assert sum(isinstance(node, ast.Assert) for node in ast.walk(tree)) == pin['assertions']
    assert (SOURCE / 'predecessors' / name).read_bytes() == (PREVIOUS / name).read_bytes()
    total += pin['lines']
    assertions += pin['assertions']
assert len(scripts) == 12 and total == 1005 and assertions == 327
subprocess.run(['/usr/bin/python3', str(HERE / 'archive-extra.py'), str(SOURCE), 'checkpoint-preparation'], check=True)
declaration = HERE / 'root-declaration-review.json'
before = declaration.read_bytes()
assert not (HERE / 'root-declaration-review-before-schema-amendment.json').exists()
(HERE / 'root-declaration-review-before-schema-amendment.json').write_bytes(before)
report = json.loads(before)
assert 'contracts' not in report and report['status'] == 'ROOT_DECLARATION_REVIEW_CLEAR'
contracts = json.loads((HERE / 'signature-plan/contracts.json').read_text())
report['contracts'] = [dict(path=name, lines=pin['lines'], sha256=pin['sha256']) for name, pin in contracts.items()]
declaration.write_text(json.dumps(report, indent=2) + '\n')
amendment = dict(reason='Add the inherited verifier contracts list from the exact accepted two-fragment declaration; no declaration or contract byte changed.',
    before_sha256=hashlib.sha256(before).hexdigest(), after_sha256=sha(declaration),
    contract_sha256=sha(HERE / 'signature-plan/contracts.json'), proof_jobs_added=0)
(HERE / 'root-declaration-schema-amendment.json').write_text(json.dumps(amendment, indent=2) + '\n')
review = dict(status='ROOT_WHOLE_TOOL_SOURCE_CLEAR_PENDING_INDEPENDENT_GATE',
    observed_at=datetime.datetime.now().astimezone().isoformat(),
    scripts=12, lines=total, assertions=assertions, pins_verified=76,
    complete_selected_source_read=True, exact_two_contract_shape_delta_read=True,
    inherited_binding_values_retained_programmatically=True, runner_and_seal_verifier_unchanged=True,
    independent_preparation_review='PENDING', prepared_execution_authorized=False,
    compiler_authorized=False, new_proof_jobs=0)
(HERE / 'root-preparation-read-scope.json').write_text(json.dumps(review, indent=2) + '\n')
print(json.dumps(review))
