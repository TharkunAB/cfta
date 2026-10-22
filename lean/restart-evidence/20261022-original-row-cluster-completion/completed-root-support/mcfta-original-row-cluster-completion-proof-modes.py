import json
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
here = root / 'lean/restart-evidence/20261022-original-row-cluster-completion'
assert json.loads((here / 'root-tool-binding-review.json').read_text())['status'] == 'ROOT_ACCEPTED_FOR_SAVED_METADATA_WORKFLOW'
for label, extra in [('normal', []), ('live', ['--live'])]:
    target = here / ('proof-evidence-' + label + '.json')
    assert not target.exists()
    result = subprocess.run(['/usr/bin/python3', str(here / 'verify-proofs.py'), '--root', str(root), *extra],
        cwd='/', capture_output=True, text=True)
    (here / ('proof-evidence-' + label + '.stdout')).write_text(result.stdout)
    (here / ('proof-evidence-' + label + '.stderr')).write_text(result.stderr)
    assert result.returncode == 0, result.stderr
    report = json.loads(result.stdout)
    assert report['status'] == 'PASS' and report['actual_jobs'] == 5 and report['failed_jobs'] == 2
    target.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(dict(status='PASS', modes=['normal', 'live'], new_lean_lake_jobs=0)))
