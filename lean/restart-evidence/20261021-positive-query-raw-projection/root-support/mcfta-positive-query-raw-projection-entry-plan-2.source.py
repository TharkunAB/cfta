import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
original = Path('/tmp/mcfta-required-corridor-chronology-entry-plan')
archived = HERE / 'entry-plan'
for source in original.rglob('*'):
    if source.is_file():
        assert source.read_bytes() == (archived / source.relative_to(original)).read_bytes()
for mode in [[], ['--live']]:
    subprocess.run(['/usr/bin/python3', str(archived / 'verify.py'), '--root', str(ROOT), *mode],
                   cwd='/', check=True)
registry = HERE / 'components.json'
items = json.loads(registry.read_text())
assert all(item['path'] != 'entry-plan' for item in items)
items.append({'path': 'entry-plan', 'verifier': 'verify.py', 'extra': ['--root', str(ROOT)], 'live': True})
registry.write_text(json.dumps(items, indent=2) + '\n')
(HERE / 'entry-plan-archive-repair.json').write_text(json.dumps({
    'reason': 'The first archive call used plan-verify.py. This package uses verify.py.',
    'failed_receipt': 'mcfta-positive-query-raw-projection-entry-plan-1.json',
    'archived_bytes_changed': False, 'additional_lean_jobs': 0,
    'status': 'PASS'}, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'component': 'entry-plan'}))
