import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
mode = sys.argv[1]
assert mode in {'normal', 'live'}
arguments = ['--live'] if mode == 'live' else []
result = subprocess.run(['/usr/bin/python3', str(HERE / 'verify-proofs.py'),
    '--root', str(ROOT), *arguments], cwd='/', capture_output=True, text=True)
for suffix, value in [('stdout', result.stdout), ('stderr', result.stderr)]:
    target = HERE / ('proof-verification-' + mode + '-initial.' + suffix)
    assert not target.exists()
    target.write_text(value)
assert result.returncode == 0, result.stderr
report = json.loads(result.stdout)
assert report['status'] == 'PASS' and report['actual_jobs'] == 5
assert report['failed_jobs'] == 0 and report['rejected_public_type_jobs'] == 1
print(json.dumps(report))
