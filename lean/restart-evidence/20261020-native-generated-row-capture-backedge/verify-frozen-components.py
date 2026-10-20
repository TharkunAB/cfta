import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
subprocess.run([sys.executable, str(HERE / 'prepare-evidence.py')],
               check=True, capture_output=True)
reports = {}
for name in ['backedge-module/generated-row-backedge-verify.py',
             'backedge-core/generated-backedge-verify.py',
             'source-review/math-review-verify.py']:
    report = json.loads(subprocess.check_output(
        [sys.executable, str(HERE / name), '--root', str(ROOT), '--live'], cwd='/'))
    assert report['status'] == 'PASS'
    reports[name] = report
print(json.dumps({'status': 'PASS', 'components': reports}, indent=2))
