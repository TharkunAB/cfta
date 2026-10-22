import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
for flags, label in [([], 'normal'), (['--live'], 'live')]:
    target = HERE / ('proof-evidence-' + label + '.json')
    errors = HERE / ('proof-evidence-' + label + '.stderr')
    assert not target.exists() and not errors.exists()
    result = subprocess.run(['/usr/bin/python3', str(HERE / 'verify-proofs.py'),
        '--root', str(ROOT), *flags], cwd='/', capture_output=True, text=True)
    target.write_text(result.stdout)
    errors.write_text(result.stderr)
    assert result.returncode == 0, result.stderr
    report = json.loads(result.stdout)
    assert report['status'] == 'PASS' and report['actual_jobs'] == 5 and report['failed_jobs'] == 2
    assert report['audit_build_jobs'] == 3625 and report['audit_dependencies'] == 75347
    print(json.dumps({'mode': label, **report}))
