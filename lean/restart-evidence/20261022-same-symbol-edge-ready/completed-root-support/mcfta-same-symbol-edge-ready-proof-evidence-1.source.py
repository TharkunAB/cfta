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
    assert report['status'] == 'PASS' and report['actual_jobs'] == 4 and report['failed_jobs'] == 1
    assert report['source_jobs'] == 3 and report['audit_jobs'] == 1
    assert report['warned_source_exit_zero_jobs'] == 0 and report['rejected_public_type_jobs'] == 0
    assert report['new_lean_lake_jobs'] == 0 and report['audit_build_jobs'] == 3627 and report['audit_dependencies'] == 75377
    print(json.dumps({'mode': label, **report}))
