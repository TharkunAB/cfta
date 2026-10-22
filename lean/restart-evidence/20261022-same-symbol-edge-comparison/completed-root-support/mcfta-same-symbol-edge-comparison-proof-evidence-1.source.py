import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
for mode, label in [([], 'normal'), (['--live'], 'live')]:
    result = subprocess.run(['/usr/bin/python3', str(HERE / 'verify-proofs.py'),
        '--root', str(ROOT), *mode], cwd='/', capture_output=True, text=True)
    (HERE / ('proof-evidence-' + label + '.json')).write_text(result.stdout)
    (HERE / ('proof-evidence-' + label + '.stderr')).write_text(result.stderr)
    assert result.returncode == 0, result.stderr
    report = json.loads(result.stdout)
    assert report['status'] == 'PASS' and report['actual_jobs'] == 3
    assert report['source_jobs'] == 2 and report['audit_jobs'] == 1
    assert report['failed_jobs'] == report['warned_source_exit_zero_jobs'] == report['rejected_public_type_jobs'] == 0
    assert report['audit_build_jobs'] > 0 and report['audit_dependencies'] > 0
print(json.dumps({'status': 'PASS', 'normal_and_live': True, 'actual_proof_jobs': 3,
                  'new_proof_jobs': 0}))
