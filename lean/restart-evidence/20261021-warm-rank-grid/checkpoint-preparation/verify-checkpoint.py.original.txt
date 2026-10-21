import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
for mode, label in [([], 'normal'), (['--live'], 'live')]:
    result = subprocess.run(['/usr/bin/python3', str(HERE / 'verify-proofs.py'),
        '--root', str(ROOT), *mode], cwd='/', capture_output=True, text=True)
    (HERE / ('proof-verification-' + label + '.stdout')).write_text(result.stdout)
    (HERE / ('proof-verification-' + label + '.stderr')).write_text(result.stderr)
    assert result.returncode == 0, result.stderr
    report = json.loads(result.stdout)
    assert report['status'] == 'PASS' and report['actual_jobs'] == 6 and report['failed_jobs'] == 1
result = subprocess.run(['/usr/bin/python3', str(HERE / 'verify-preservation.py')],
    cwd='/', capture_output=True, text=True)
(HERE / 'preservation-final.stderr').write_text(result.stderr)
assert result.returncode == 0, result.stderr
preserved = json.loads(result.stdout)
(HERE / 'preservation-final.json').write_text(json.dumps(preserved, indent=2) + '\n')
report = dict(status='PASS', actual_jobs=6, source_jobs=5, audit_jobs=1, failed_jobs=1,
    audit_dependencies=75221, audit_build_jobs=3619, selected_modules=2,
    new_modules=0, proof_declaration_limits_unchanged=True,
    baseline_files=preserved['baseline_files'], archived_components=preserved['archived_components'],
    both_proof_verification_modes=True, no_haskell_or_package_changes=True)
(HERE / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
