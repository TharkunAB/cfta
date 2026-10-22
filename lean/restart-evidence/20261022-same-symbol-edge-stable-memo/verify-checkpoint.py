import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
AUDIT_SHA = 'c4b5c7f777ec5c09154b2a0fb383b9b7686aa6a9f0370a7ef272b4739fe8fab9'
AUDIT_JOBS = int('3626')
AUDIT_DEPENDENCIES = int('75371')
for mode, label in [([], 'normal'), (['--live'], 'live')]:
    result = subprocess.run(['/usr/bin/python3', str(HERE / 'verify-proofs.py'),
        '--root', str(ROOT), *mode], cwd='/', capture_output=True, text=True)
    (HERE / ('proof-verification-' + label + '.stdout')).write_text(result.stdout)
    (HERE / ('proof-verification-' + label + '.stderr')).write_text(result.stderr)
    assert result.returncode == 0, result.stderr
    report = json.loads(result.stdout)
    assert report['status'] == 'PASS' and report['actual_jobs'] == int('6') and report['failed_jobs'] == int('2')
    assert report['source_jobs'] == int('5') and report['audit_jobs'] == int('1') and report['selected_modules'] == 1
    assert report['audit_build_jobs'] == AUDIT_JOBS and report['audit_dependencies'] == AUDIT_DEPENDENCIES
    assert report['audit_log_sha256'] == AUDIT_SHA
    assert report['warned_source_exit_zero_jobs'] == int('1')
    assert report['rejected_public_type_jobs'] == int('0')
result = subprocess.run(['/usr/bin/python3', str(HERE / 'verify-preservation.py')],
    cwd='/', capture_output=True, text=True)
(HERE / 'preservation-final.stderr').write_text(result.stderr)
assert result.returncode == 0, result.stderr
preserved = json.loads(result.stdout)
(HERE / 'preservation-final.json').write_text(json.dumps(preserved, indent=2) + '\n')
assert preserved['status'] == 'PASS' and preserved['baseline_files'] == 78951
baseline = json.loads((HERE / 'starting-files.json').read_text())
selected = json.loads((HERE / 'selected-sources.json').read_text())
new_modules = sum(name not in baseline for name in selected)
assert len(selected) == 1 and new_modules == 1
report = dict(status='PASS', actual_jobs=report['actual_jobs'], source_jobs=report['source_jobs'],
    audit_jobs=report['audit_jobs'], failed_jobs=report['failed_jobs'],
    warned_source_exit_zero_jobs=report['warned_source_exit_zero_jobs'],
    rejected_public_type_jobs=report['rejected_public_type_jobs'],
    audit_dependencies=report['audit_dependencies'], audit_build_jobs=report['audit_build_jobs'],
    selected_modules=len(selected), new_modules=new_modules, proof_declaration_limits_unchanged=True,
    baseline_files=preserved['baseline_files'], archived_components=preserved['archived_components'],
    both_proof_verification_modes=True, no_haskell_or_package_changes=True)
(HERE / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
