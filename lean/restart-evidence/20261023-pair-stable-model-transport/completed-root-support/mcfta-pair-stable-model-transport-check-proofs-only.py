import json
import subprocess
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = ROOT / 'lean/restart-evidence/20261023-pair-stable-model-transport'
for label, flags in [('normal', []), ('live', ['--live'])]:
    result = subprocess.run(['/usr/bin/python3', str(HERE / 'verify-proofs.py'), '--root', str(ROOT), *flags],
        cwd='/', capture_output=True, text=True)
    for suffix, value in [('stdout', result.stdout), ('stderr', result.stderr)]:
        path = HERE / ('proof-evidence-' + label + '.' + suffix)
        assert not path.exists()
        path.write_text(value)
    assert result.returncode == 0, result.stderr
    report = json.loads(result.stdout)
    assert report['status'] == 'PASS' and report['live'] is (label == 'live')
    assert report['actual_jobs'] == 3 and report['source_jobs'] == 2 and report['audit_jobs'] == 1
    assert report['failed_jobs'] == report['warned_source_exit_zero_jobs'] == report['rejected_public_type_jobs'] == 0
    assert report['audit_build_jobs'] == 3641 and report['audit_dependencies'] == 75502
    path = HERE / ('proof-evidence-' + label + '.json')
    assert not path.exists()
    path.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(dict(mode=label, report=report)))
