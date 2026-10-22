import json
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
here = root / 'lean/restart-evidence/20261023-original-row-reconstruction'
for label, arguments in [('normal', []), ('live', ['--live'])]:
    result = subprocess.run(['/usr/bin/python3', str(here / 'verify-proofs.py'),
        '--root', str(root), *arguments], cwd='/', capture_output=True, text=True)
    for suffix, text in [('stdout', result.stdout), ('stderr', result.stderr)]:
        path = here / ('proof-evidence-' + label + '.' + suffix)
        assert not path.exists()
        path.write_text(text)
    assert result.returncode == 0, result.stderr
    report = json.loads(result.stdout)
    assert report['status'] == 'PASS' and report['live'] is (label == 'live')
    assert report['actual_jobs'] == 4 and report['source_jobs'] == 3 and report['audit_jobs'] == 1
    assert report['failed_jobs'] == 1 and report['warned_source_exit_zero_jobs'] == 0
    assert report['rejected_public_type_jobs'] == 0
    assert report['audit_build_jobs'] == 3640 and report['audit_dependencies'] == 75501
    path = here / ('proof-evidence-' + label + '.json')
    assert not path.exists()
    path.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(dict(mode=label, report=report)))
