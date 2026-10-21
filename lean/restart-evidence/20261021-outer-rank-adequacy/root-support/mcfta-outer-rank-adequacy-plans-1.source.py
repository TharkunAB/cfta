import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
components = []
for name, verifier in [('adequacy-plan', 'verify.py'),
                       ('adequacy-plan-review', 'review-verify.py')]:
    for live in [False, True]:
        command = ['/usr/bin/python3', str(HERE / name / verifier), '--root', str(ROOT)]
        if live:
            command.append('--live')
        result = subprocess.check_output(command, cwd='/', text=True)
        (HERE / (name + ('-live' if live else '-ordinary') + '.json')).write_text(result)
        assert json.loads(result)['status'] == 'PASS'
    components.append({'path': name, 'verifier': verifier,
                       'extra': ['--root', str(ROOT)], 'live': True})
assert not (HERE / 'components.json').exists()
(HERE / 'components.json').write_text(json.dumps(components, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'components': len(components), 'proof_jobs': 0}))
