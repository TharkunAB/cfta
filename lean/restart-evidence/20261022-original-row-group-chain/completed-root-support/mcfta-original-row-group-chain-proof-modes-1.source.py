import json
import subprocess
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = ROOT / 'lean/restart-evidence/20261022-original-row-group-chain'
for mode, flags in [('normal',[]),('live',['--live'])]:
    result = subprocess.run(['/usr/bin/python3',str(HERE / 'verify-proofs.py'),'--root',str(ROOT),*flags],cwd='/',capture_output=True)
    (HERE / ('standalone-' + mode + '.stdout')).write_bytes(result.stdout)
    (HERE / ('standalone-' + mode + '.stderr')).write_bytes(result.stderr)
    assert result.returncode == 0, result.stderr.decode()
    report = json.loads(result.stdout)
    assert report['status'] == 'PASS' and report['live'] is (mode == 'live')
    assert report['actual_jobs'] == 3 and report['failed_jobs'] == 0
    (HERE / ('proof-evidence-' + mode + '.json')).write_bytes(result.stdout)
    print(json.dumps(report))
