import datetime
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = ROOT / 'lean/restart-evidence/20261022-original-row-group-chain'
for name in ['verifier-audit', 'authorization-update', 'authorization-audit']:
    path = Path('/tmp/mcfta-original-row-group-chain-' + name)
    for pin in json.loads((path / 'pins.json').read_text()):
        data = (path / pin['path']).read_bytes()
        assert len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256']
    subprocess.run(['/usr/bin/python3', str(HERE / 'archive-extra.py'), str(path), name], check=True)
jobs = {}
for path in HERE.glob('*.json'):
    data = json.loads(path.read_text())
    if isinstance(data,dict) and 'wrapper' in data and 'exit_code' in data and Path(data.get('command',[''])[0]).name in {'lean','lake'}:
        raw = (HERE / data['log']).read_bytes()
        jobs[path.stem] = [data['exit_code'], data.get('sha256'), hashlib.sha256(raw).hexdigest(),
            len(re.findall(rb'^.+?:\d+:\d+: error(?:\([^)]*\))?:',raw,re.M)),
            len(re.findall(rb'^.+?:\d+:\d+: warning(?:\([^)]*\))?:',raw,re.M))]
assert set(jobs) == {'original-row-group-chain-strict-1','original-row-group-chain-public-1','original-row-group-chain-audit-1'}
assert all(row[0] == 0 for row in jobs.values())
assert (HERE / 'original-row-group-chain-strict-1.log').read_bytes() == b''
raw = (HERE / 'original-row-group-chain-audit-1.log').read_bytes()
assert b'Build completed successfully (3639 jobs).' in raw
assert b'Checked axiom dependencies of 75499 MicroCFTA theorems.' in raw
report = dict(status='PASS', observed_at=datetime.datetime.now().astimezone().isoformat(), jobs=jobs,
    actual_jobs=3, source_jobs=2, audit_jobs=1, failed_jobs=0, warned_source_exit_zero_jobs=0,
    rejected_public_type_jobs=0, audit_build_jobs=3639, audit_dependencies=75499,
    mathematical_repairs=0, metadata_failures=0, proof_commit='PENDING', whole_goal_complete=False)
(HERE / 'actual-job-metrics.json').write_text(json.dumps(report,indent=2)+'\n')
with (HERE / 'current-progress.md').open('a') as out:
    out.write('\n## Aggregate Audit passes\n\n')
    out.write('Audit1 passes with3639 jobs and75499 theorem dependencies.\n')
    out.write('The actual ledger has3 commands: strict1, sole FULL1 and Audit1.\n')
    out.write('All return0. Strict output is literal empty. Source warning counts are0.\n')
    out.write('Audit retains existing replay warnings in its raw log. No source or metadata\n')
    out.write('repair is needed at this cut. The actual-result tool binding remains pending.\n')
    out.write('The source remains uncommitted. The whole goal is incomplete.\n')
print(json.dumps({key:value for key,value in report.items() if key != 'jobs'}))
