import datetime
import hashlib
import json
import os
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
stem = 'child-separation-search-1'
assert not (HERE / (stem + '.json')).exists()
usage = json.loads(subprocess.check_output(['python3', '/tmp/mcfta-weekly-usage.py'], text=True))
(HERE / (stem + '.usage.json')).write_text(json.dumps(usage, indent=2) + '\n')
assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1, usage
source = HERE / 'child-separation-search.py'
frozen = HERE / (stem + '.source.py')
assert not frozen.exists()
frozen.write_bytes(source.read_bytes())
command = ['/usr/bin/python3', str(frozen)]
wrapped = ['/home/tritlo/Code/heavy-management/bin/capped', '--mem', '4G', '--time', '5m',
           'python3', str(HERE / 'child-separation-capped-worker.py')]
env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1', XDG_RUNTIME_DIR='/run/user/1000',
           DBUS_SESSION_BUS_ADDRESS='unix:path=/run/user/1000/bus',
           HEAVY_PEAKS=str(HERE / 'child-separation-peaks.txt'),
           CHILD_SEPARATION_LIMITS=str(HERE / (stem + '.limits.json')),
           CHILD_SEPARATION_COMMAND=json.dumps(command))
started = datetime.datetime.now(datetime.timezone.utc).isoformat()
with (HERE / (stem + '.log')).open('xb') as log:
    result = subprocess.run(wrapped, cwd='/', env=env, stdout=log, stderr=subprocess.STDOUT)
report = dict(command=command, wrapper=wrapped, exit_code=result.returncode, started_at=started,
              observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(), source=frozen.name,
              sha256=hashlib.sha256(frozen.read_bytes()).hexdigest(), log=stem + '.log',
              limits=stem + '.limits.json')
(HERE / (stem + '.json')).write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
print((HERE / (stem + '.log')).read_text())
raise SystemExit(result.returncode)
