from pathlib import Path
import datetime
import json
import os
import subprocess
import sys

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = Path(__file__).resolve().parent
name, source = sys.argv[1:]
snapshot = HERE / (name + '.source.lean')
assert not snapshot.exists()
snapshot.write_bytes(Path(source).read_bytes())
command = ['/home/tritlo/Code/heavy-management/bin/capped', '--mem', '4G', '--time', '5m',
    'python3', str(HERE / 'union-local-check-worker.py'), str(HERE / (name + '.limits.json')), str(snapshot)]
environment = os.environ.copy()
environment.update(LEAN_PATH=str(ROOT / 'lean/.lake/build/lib/lean'),
    HEAVY_PEAKS=str(HERE / 'union-local-peaks.txt'), XDG_RUNTIME_DIR='/run/user/1000',
    DBUS_SESSION_BUS_ADDRESS='unix:path=/run/user/1000/bus')
with (HERE / (name + '.log')).open('wb') as output:
    result = subprocess.run(command, cwd=ROOT / 'lean', env=environment,
        stdout=output, stderr=subprocess.STDOUT)
(HERE / (name + '.json')).write_text(json.dumps(dict(command=command,
    exit_code=result.returncode, source=snapshot.name, log=name+'.log',
    timestamp=datetime.datetime.now().astimezone().isoformat(),
    LEAN_PATH=environment['LEAN_PATH'], memory_max='4G', swap_max=0), indent=2)+'\n')
print(name, 'exit', result.returncode, 'bytes', (HERE / (name+'.log')).stat().st_size)
if result.returncode:
    print((HERE / (name+'.log')).read_text()[:18000])
sys.exit(result.returncode)
