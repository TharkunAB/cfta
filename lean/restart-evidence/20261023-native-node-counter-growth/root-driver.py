import datetime, json, os, subprocess, sys
from pathlib import Path
root = Path('/home/tritlo/Code/mcfta')
here = root / 'lean/restart-evidence/20261023-native-node-counter-growth'
stem, script = sys.argv[1:3]
usage = subprocess.check_output(['/usr/bin/python3', '/tmp/mcfta-weekly-usage.py'], text=True)
Path('/tmp/' + stem + '.usage.json').write_text(usage)
sampled = json.loads(usage)
assert sampled['age_seconds'] <= 600 and sampled['remaining_percent'] > 1
source = Path(script) if Path(script).is_absolute() else here / script
snapshot = Path('/tmp/' + stem + '.source.py')
assert not snapshot.exists()
snapshot.write_bytes(source.read_bytes())
command = ['/usr/bin/python3', str(source), *sys.argv[3:]]
env = {**os.environ, 'PYTHONDONTWRITEBYTECODE': '1', 'XDG_RUNTIME_DIR': '/run/user/1000',
       'DBUS_SESSION_BUS_ADDRESS': 'unix:path=/run/user/1000/bus',
       'HEAVY_PEAKS': '/tmp/' + stem + '.peaks.txt', 'NATIVE_CAUSAL_LIMITS': '/tmp/' + stem + '.limits.json',
       'NATIVE_CAUSAL_COMMAND': json.dumps(command)}
wrapper = ['/home/tritlo/Code/heavy-management/bin/capped', '--mem', '4G', '--time', '5m',
           '/usr/bin/python3', str(here / 'root-capped-worker.py')]
with Path('/tmp/' + stem + '.log').open('xb') as log:
    result = subprocess.run(wrapper, env=env, cwd=root, stdout=log, stderr=subprocess.STDOUT)
receipt = {'command': command, 'wrapper': wrapper, 'exit_code': result.returncode,
           'observed_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
           'log': '/tmp/' + stem + '.log', 'limits': '/tmp/' + stem + '.limits.json'}
Path('/tmp/' + stem + '.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt))
if result.returncode:
    print(Path('/tmp/' + stem + '.log').read_text()[-18000:])
raise SystemExit(result.returncode)
