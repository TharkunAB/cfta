from pathlib import Path
import datetime
import hashlib
import json
import os
import shlex
import subprocess
import sys

source = Path(sys.argv[1]).resolve()
expected = sys.argv[2]
runtime = Path(__file__).parent
assert hashlib.sha256(source.read_bytes()).hexdigest() == expected
cg = next(line.split(':', 2)[2] for line in Path('/proc/self/cgroup').read_text().splitlines()
          if line.startswith('0::'))
cgroup = Path('/sys/fs/cgroup') / cg.lstrip('/')
limits = {name: (cgroup / name).read_text().strip()
          for name in ['memory.max', 'memory.high', 'memory.swap.max']}
assert limits == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
environment = dict(os.environ)
environment.pop('LEAN_SYSROOT', None)
environment['LEAN_NUM_THREADS'] = '1'
command = 'exec lake env lean -j1 -DwarningAsError=true ' + shlex.quote(str(source))
if len(sys.argv) == 4:
    command = 'lake build ' + shlex.quote(sys.argv[3]) + ' && ' + command
result = subprocess.run(
    ['nix-shell', '/home/tritlo/Code/mcfta/shell.nix', '--run',
     command],
    cwd='/home/tritlo/Code/mcfta/lean', env=environment,
    capture_output=True, text=True)
(runtime / 'draft-output.txt').write_text(result.stdout + result.stderr)
assert hashlib.sha256(source.read_bytes()).hexdigest() == expected
report = {'at': datetime.datetime.now().astimezone().isoformat(),
          'source': str(source), 'sha256': expected, 'limits': limits,
          'compiler_exit': result.returncode, 'public_laws_added': 0,
          'emitted_type_origin_proved': False, 'haskell_changes': False}
(runtime / 'draft-checked.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
raise SystemExit(result.returncode)
