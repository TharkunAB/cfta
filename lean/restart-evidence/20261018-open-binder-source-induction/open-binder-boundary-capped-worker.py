import os, json
from pathlib import Path
relative = Path('/proc/self/cgroup').read_text().split('0::', 1)[1].splitlines()[0]
base = Path('/sys/fs/cgroup') / relative.lstrip('/')
limits = {key: (base/key).read_text().strip() for key in ['memory.max', 'memory.high', 'memory.swap.max']}
Path(os.environ['OPEN_BINDER_BOUNDARY_LIMITS']).write_text(json.dumps(limits, indent=2) + '\n')
assert limits == {'memory.max':'4294967296', 'memory.high':'4294967296', 'memory.swap.max':'0'}, limits
command = json.loads(os.environ['OPEN_BINDER_BOUNDARY_COMMAND'])
os.execv(command[0], command)
