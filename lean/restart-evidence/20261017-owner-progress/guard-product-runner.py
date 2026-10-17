import os
from pathlib import Path
cgroup = Path('/sys/fs/cgroup')
current = next(line.split(':', 2)[2] for line in Path('/proc/self/cgroup').read_text().splitlines() if line.startswith('0::'))
actual = cgroup / current.lstrip('/')
for name, expected in [('memory.max', '4294967296'), ('memory.high', '4294967296'), ('memory.swap.max', '0')]:
    value = (actual / name).read_text().strip()
    print(f'{name}={value}', flush=True)
    assert value == expected, (name, value)
os.environ['LEAN_PATH'] = '/home/tritlo/Code/mcfta/lean/.lake/build/lib/lean'
os.execv('/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean', ['lean', '-Dlinter.all=true', os.environ['OWNER_PROGRESS_SOURCE']])
