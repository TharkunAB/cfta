from pathlib import Path
import json
relative = next(line.split(':', 2)[2] for line in Path('/proc/self/cgroup').read_text().splitlines() if line.startswith('0::'))
base = Path('/sys/fs/cgroup') / relative.lstrip('/')
result = {'cgroup': relative, **{key: (base / key).read_text().strip() for key in ['memory.max','memory.high','memory.swap.max']}}
assert result['memory.max'] == result['memory.high'] == '4294967296'
assert result['memory.swap.max'] == '0'
Path('/tmp/mcfta-child-invariants-20261025/cap-probe.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result))
