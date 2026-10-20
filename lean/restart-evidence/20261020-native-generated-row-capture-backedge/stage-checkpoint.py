"""Stage the sealed physical evidence and current documents."""

import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
restored = {item['original'] for item in json.loads((HERE / 'compressed-evidence.json').read_text())}
current = set(json.loads((HERE / 'current-documents.json').read_text()))
current.update('lean/MicroCFTA/' + name + '.lean'
               for name in json.loads((HERE / 'new-modules.json').read_text()))
paths = set(current)
paths.add(str((HERE / 'SHA256SUMS').relative_to(ROOT)))
for line in (HERE / 'SHA256SUMS').read_text().splitlines():
    paths.add(line.split('  ', 1)[1])
assert not paths & restored
assert all((ROOT / path).stat().st_size < 90 * 1024 * 1024 for path in paths)
subprocess.run(['git', 'add', '-f', '--', *sorted(paths)], cwd=ROOT, check=True)
subprocess.run(['git', 'diff', '--cached', '--check', '--', *sorted(current)], cwd=ROOT, check=True)
print(json.dumps({'status': 'PASS', 'staged_paths': len(paths),
                  'ignored_raw_paths_excluded': len(restored)}))
