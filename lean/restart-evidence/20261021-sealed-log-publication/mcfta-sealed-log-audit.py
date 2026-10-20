import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT / 'lean/restart-evidence'
tracked = set(subprocess.check_output(['git', 'ls-files', '-z'], cwd=ROOT).decode().split('\0'))
required = {}
missing = []
for manifest in sorted(BASE.rglob('SHA256SUMS')):
    for line in manifest.read_text().splitlines():
        digest, name = line.split('  ', 1)
        path = ROOT / name if name.startswith('lean/') else manifest.parent / name
        relative = str(path.relative_to(ROOT))
        if relative in tracked:
            continue
        if not path.is_file():
            missing.append({'manifest': str(manifest.relative_to(ROOT)), 'path': relative})
            continue
        data = path.read_bytes()
        assert hashlib.sha256(data).hexdigest() == digest, relative
        item = required.setdefault(relative, {'bytes': len(data), 'sha256': digest, 'manifests': []})
        assert item['sha256'] == digest
        item['manifests'].append(str(manifest.relative_to(ROOT)))
report = {'status': 'PASS' if not missing else 'MISSING', 'required_untracked_files': required,
          'missing_local': missing, 'total_bytes': sum(x['bytes'] for x in required.values())}
Path('/tmp/mcfta-sealed-log-audit.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({'status': report['status'], 'untracked_required': len(required),
                 'total_bytes': report['total_bytes'], 'missing_local': len(missing),
                 'largest': sorted(required.items(), key=lambda x:x[1]['bytes'], reverse=True)[:8]}))
