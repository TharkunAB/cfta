"""Check archive restoration without an existing copy of any raw log."""

import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
items = json.loads((HERE / 'compressed-evidence.json').read_text())
with tempfile.TemporaryDirectory(prefix='mcfta-backedge-restore-') as directory:
    target_root = Path(directory)
    target_here = target_root / HERE.relative_to(ROOT)
    target_here.mkdir(parents=True)
    for name in ['prepare-evidence.py', 'compressed-evidence.json']:
        shutil.copyfile(HERE / name, target_here / name)
    for name in {item['archive'] for item in items}:
        destination = target_root / name
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / name, destination)
    for item in items:
        destination = target_root / item['original']
        destination.parent.mkdir(parents=True, exist_ok=True)
        assert not destination.exists()
    result = subprocess.run([sys.executable, str(target_here / 'prepare-evidence.py')],
                            cwd='/', check=True, capture_output=True, text=True)
    assert result.stdout == 'PASS: compressed archives and exact original raw logs verified\n'
print(json.dumps({'status': 'PASS', 'restored_paths': len(items),
                  'distinct_archives': len({item['archive'] for item in items}),
                  'original_bytes_restored': sum(item['original_bytes'] for item in items),
                  'existing_raw_logs_used': False}))
