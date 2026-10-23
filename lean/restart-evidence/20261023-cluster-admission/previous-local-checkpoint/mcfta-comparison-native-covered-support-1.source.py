import hashlib
import json
import shutil
from pathlib import Path

HERE = Path(__file__).resolve().parent
target = HERE / 'completed-root-support'
target.mkdir()
files = {}
for source in sorted(Path('/tmp').glob('mcfta-comparison-native-covered-*')):
    if not source.is_file() or source.name.startswith('mcfta-comparison-native-covered-support-1'):
        continue
    shutil.copyfile(source, target / source.name)
    files[source.name] = hashlib.sha256(source.read_bytes()).hexdigest()
(target / 'manifest.json').write_text(json.dumps(files, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'files': len(files)}))
