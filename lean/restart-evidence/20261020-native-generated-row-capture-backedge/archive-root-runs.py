import json
from pathlib import Path
import shutil

HERE = Path(__file__).resolve().parent
for stem, target in [
    ('mcfta-backedge-archive-components-1', 'archive-components-run'),
    ('mcfta-backedge-compress-1', 'compress-run'),
    ('mcfta-backedge-restore-check-1', 'restore-check-run'),
]:
    for extension in ['json', 'log', 'limits.json', 'peaks.txt', 'source.py', 'usage.json']:
        source = Path('/tmp/' + stem + '.' + extension)
        destination = HERE / (target + '.' + extension)
        assert source.is_file() and not destination.exists()
        shutil.copyfile(source, destination)
print(json.dumps({'status': 'PASS', 'root_artifact_sets': 3}))
