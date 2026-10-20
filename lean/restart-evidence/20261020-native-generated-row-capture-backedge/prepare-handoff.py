import json
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
for stem, target in [
    ('mcfta-backedge-copied-components-1', 'copied-components-run'),
    ('mcfta-backedge-archive-helper-1', 'archive-helper-run'),
    ('mcfta-backedge-archive-fixture-1', 'archive-fixture-run'),
    ('mcfta-backedge-archive-root-runs-1', 'archive-root-runs'),
]:
    for extension in ['json', 'log', 'limits.json', 'peaks.txt', 'source.py', 'usage.json']:
        source = Path('/tmp/' + stem + '.' + extension)
        destination = HERE / (target + '.' + extension)
        assert source.is_file() and not destination.exists()
        shutil.copyfile(source, destination)
for script, arguments in [('prepare-metadata.py', ['92237']),
                          ('write-fixture-summary.py', []),
                          ('write-current-documents.py', []),
                          ('finish-readme.py', [])]:
    result = json.loads(subprocess.check_output(
        [sys.executable, str(HERE / script), *arguments], cwd=ROOT))
    assert result['status'] == 'PASS'
    print(json.dumps({'script': script, **result}))
