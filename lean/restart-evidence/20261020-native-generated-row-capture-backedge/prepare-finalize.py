import json
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
for stem, target in [('mcfta-backedge-handoff-1', 'handoff-run'),
                     ('mcfta-backedge-archive-review-1', 'archive-review-run')]:
    for extension in ['json', 'log', 'limits.json', 'peaks.txt', 'source.py', 'usage.json']:
        source = Path('/tmp/' + stem + '.' + extension)
        destination = HERE / (target + '.' + extension)
        assert source.is_file() and not destination.exists()
        shutil.copyfile(source, destination)
for script, arguments in [('prepare-metadata.py', ['92237']), ('compress-large-logs.py', [])]:
    result = json.loads(subprocess.check_output([sys.executable, str(HERE / script), *arguments]))
    assert result['status'] == 'PASS'
    print(json.dumps({'script': script, **result}))
