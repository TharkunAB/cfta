import json
import shutil
from pathlib import Path

HERE = Path(__file__).resolve().parent
for stem in ['mcfta-stored-mu-position-prepare-1', 'mcfta-stored-mu-position-verify-1', 'mcfta-stored-mu-position-extend-1']:
    for suffix in ['json', 'log', 'limits.json', 'peaks.txt', 'source.py', 'usage.json']:
        source = Path('/tmp') / (stem + '.' + suffix)
        assert source.is_file(), source
        shutil.copyfile(source, HERE / 'root-support' / source.name)
print(json.dumps({'status': 'PASS'}))
