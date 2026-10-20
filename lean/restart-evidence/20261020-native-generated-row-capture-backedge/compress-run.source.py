import gzip
import hashlib
import json
import shutil
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
here = root / 'lean/restart-evidence/20261020-native-generated-row-capture-backedge'
shutil.copyfile(root / 'lean/restart-evidence/20261017-initial-parent/prepare-evidence.py',
                here / 'prepare-evidence.py')


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


logs = [here / 'backedge-module/generated-row-backedge-public-2.log',
        here / 'backedge-module/generated-row-backedge-public-3.log',
        here / 'source-review/reviewed/generated-row-backedge-public-3.log']
archives = {}
items = []
for original in logs:
    raw_digest = digest(original)
    if raw_digest not in archives:
        archive = original.with_suffix(original.suffix + '.gz')
        assert not archive.exists()
        with original.open('rb') as source, archive.open('xb') as output:
            with gzip.GzipFile(filename='', mode='wb', fileobj=output, mtime=0) as target:
                shutil.copyfileobj(source, target)
        assert archive.stat().st_size < 90 * 1024 * 1024
        archives[raw_digest] = archive
    archive = archives[raw_digest]
    items.append({'original': str(original.relative_to(root)),
                  'original_bytes': original.stat().st_size,
                  'original_sha256': raw_digest,
                  'archive': str(archive.relative_to(root)),
                  'archive_bytes': archive.stat().st_size,
                  'archive_sha256': digest(archive)})
(here / 'compressed-evidence.json').write_text(json.dumps(items, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'restored_paths': len(items),
                  'distinct_archives': len(archives), 'items': items}))
