"""Add lossless archives for oversized raw logs before finalization."""

import gzip
import hashlib
import json
from pathlib import Path
import shutil

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


items = json.loads((HERE / 'compressed-evidence.json').read_text())
originals = {item['original'] for item in items}
archives = {item['original_sha256']: ROOT / item['archive'] for item in items}
added = []
for original in sorted(HERE.rglob('*')):
    if not original.is_file() or original.stat().st_size < 90 * 1024 * 1024:
        continue
    relative = str(original.relative_to(ROOT))
    if relative in originals:
        continue
    assert original.suffix == '.log', relative
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
    item = {'original': relative, 'original_bytes': original.stat().st_size,
            'original_sha256': raw_digest, 'archive': str(archive.relative_to(ROOT)),
            'archive_bytes': archive.stat().st_size, 'archive_sha256': digest(archive)}
    items.append(item)
    added.append(item)
(HERE / 'compressed-evidence.json').write_text(json.dumps(items, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'new_archived_paths': added,
                  'total_restored_paths': len(items), 'distinct_archives': len(archives)}))
