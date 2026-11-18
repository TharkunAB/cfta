from pathlib import Path
import gzip
import hashlib
import json

ROOT = Path('/home/tritlo/Code/mcfta')
WORK = Path(__file__).resolve().parent
PACKET = ROOT / 'lean/restart-evidence/20261118-source78-real-eager-task-obligations-checkpoint'
records, payloads = [], {}
items = json.loads((WORK / 'archive-files.json').read_text())
late = WORK / 'CHECKPOINT-POST-BINDER-FILES.json'
if late.exists():
    for item in json.loads(late.read_text()):
        path = ROOT / item['path']
        assert path.parent == WORK
        assert path.name in {'CHECKPOINT-BINDER-ROOT-REVIEW.json', 'CHECKPOINT-ARCHIVE-ENGINES-ROOT-REVIEW.json', 'CHECKPOINT-PREPARER-ACTUAL-RUN.json', 'CHECKPOINT-PREPARER-CONSOLE.txt'}
        assert item['path'] not in {e['path'] for e in items}
        items.append(item)
assert not PACKET.exists()
PACKET.mkdir()
for item in items:
    source = ROOT / item['path']
    assert source.is_file() and not source.is_symlink()
    assert source.suffix not in {'.olean', '.ilean', '.o', '.hi', '.a', '.so', '.dylib', '.pyc'}
    before = source.stat()
    data = source.read_bytes()
    after = source.stat()
    assert (before.st_ino, before.st_size, before.st_mtime_ns) == (after.st_ino, after.st_size, after.st_mtime_ns)
    digest = hashlib.sha256(data).hexdigest()
    assert len(data) == item['bytes'] and digest == item['sha256']
    assert not data.startswith(b'\x7fELF')
    if digest not in payloads:
        target = PACKET / 'payloads' / (digest + '.gz')
        target.parent.mkdir(exist_ok=True)
        target.write_bytes(gzip.compress(data, mtime=0))
        payloads[digest] = str(target.relative_to(PACKET))
    records.append({'original': str(source), 'archived': payloads[digest], 'gzip': True,
                    'source_bytes': len(data), 'source_sha256': digest})
(PACKET / 'archived-inputs.json').write_text(json.dumps(records, indent=2) + '\n')
print(json.dumps({'selected_inputs': len(records), 'distinct_payloads': len(payloads), 'archive': str(PACKET)}))
