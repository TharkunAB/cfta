from pathlib import Path
import argparse
import gzip
import hashlib
import json
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument('snapshot', type=Path)
parser.add_argument('--repository', type=Path, default=Path('/home/tritlo/Code/mcfta'))
parser.add_argument('--committed', action='store_true')
args = parser.parse_args()
snapshot = args.snapshot.resolve()
repository = args.repository.resolve()
old_area = Path('/tmp/mcfta-flat-recursive-20261027')
old_repository = Path('/home/tritlo/Code/mcfta')


def digest(data):
    return hashlib.sha256(data).hexdigest()


manifest = json.loads((snapshot / 'manifest.json').read_text())
actual = {str(p.relative_to(snapshot)) for p in snapshot.rglob('*') if p.is_file()}
expected = {record['path'] for record in manifest['files']}
assert actual == expected | {'manifest.json'}
for record in manifest['files']:
    path = snapshot / record['path']
    assert not path.is_symlink()
    data = path.read_bytes()
    assert len(data) == record['bytes'] and digest(data) == record['sha256'], path
decoded = json.loads((snapshot / 'decoded-files.json').read_text())
archives = {item['original_path']: item for item in decoded}


def read(relative):
    path = snapshot / relative
    if path.is_file():
        return path.read_bytes()
    record = archives[str(relative)]
    data = gzip.decompress((snapshot / record['stored_path']).read_bytes())
    assert len(data) == record['bytes'] and digest(data) == record['sha256'], relative
    return data


for name in archives:
    read(name)


def relocated(path, review):
    path = Path(path)
    if path.is_absolute() and path.is_relative_to(old_area):
        return read(path.relative_to(old_area))
    if path.is_absolute() and path.is_relative_to(old_repository):
        return (repository / path.relative_to(old_repository)).read_bytes()
    if path.is_absolute():
        raise ValueError(path)
    return read(review / path)


def original_of(entry):
    name = entry.get('source', entry.get('source_path', entry.get('path')))
    path = Path(name)
    return str(path if path.is_absolute() else old_repository / path)


def first_of(entry):
    return entry.get('first_line', entry.get('first', entry.get('start')))


review_records = 0
historical_sources = []
for name in sorted(actual | set(archives)):
    if not name.endswith(('/source-pins.json', '/draft-pins.json')) or not (len(Path(name).parts) == 2 or name == 'callback-correspondence-draft/v2/source-pins.json'):
        continue
    review = Path(name).parent
    entries = []

    def visit(value, inherited_source=None, inherited_hash=None):
        if isinstance(value, list):
            for item in value:
                visit(item, inherited_source, inherited_hash)
        elif isinstance(value, dict):
            copied = value.get('snapshot', value.get('copy_path'))
            original = value.get('source', value.get('source_path', value.get('path', inherited_source)))
            source_hash = inherited_hash
            if copied and original and 'sha256' in value:
                entry = dict(value, source=original)
                if first_of(entry) is not None and 'source_sha256' not in entry:
                    entry['source_sha256'] = inherited_hash
                entries.append(entry)
                if first_of(entry) is None:
                    source_hash = entry['sha256']
            for item in value.values():
                visit(item, original, source_hash)

    visit(json.loads(read(name)))
    wholes = {}
    for entry in entries:
        copied = entry.get('snapshot', entry.get('copy_path'))
        original = original_of(entry)
        data = relocated(copied, review)
        assert len(data) == entry['bytes'] and digest(data) == entry['sha256'], (name, copied)
        first = first_of(entry)
        if first is None:
            wholes[(original, digest(data))] = data
    for entry in entries:
        copied = entry.get('snapshot', entry.get('copy_path'))
        original = original_of(entry)
        data = relocated(copied, review)
        first = first_of(entry)
        last = entry.get('last_line', entry.get('last', entry.get('end')))
        if first is not None:
            full_hash = entry.get('source_sha256')
            candidates = [value for (source, sha), value in wholes.items()
                          if source == original and (full_hash is None or full_hash == sha)]
            if not candidates:
                candidates = [relocated(original, review)]
            assert any(b''.join(full.splitlines(keepends=True)[first-1:last]) == data
                       for full in candidates), (name, copied)
        else:
            live = relocated(original, review)
            if live != data:
                historical_sources.append({'review': name, 'source': original,
                                           'historical_sha256': digest(data), 'current_sha256': digest(live)})
        review_records += 1

for module in json.loads(read('modules.json')) + ['Audit',
        'SourceCurrentColdFiniteWarmCalls', 'SourcePruningEnumerationCapturedRendering']:
    relative = Path('lean/MicroCFTA') / (module + '.lean')
    assert read(Path('installed-sources') / relative) == (repository / relative).read_bytes()
for status in json.loads(read('document-validation.json')):
    current = (repository / status['path']).read_bytes()
    assert len(current) == status['bytes'] and digest(current) == status['sha256']
    if status.get('inserted_bytes') is not None:
        old = read(Path('prior-documents') / status['path'])
        offset = status['offset']
        count = status['inserted_bytes']
        assert current[:offset] + current[offset+count:] == old
if args.committed:
    prefix = snapshot.relative_to(repository)
    tracked = subprocess.check_output(['git', 'ls-files', '-z', '--', str(prefix)], cwd=repository)
    names = {str(Path(item.decode()).relative_to(prefix)) for item in tracked.split(b'\0') if item}
    assert names == actual
    for name in names:
        data = subprocess.check_output(['git', 'show', 'HEAD:' + str(prefix / name)], cwd=repository)
        assert data == (snapshot / name).read_bytes(), name
print(json.dumps({'status': 'pass', 'payloads': len(expected),
    'bytes': sum(r['bytes'] for r in manifest['files']), 'archives': len(archives),
    'review_records': review_records, 'historical_sources': historical_sources,
    'committed': args.committed, 'manifest_sha256': digest((snapshot / 'manifest.json').read_bytes())}))
