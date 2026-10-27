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
old_area = Path('/tmp/mcfta-flat-pruning-callback-20261027')
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
review_records = 0
for name in sorted(actual | set(archives)):
    if not name.endswith('/source-pins.json'):
        continue
    review = Path(name).parent
    def visit(value):
        global review_records
        if isinstance(value, list):
            for item in value:
                visit(item)
        elif isinstance(value, dict):
            copied = value.get('snapshot', value.get('copy_path'))
            original = value.get('source', value.get('source_path'))
            if copied and original and 'sha256' in value:
                data = relocated(copied, review)
                assert len(data) == value['bytes'] and digest(data) == value['sha256']
                source = Path(original)
                if not source.is_absolute():
                    source = old_repository / source
                original_data = relocated(source, review)
                first = value.get('first_line', value.get('first'))
                last = value.get('last_line', value.get('last'))
                if first is not None:
                    original_data = b''.join(original_data.splitlines(keepends=True)[first-1:last])
                assert original_data == data, (name, copied)
                review_records += 1
            else:
                for item in value.values():
                    visit(item)
    pins = json.loads(read(name))
    visit(pins)
    for status in pins.get('status_documents', []):
        current = (repository / status['path']).read_bytes()
        baseline = read(Path('prior-documents') / status['path'])
        offset = status['offset']
        count = status['inserted_bytes']
        assert digest(current) == status['current_sha256']
        assert digest(baseline) == status['baseline_sha256']
        assert digest(current[offset:offset+count]) == status['inserted_sha256']
        assert current[:offset] + current[offset+count:] == baseline
for module in json.loads(read('modules.json')) + ['Audit',
    'SourceCurrentColdFiniteWarmCalls', 'SourcePruningEnumerationCapturedRendering']:
    relative = Path('lean/MicroCFTA') / (module + '.lean')
    assert read(Path('installed-sources') / relative) == (repository / relative).read_bytes()
if args.committed:
    prefix = snapshot.relative_to(repository)
    tracked = subprocess.check_output(['git', 'ls-files', '-z', '--', str(prefix)], cwd=repository)
    names = {str(Path(item.decode()).relative_to(prefix)) for item in tracked.split(b'\0') if item}
    assert names == actual
    for name in names:
        data = subprocess.check_output(['git', 'show', 'HEAD:' + str(prefix / name)], cwd=repository)
        assert data == (snapshot / name).read_bytes(), name
print(json.dumps({'status': 'pass', 'payloads': len(expected), 'bytes': sum(r['bytes'] for r in manifest['files']),
    'archives': len(archives), 'review_records': review_records, 'committed': args.committed,
    'manifest_sha256': digest((snapshot / 'manifest.json').read_bytes())}))
