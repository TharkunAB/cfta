import argparse, hashlib, json, os, re, tarfile
from pathlib import Path, PurePosixPath

parser = argparse.ArgumentParser()
parser.add_argument('evidence', type=Path)
parser.add_argument('--extract', type=Path)
args = parser.parse_args()
manifest = json.loads((args.evidence / 'manifest.json').read_text())
assert manifest['archive_format'] == 'sha256-objects-v1'
archive_name = manifest['archive']
assert isinstance(archive_name, str) and Path(archive_name).name == archive_name
archive = args.evidence / archive_name
assert not archive.is_symlink() and archive.is_file()
assert archive.stat().st_size == manifest['archive_bytes']
assert hashlib.sha256(archive.read_bytes()).hexdigest() == manifest['archive_sha256']
paths = {}
objects = {}
def safe_name(name):
    assert isinstance(name, str) and name and '\\' not in name and '\x00' not in name
    path = PurePosixPath(name)
    assert not path.is_absolute() and str(path) == name and '..' not in path.parts and name != '.'
    return path

for row in manifest['payloads']:
    name, size, digest = row['path'], row['bytes'], row['sha256']
    safe_name(name)
    assert name not in paths
    assert type(size) is int and size >= 0
    assert isinstance(digest, str) and re.fullmatch('[0-9a-f]{64}', digest)
    paths[name] = row
    if digest in objects:
        assert objects[digest]['bytes'] == size
    else:
        objects[digest] = {'bytes': size, 'paths': []}
    objects[digest]['paths'].append(name)
directories = manifest['directories']
assert directories == sorted(set(directories))
for name in directories:
    safe_name(name)
    assert name not in paths
directory_set = set(directories)
for name in set(paths) | directory_set:
    parts = PurePosixPath(name).parts
    assert all('/'.join(parts[:i]) in directory_set for i in range(1, len(parts)))
if args.extract:
    assert not os.path.lexists(args.extract)
    args.extract.mkdir(parents=True, exist_ok=False)
    for name in directories:
        (args.extract / name).mkdir(parents=True, exist_ok=True)
expected = {'sha256/' + digest for digest in objects}
seen = set()
with tarfile.open(archive, 'r:gz') as source:
    for member in source:
        assert member.name in expected and member.name not in seen
        assert member.isfile() and not member.issym() and not member.islnk()
        seen.add(member.name)
        digest = member.name.removeprefix('sha256/')
        row = objects[digest]
        assert member.size == row['bytes']
        stream = source.extractfile(member)
        assert stream is not None
        data = stream.read()
        assert len(data) == row['bytes'] and hashlib.sha256(data).hexdigest() == digest
        if args.extract:
            for name in row['paths']:
                target = args.extract / name
                target.parent.mkdir(parents=True, exist_ok=True)
                with target.open('xb') as output:
                    output.write(data)
assert seen == expected
if args.extract:
    restored = {str(p.relative_to(args.extract)): p for p in args.extract.rglob('*') if p.is_file()}
    assert set(restored) == set(paths)
    assert {str(p.relative_to(args.extract)) for p in args.extract.rglob('*') if p.is_dir()} == directory_set
    for name, source in restored.items():
        assert not source.is_symlink()
        data = source.read_bytes()
        assert len(data) == paths[name]['bytes']
        assert hashlib.sha256(data).hexdigest() == paths[name]['sha256']
print(json.dumps({'status': 'pass', 'archive_format': manifest['archive_format'],
                  'payloads': len(paths), 'unique_objects': len(objects),
                  'directories': len(directories),
                  'payload_bytes': sum(row['bytes'] for row in paths.values()),
                  'unique_object_bytes': sum(row['bytes'] for row in objects.values()),
                  'fresh_regular_file_extraction': bool(args.extract)}))
