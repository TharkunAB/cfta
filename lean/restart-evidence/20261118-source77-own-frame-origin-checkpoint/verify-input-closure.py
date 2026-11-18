from pathlib import Path
from collections import Counter
import gzip
import hashlib
import json
import subprocess

ROOT = Path('/home/tritlo/Code/mcfta')
BASE = ROOT / 'lean/restart-evidence'
PACKET = BASE / '20261118-source77-own-frame-origin-checkpoint'
SHA = lambda data: hashlib.sha256(data).hexdigest()
read = lambda path: json.loads(path.read_text())
config = read(PACKET / 'checkpoint.json')
exact, by_digest = {}, {}


def index_archive(path, manifest_sha=None, inputs_sha=None):
    encoded = {}
    if manifest_sha:
        manifest_data = (path / 'manifest.json').read_bytes()
        assert SHA(manifest_data) == manifest_sha
        manifest = json.loads(manifest_data)
        encoded = {x['path']: x['sha256'] for x in manifest['files']}
    data = (path / 'archived-inputs.json').read_bytes()
    if inputs_sha:
        assert SHA(data) == inputs_sha
    if encoded:
        assert SHA(data) == encoded['archived-inputs.json']
    for x in json.loads(data):
        name = str(Path(x['original']).relative_to(ROOT))
        e = (path / x['archived'], x['gzip'], encoded.get(x['archived']))
        exact.setdefault((name, x['source_sha256']), e)
        by_digest.setdefault(x['source_sha256'], e)
    for name, digest in encoded.items():
        exact.setdefault((str((path / name).relative_to(ROOT)), digest), (path / name, False, digest))
        by_digest.setdefault(digest, (path / name, False, digest))
    if manifest_sha:
        exact[(str((path / 'manifest.json').relative_to(ROOT)), manifest_sha)] = (path / 'manifest.json', False, manifest_sha)


index_archive(PACKET)
links = read(PACKET / 'ancestor-links.json')['linked_existing_archives']
assert len(links) == 56
for x in links:
    index_archive(BASE / x['root'], x['manifest_sha256'], x['archived_inputs_sha256'])
normal = json.loads(gzip.decompress((PACKET / 'source-pins.json.gz').read_bytes()))
assert len(normal) == 6301
# Recover checked Source/toolchain bytes from the code commit without copying a cache.
proc = subprocess.Popen(['git', 'cat-file', '--batch'], cwd=ROOT, stdin=subprocess.PIPE, stdout=subprocess.PIPE)
for name, digest in sorted(normal.items()):
    proc.stdin.write((config['checked_code'] + ':' + name + '\n').encode())
    proc.stdin.flush()
    header = proc.stdout.readline().split()
    assert len(header) == 3 and header[1] == b'blob', (name, header)
    data = proc.stdout.read(int(header[2]))
    assert proc.stdout.read(1) == b'\n' and SHA(data) == digest, name
proc.stdin.close()
assert proc.wait() == 0


def payload(name, digest):
    e = exact.get((name, digest)) or by_digest.get(digest)
    assert e, ('Unresolved archived input', name, digest)
    path, compressed, encoded = e
    data = path.read_bytes()
    assert encoded is None or SHA(data) == encoded, path
    if compressed:
        data = gzip.decompress(data)
    assert SHA(data) == digest, (name, path)
    return data


counts, pairs, maps, checked = Counter(), set(), {}, set()
for item in read(PACKET / 'input-maps.json'):
    pins = json.loads(payload(item['path'], item['sha256']))
    maps[item['path']] = len(pins)
    for name, digest in pins.items():
        if (name, digest) in pairs:
            continue
        pairs.add((name, digest))
        if normal.get(name) == digest:
            counts['checked_Source_or_toolchain'] += 1
        else:
            payload(name, digest)
            counts['hash_bound_archived_payload'] += 1
            checked.add((name, digest))
assert sorted(maps.values()) == sorted(config['formal_input_map_counts'])
assert all('Inspect' not in name or not name.endswith('SOURCE-PINS.json') for name in maps)
print(json.dumps({'status': 'ALL FORMAL ACTUAL INPUT MAPS RECOVERABLE', 'maps': maps,
                  'distinct_path_digest_pairs': len(pairs), 'classifications': dict(counts),
                  'linked_ancestors': len(links), 'ancestor_archives_copied': 0,
                  'normal_cache_data_copied': False, 'new_theorem_credit': 0}))
