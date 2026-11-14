from pathlib import Path
import gzip
import hashlib
import json
import subprocess
import sys

ROOT = Path('/home/tritlo/Code/mcfta')
PACKET = ROOT / 'lean/restart-evidence/20261114-shared-child-resources-and-atom-steps'
SHA = lambda data: hashlib.sha256(data).hexdigest()
checkpoint = json.loads((PACKET / 'checkpoint.json').read_text())
records = json.loads((PACKET / 'archived-inputs.json').read_text())
for item in records:
    path = PACKET / item['archived']
    data = path.read_bytes()
    if item['gzip']:
        data = gzip.decompress(data)
    assert len(data) == item['source_bytes']
    assert SHA(data) == item['source_sha256'], path
pins = json.loads(gzip.decompress((PACKET / 'source-pins.json.gz').read_bytes()))
source_pins = {p: sha for p, sha in pins.items() if p.startswith('lean/MicroCFTA/')}
tree = hashlib.sha256()
for path, digest in sorted(source_pins.items()):
    tree.update(path.encode() + b'\0' + digest.encode() + b'\n')
assert len(source_pins) == checkpoint['source_files']
assert tree.hexdigest() == checkpoint['source_tree_sha256']
if '--current-tree' in sys.argv:
    for path, digest in pins.items():
        assert SHA((ROOT / path).read_bytes()) == digest, path
for item in checkpoint['documents']:
    old = subprocess.check_output(['git', 'show', item['prior_commit'] + ':' + item['path']], cwd=ROOT)
    prefix = gzip.decompress((PACKET / 'document-prefixes' / (item['path'] + '.gz')).read_bytes())
    assert SHA(old) == item['prior_sha256']
    assert SHA(prefix) == item['prefix_sha256']
    assert SHA(prefix + old) == item['updated_sha256']
    if '--current-tree' in sys.argv:
        assert (ROOT / item['path']).read_bytes() == prefix + old
expected_patch = subprocess.check_output(['git', 'diff', checkpoint['prior_checkpoint'],
                                         checkpoint['checked_code'], '--', 'lean/MicroCFTA'], cwd=ROOT)
assert gzip.decompress((PACKET / 'checked-code.patch.gz').read_bytes()) == expected_patch
for path in PACKET.rglob('*'):
    assert not path.is_symlink(), path
    if path.is_file():
        assert path.suffix not in {'.olean', '.ilean', '.o', '.hi', '.a', '.so', '.dylib'}, path
        assert not path.read_bytes().startswith(b'\x7fELF'), path
manifest_path = PACKET / 'manifest.json'
if '--write-manifest' in sys.argv:
    assert not manifest_path.exists()
    summary = {'archived_inputs_verified': len(records), 'source_files': len(source_pins),
               'source_tree_sha256': tree.hexdigest(), 'prior_document_bytes_preserved': True,
               'no_compiled_objects_or_symlinks': True, 'checked_code': checkpoint['checked_code']}
    (PACKET / 'verification.json').write_text(json.dumps(summary, indent=2) + '\n')
    files = [{'path': str(p.relative_to(PACKET)), 'bytes': p.stat().st_size,
              'sha256': SHA(p.read_bytes())}
             for p in sorted(PACKET.rglob('*')) if p.is_file() and p != manifest_path]
    manifest_path.write_text(json.dumps({'files': files}, indent=2) + '\n')
manifest = json.loads(manifest_path.read_text())
expected = {item['path'] for item in manifest['files']}
actual = {str(p.relative_to(PACKET)) for p in PACKET.rglob('*') if p.is_file() and p != manifest_path}
assert actual == expected
for item in manifest['files']:
    data = (PACKET / item['path']).read_bytes()
    assert len(data) == item['bytes'] and SHA(data) == item['sha256'], item['path']
print(json.dumps({'archived_inputs_verified': len(records), 'payload_files_verified': len(expected),
                  'total_files': len(expected) + 1,
                  'total_bytes': sum(p.stat().st_size for p in PACKET.rglob('*') if p.is_file()),
                  'manifest_sha256': SHA(manifest_path.read_bytes()), 'source_tree_sha256': tree.hexdigest()}))
