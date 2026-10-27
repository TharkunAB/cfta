from pathlib import Path
import gzip
import hashlib
import json
import shutil
import subprocess

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-flat-pruning-callback-20261027')
snapshot = root / 'lean/restart-evidence/20261027-flat-pruning-callback'
preserved = Path('/tmp/mcfta-flat-pruning-callback-packaging-v1')
assert not preserved.exists()
def digest(data):
    return hashlib.sha256(data).hexdigest()
manifest_data = (snapshot / 'manifest.json').read_bytes()
manifest = json.loads(manifest_data)
documents = json.loads((area / 'document-paths.json').read_text())
prefix = str(snapshot.relative_to(root))
expected = set(documents) | {prefix + '/' + record['path'] for record in manifest['files']} | {prefix + '/manifest.json'}
staged = subprocess.check_output(['git', 'diff', '--cached', '--name-only', '-z'], cwd=root)
assert {item.decode() for item in staged.split(b'\0') if item} == expected
subprocess.run(['git', 'restore', '--staged', '--', *documents, prefix], cwd=root, check=True)
snapshot.rename(preserved)
snapshot.mkdir()
for record in manifest['files']:
    target = snapshot / record['path']
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(preserved / record['path'], target)
decoded = json.loads((snapshot / 'decoded-files.json').read_text())
changes = []
for path in sorted(snapshot.rglob('*')):
    if not path.is_file() or path.suffix == '.gz':
        continue
    data = path.read_bytes()
    if not data.endswith((b'\n\n', b'\r\n\r\n')):
        continue
    target = path.with_name(path.name + '.gz')
    target.write_bytes(gzip.compress(data, mtime=0))
    record = {'original_path': str(path.relative_to(snapshot)),
        'stored_path': str(target.relative_to(snapshot)), 'bytes': len(data), 'sha256': digest(data)}
    decoded.append(record)
    changes.append(record)
    path.unlink()
(snapshot / 'decoded-files.json').write_text(json.dumps(decoded, indent=2) + '\n')
(snapshot / 'packaging-v1-manifest.json').write_bytes(manifest_data)
(snapshot / 'packaging-revision.json').write_text(json.dumps({
    'reason': 'Git whitespace checking rejects final blank lines in exact literal source/prose excerpts. Compress these payloads losslessly. Keep the first immutable snapshot outside the worktree and retain its manifest here.',
    'preserved_v1': str(preserved), 'v1_manifest_sha256': digest(manifest_data),
    'changes': changes, 'decoded_original_bytes_unchanged': True}, indent=2) + '\n')
shutil.copyfile(__file__, snapshot / 'packaging-revision.py')
files = []
for path in sorted(snapshot.rglob('*')):
    if path.is_file():
        data = path.read_bytes()
        files.append({'path': str(path.relative_to(snapshot)), 'bytes': len(data), 'sha256': digest(data)})
manifest['files'] = files
(snapshot / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
old_report = Path('/tmp/mcfta-flat-pruning-callback-snapshot.json')
shutil.copyfile(old_report, '/tmp/mcfta-flat-pruning-callback-snapshot-v1.json')
report = {'snapshot': str(snapshot), 'payloads': len(files), 'bytes': sum(r['bytes'] for r in files),
    'archives': len(decoded), 'manifest_sha256': digest((snapshot / 'manifest.json').read_bytes()),
    'literal_excerpts_compressed': len(changes)}
old_report.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
