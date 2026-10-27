from pathlib import Path
import gzip
import hashlib
import json
import shutil
import subprocess

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-flat-captured-edge-20261027')
snapshot = root / 'lean/restart-evidence/20261027-flat-captured-edge'
assert not snapshot.exists()
assert (area / 'final-claim-review/report.txt').is_file()


def digest(data):
    return hashlib.sha256(data).hexdigest()


documents = json.loads((area / 'document-paths.json').read_text())
records = json.loads((area / 'document-validation.json').read_text())
for record in records:
    name = record['path']
    data = (root / name).read_bytes()
    assert len(data) == record['bytes'] and digest(data) == record['sha256']
    if record.get('inserted_bytes') is not None:
        baseline = (area / 'prior-documents' / name).read_bytes()
        offset = record['offset']
        count = record['inserted_bytes']
        assert data[:offset] + data[offset+count:] == baseline
    target = area / 'current-documents' / name
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(data)
(area / 'current-document-changes.patch').write_bytes(subprocess.check_output(
    ['git', 'diff', '--', *documents], cwd=root))
for name in ['validate-flat-captured-edge', 'document-flat-captured-edge',
        'commit-flat-captured-edge-source', 'commit-flat-captured-edge-checkpoint',
        'verify-flat-captured-edge-evidence', 'freeze-flat-captured-edge',
        'publish-flat-captured-edge']:
    target = area / 'helpers' / (name + '.py')
    target.parent.mkdir(exist_ok=True)
    shutil.copyfile('/tmp/mcfta-' + name + '.py', target)
shutil.copyfile('/tmp/mcfta-verify-flat-captured-edge-evidence.py', area / 'verify-evidence.py')
snapshot.mkdir()
decoded = []
for path in sorted(area.rglob('*')):
    if not path.is_file():
        continue
    assert not path.is_symlink()
    data = path.read_bytes()
    relative = path.relative_to(area)
    target = snapshot / relative
    trailing = any(line.rstrip(b'\r\n').endswith((b' ', b'\t')) for line in data.splitlines(keepends=True))
    extra_blank = data.endswith((b'\n\n', b'\r\n\r\n'))
    if path.suffix in {'.log', '.patch'} or trailing or extra_blank or len(data) > 65536:
        target = target.with_name(target.name + '.gz')
        decoded.append({'original_path': str(relative), 'stored_path': str(target.relative_to(snapshot)),
            'bytes': len(data), 'sha256': digest(data)})
        data = gzip.compress(data, mtime=0)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(data)
(snapshot / 'decoded-files.json').write_text(json.dumps(decoded, indent=2) + '\n')
payloads = []
for path in sorted(snapshot.rglob('*')):
    if path.is_file():
        data = path.read_bytes()
        payloads.append({'path': str(path.relative_to(snapshot)), 'bytes': len(data), 'sha256': digest(data)})
manifest = {'source_head': (area / 'source-head.txt').read_text().strip(),
    'published_base': (area / 'published-base.txt').read_text().strip(), 'files': payloads}
(snapshot / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
result = {'snapshot': str(snapshot), 'payloads': len(payloads),
    'bytes': sum(record['bytes'] for record in payloads), 'archives': len(decoded),
    'manifest_sha256': digest((snapshot / 'manifest.json').read_bytes())}
Path('/tmp/mcfta-flat-captured-edge-snapshot.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result))
