import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
parser = argparse.ArgumentParser()
parser.add_argument('--remote-file', type=Path)
args = parser.parse_args()


def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)


assert git('status', '--porcelain') == b''
head = git('rev-parse', 'HEAD').decode().strip()
records = git('ls-tree', '-r', '--full-tree', '-z', 'HEAD').split(b'\0')
expected_index = {}
for record in records:
    if not record:
        continue
    meta, raw = record.split(b'\t', 1)
    mode, kind, oid = meta.split()
    assert kind == b'blob'
    path = ROOT / os.fsdecode(raw)
    data = os.fsencode(os.readlink(path)) if mode == b'120000' else path.read_bytes()
    assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest().encode() == oid
    if mode in [b'100644', b'100755']:
        assert bool(path.stat().st_mode & 0o111) == (mode == b'100755')
    expected_index[raw] = (mode, oid)
actual_index = {}
for record in git('ls-files', '--stage', '-z').split(b'\0'):
    if record:
        meta, raw = record.split(b'\t', 1)
        mode, oid, stage = meta.split()
        assert stage == b'0'
        actual_index[raw] = (mode, oid)
assert actual_index == expected_index
checks = set()
for line in (HERE / 'SHA256SUMS').read_text().splitlines():
    digest, name = line.split('  ', 1)
    assert hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == digest
    assert os.fsencode(name) in expected_index
    checks.add(name)
assert checks == {str(path.relative_to(ROOT)) for path in HERE.rglob('*') if path.is_file() and path.name != 'SHA256SUMS'}
for entry in json.loads((HERE / 'root-scope-manifest.json').read_text())['entries']:
    data = (ROOT / entry['path']).read_bytes()
    assert len(data) == entry['bytes'] and hashlib.sha256(data).hexdigest() == entry['sha256']
verification = json.loads(subprocess.check_output(['python3', str(HERE / 'verify-integration.py')], cwd=ROOT))
assert verification == json.loads((HERE / 'integration-verification.json').read_text())
report = dict(head=head, tracked_blobs_and_modes=len(expected_index), filesystem_index_head_equal=True,
              evidence_checksums=len(checks), integration_verification_matches=True, clean=True,
              imported_main=verification['imported_main'])
if args.remote_file:
    remote = dict(line.split()[::-1] for line in args.remote_file.read_text().splitlines())
    assert remote['refs/heads/formalize'] == head
    assert 'refs/heads/main' in remote
    report.update(remote=remote, newer_upstream_main_observed=remote['refs/heads/main'] != verification['imported_main'])
print(json.dumps(report, indent=2))
