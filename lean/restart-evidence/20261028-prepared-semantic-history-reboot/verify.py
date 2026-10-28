"""Verify or reconstruct a saved reboot evidence snapshot."""
from pathlib import Path
import argparse
import hashlib
import json
import tarfile

parser = argparse.ArgumentParser()
parser.add_argument('snapshot',type=Path)
parser.add_argument('--extract',type=Path)
args = parser.parse_args()
manifest = json.loads((args.snapshot/'manifest.json').read_text())
archive = args.snapshot/manifest['archive']
assert archive.stat().st_size == manifest['archive_bytes']
assert hashlib.sha256(archive.read_bytes()).hexdigest() == manifest['archive_sha256']
expected = {record['path']:record for record in manifest['payloads']}
assert len(expected) == len(manifest['payloads'])
if args.extract:
    args.extract.mkdir(parents=True,exist_ok=False)
seen = set()
with tarfile.open(archive,'r:gz') as tar:
    for member in tar:
        assert member.isfile() and member.name in expected and member.name not in seen
        relative = Path(member.name)
        assert not relative.is_absolute() and '..' not in relative.parts
        raw = tar.extractfile(member).read()
        record = expected[member.name]
        assert len(raw) == record['bytes'] and hashlib.sha256(raw).hexdigest() == record['sha256']
        if args.extract:
            target = args.extract/relative
            target.parent.mkdir(parents=True,exist_ok=True)
            target.write_bytes(raw)
        seen.add(member.name)
assert seen == set(expected)
print(json.dumps({'status':'pass','payloads':len(seen),'archive_sha256':manifest['archive_sha256'],'reconstructed':str(args.extract) if args.extract else None}))
