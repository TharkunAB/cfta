from pathlib import Path
import hashlib
import json
import shutil
import tarfile

ROOT = Path('/home/tritlo/Code/mcfta')
AREA = Path('/tmp/mcfta-sibling-execution-path-control-20261030')
DEST = ROOT / 'lean/restart-evidence/20261030-sibling-execution-path-control'
DEST.mkdir(exist_ok=False)
seal = json.loads((AREA / 'FROZEN.json').read_text())
assert seal['write_halt'] is True and seal['goal_turn'] == 'progress'
expected = {row['path']: row for row in seal['payloads']}
paths = sorted(path for path in AREA.rglob('*') if path.is_file())
assert {str(path.relative_to(AREA)) for path in paths} == set(expected) | {'FROZEN.json'}
rows = []
for path in paths:
    assert not path.is_symlink() and not (path.stat().st_mode & 0o222)
    data = path.read_bytes()
    row = {'path': str(path.relative_to(AREA)), 'bytes': len(data),
           'sha256': hashlib.sha256(data).hexdigest()}
    if row['path'] != 'FROZEN.json':
        assert row == expected[row['path']]
    rows.append(row)
archive = DEST / 'evidence.tar.gz'
with tarfile.open(archive, 'w:gz', compresslevel=6) as target:
    for path in paths:
        target.add(path, arcname=str(path.relative_to(AREA)), recursive=False)
manifest = {'archive': archive.name, 'archive_bytes': archive.stat().st_size,
            'archive_sha256': hashlib.sha256(archive.read_bytes()).hexdigest(),
            'source_commit': seal['source_head'], 'docs_commit': seal['docs_head'],
            'payloads': rows}
(DEST / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
shutil.copyfile(ROOT / 'lean/restart-evidence/20261030-execution-path-control/verify.py', DEST / 'verify.py')
shutil.copyfile(__file__, DEST / 'package.py')
(DEST / 'README.md').write_text(f'''# Sibling execution paths: restart evidence

Source `{seal['source_head']}`. Documentation `{seal['docs_head']}`.
The full objective remains incomplete. Work continues.
All {len(rows)} regular payloads are retained without filtering.
Raw bytes: {sum(row['bytes'] for row in rows)}. Compressed bytes: {manifest['archive_bytes']}.
SHA256: `{manifest['archive_sha256']}`.

Verify or reconstruct from the repository root:

```sh
python3 lean/restart-evidence/20261030-sibling-execution-path-control/verify.py lean/restart-evidence/20261030-sibling-execution-path-control --extract /tmp/mcfta-sibling-execution-path-control-restored-20261030
```

Use a fresh destination. Omit `--extract` to verify only.
The verifier rejects duplicate, missing, extra, unsafe, and non-regular members.
It executes no Lean or Haskell. Keep source and reconstructed evidence read-only.
Extraction creates ordinary writable files. Remove their write bits before
running the contained ownership check. Give each metadata verifier a separate
writable output directory.
All 25 compiler commands remain, including four failed checks and their
replacements. There are 115 input snapshots. Five frozen reviews retain
203 payloads. The complete 140,163-byte new public
tail was read independently. All old public output and document bodies remain.
Thirteen laws are checked. The positive-depth whole-worker induction and
sufficient original recursion depth remain open. No Haskell source changed.

---

''' + (ROOT / 'lean/notes-current-sibling-execution-path-control.md').read_text())
print(json.dumps({'payloads': len(rows), 'raw_bytes': sum(row['bytes'] for row in rows),
                  'archive_bytes': manifest['archive_bytes'], 'archive_sha256': manifest['archive_sha256']}))
