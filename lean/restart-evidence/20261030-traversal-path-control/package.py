from pathlib import Path
import hashlib, json, shutil, tarfile

ROOT = Path('/home/tritlo/Code/mcfta')
AREA = Path('/tmp/mcfta-traversal-path-control-20261030')
DEST = ROOT / 'lean/restart-evidence/20261030-traversal-path-control'
DEST.mkdir(exist_ok=False)
seal = json.loads((AREA / 'FROZEN.json').read_text())
assert seal['write_halt'] and seal['full_goal'] == 'active'
expected = {row['path']: row for row in seal['payloads']}
paths = sorted(path for path in AREA.rglob('*') if path.is_file())
assert {str(path.relative_to(AREA)) for path in paths} == set(expected) | {'FROZEN.json'}
rows = []
for path in paths:
    assert not path.is_symlink()
    data = path.read_bytes()
    row = dict(path=str(path.relative_to(AREA)), bytes=len(data), sha256=hashlib.sha256(data).hexdigest())
    if row['path'] != 'FROZEN.json':
        assert row == expected[row['path']]
    rows.append(row)
archive = DEST / 'evidence.tar.gz'
with tarfile.open(archive, 'w:gz', compresslevel=6) as target:
    for path in paths:
        target.add(path, arcname=str(path.relative_to(AREA)), recursive=False)
manifest = dict(archive=archive.name, archive_bytes=archive.stat().st_size,
    archive_sha256=hashlib.sha256(archive.read_bytes()).hexdigest(), source_commit=seal['source_head'],
    docs_commit=seal['docs_head'], payloads=rows)
(DEST / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
shutil.copyfile(ROOT / 'lean/restart-evidence/20261030-finite-prefix-control/verify.py', DEST / 'verify.py')
shutil.copyfile(__file__, DEST / 'package.py')
(DEST / 'README.md').write_text(f'''# Child observation paths: restart evidence

Full goal ACTIVE. Source `{seal['source_head']}`. Documentation `{seal['docs_head']}`.
All {len(rows)} regular payloads are retained without filtering.
Raw bytes: {sum(row['bytes'] for row in rows)}. Compressed bytes: {manifest['archive_bytes']}.
SHA256: `{manifest['archive_sha256']}`.

Verify or reconstruct from the repository root:

```sh
python3 lean/restart-evidence/20261030-traversal-path-control/verify.py lean/restart-evidence/20261030-traversal-path-control --extract /tmp/mcfta-traversal-path-control-restored
```

Use a fresh destination. Omit `--extract` to verify only.
The verifier rejects duplicate, missing, extra, unsafe, and non-regular members.
It executes no Lean or Haskell.
Keep source and reconstructed evidence read-only.
Both failed opaque matcher drafts, the precompiler bus-launch failure, and exact repaired versions remain.
The whole-worker source-review proposal remains explicitly UNCOMPILED.
No Haskell source changed. The full goal stays active.

---

''' + (ROOT / 'lean/notes-current-traversal-path-control.md').read_text())
print(json.dumps(dict(payloads=len(rows), raw_bytes=sum(row['bytes'] for row in rows),
    archive_bytes=manifest['archive_bytes'], archive_sha256=manifest['archive_sha256'])))
