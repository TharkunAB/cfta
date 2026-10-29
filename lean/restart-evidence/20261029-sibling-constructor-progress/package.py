"""Archive every sealed actual prepared sibling evidence file."""
from pathlib import Path
import hashlib, json, shutil, tarfile

ROOT = Path('/home/tritlo/Code/mcfta')
SOURCE = Path('/tmp/mcfta-sibling-constructor-progress-20261029')
DEST = ROOT / 'lean/restart-evidence/20261029-sibling-constructor-progress'
DEST.mkdir(exist_ok=False)
seal = json.loads((SOURCE / 'FROZEN.json').read_text())
assert seal['write_halt'] and seal['full_goal'] == 'active'
expected = {row['path']: row for row in seal['payloads']}
assert len(expected) == len(seal['payloads'])
paths = sorted(path for path in SOURCE.rglob('*') if path.is_file())
assert {str(path.relative_to(SOURCE)) for path in paths} == set(expected) | {'FROZEN.json'}
records = []
for path in paths:
    assert not path.is_symlink(); data = path.read_bytes()
    row = dict(path=str(path.relative_to(SOURCE)), bytes=len(data), sha256=hashlib.sha256(data).hexdigest())
    if row['path'] != 'FROZEN.json': assert row == expected[row['path']]
    records.append(row)
archive = DEST / 'evidence.tar.gz'
with tarfile.open(archive, 'w:gz', compresslevel=6) as target:
    for path in paths: target.add(path, arcname=str(path.relative_to(SOURCE)), recursive=False)
manifest = dict(archive=archive.name, archive_bytes=archive.stat().st_size, archive_sha256=hashlib.sha256(archive.read_bytes()).hexdigest(), source_commit=seal['source_head'], docs_commit=seal['docs_head'], payloads=records)
(DEST / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
shutil.copyfile(ROOT / 'lean/restart-evidence/20261029-recursive-ancestry-progress/verify.py', DEST / 'verify.py')
shutil.copyfile(__file__, DEST / 'package.py')
readme = f'''# Actual prepared sibling progress: complete restart evidence

Source `{seal['source_head']}`. Documentation `{seal['docs_head']}`.
The full formalization objective remains ACTIVE on formalize.
Every sealed regular file is archived without a filter.
The manifest binds all {len(records):,} paths, byte counts and hashes.
Raw bytes: {sum(row['bytes'] for row in records):,}.
Compressed bytes: {manifest['archive_bytes']:,}.
SHA256: `{manifest['archive_sha256']}`.

Verify or reconstruct from the repository root:

```sh
python3 lean/restart-evidence/20261029-sibling-constructor-progress/verify.py lean/restart-evidence/20261029-sibling-constructor-progress --extract /tmp/mcfta-sibling-constructor-progress-restored
```

Use a fresh destination. Omit --extract to verify only. The standard-library
verifier rejects duplicate, missing, extra, unsafe and non-regular members.
It executes no Lean or Haskell code. Keep reconstructed evidence immutable.
Continue in a new writable area. The original source area is sealed read-only.
Historical labels and both failed import drafts remain. Three final strict source
mappings identify the checked repairs. All24 command input snapshots match.
The note below states the result, admissions, failures and remaining gaps.

---

'''
(DEST / 'README.md').write_text(readme + (ROOT / 'lean/notes-current-sibling-constructor-progress.md').read_text())
print(json.dumps(dict(payloads=len(records), raw_bytes=sum(row['bytes'] for row in records), archive_bytes=manifest['archive_bytes'], archive_sha256=manifest['archive_sha256'])))
