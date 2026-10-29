"""Archive every sealed checked query and tuple-budget evidence file."""
from pathlib import Path
import hashlib,json,shutil,tarfile

ROOT=Path('/home/tritlo/Code/mcfta')
SOURCE=Path('/tmp/mcfta-checked-prefix-progress-20261029')
DEST=ROOT/'lean/restart-evidence/20261029-checked-prefix-progress'
DEST.mkdir(exist_ok=False)
seal=json.loads((SOURCE/'FROZEN.json').read_text())
assert seal['write_halt'] and seal['full_goal']=='active'
expected={v['path']:v for v in seal['payloads']}
assert len(expected)==len(seal['payloads'])
paths=sorted(p for p in SOURCE.rglob('*') if p.is_file())
assert {str(p.relative_to(SOURCE)) for p in paths}==set(expected)|{'FROZEN.json'}
records=[]
for path in paths:
    assert not path.is_symlink()
    data=path.read_bytes()
    record=dict(path=str(path.relative_to(SOURCE)),bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
    if record['path']!='FROZEN.json':assert record==expected[record['path']]
    records.append(record)
archive=DEST/'evidence.tar.gz'
with tarfile.open(archive,'w:gz',compresslevel=6) as target:
    for path in paths:target.add(path,arcname=str(path.relative_to(SOURCE)),recursive=False)
manifest=dict(archive=archive.name,archive_bytes=archive.stat().st_size,archive_sha256=hashlib.sha256(archive.read_bytes()).hexdigest(),source_commit=seal['source_head'],docs_commit=seal['docs_head'],payloads=records)
(DEST/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
shutil.copyfile(ROOT/'lean/restart-evidence/20261029-recursive-ancestry-progress/verify.py',DEST/'verify.py')
shutil.copyfile(__file__,DEST/'package.py')
readme=f'''# Checked query prefix bounds and tuple-budget emptiness: complete restart evidence

Source `{seal['source_head']}`. Documentation `{seal['docs_head']}`.
The full formalization objective remains ACTIVE on formalize.
Every sealed regular file is archived without a filter.
The manifest binds all {len(records):,} paths, byte counts and hashes.
Raw bytes: {sum(v['bytes'] for v in records):,}.
Compressed bytes: {manifest['archive_bytes']:,}.
SHA256: `{manifest['archive_sha256']}`.

Verify or reconstruct from the repository root:

```sh
python3 lean/restart-evidence/20261029-checked-prefix-progress/verify.py lean/restart-evidence/20261029-checked-prefix-progress --extract /tmp/mcfta-checked-prefix-progress-restored
```

Use a fresh destination. Omit --extract to verify only. The standard-library
verifier rejects duplicate, missing, extra, unsafe and non-regular members.
It executes no Lean or Haskell code. Keep reconstructed evidence immutable.
Continue in a new writable area. The original source area is sealed read-only.
Historical UNTESTED labels and failed drafts remain. Final strict mappings
identify the exact six checked sources. All 107 command input snapshots match.
The note below specifies the result, conditions, failures and remaining gaps.

---

'''
(DEST/'README.md').write_text(readme+(ROOT/'lean/notes-current-checked-prefix-progress.md').read_text())
print(json.dumps(dict(payloads=len(records),raw_bytes=sum(v['bytes']for v in records),archive_bytes=manifest['archive_bytes'],archive_sha256=manifest['archive_sha256'])))
