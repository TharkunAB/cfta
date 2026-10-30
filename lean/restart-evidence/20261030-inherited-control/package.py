from pathlib import Path
import hashlib,json,shutil,tarfile

ROOT=Path('/home/tritlo/Code/mcfta')
AREA=Path('/tmp/mcfta-inherited-control-20261030')
DEST=ROOT/'lean/restart-evidence/20261030-inherited-control'
DEST.mkdir(exist_ok=False)
seal=json.loads((AREA/'FROZEN.json').read_text())
assert seal['write_halt'] and seal['full_goal']=='active'
expected={r['path']:r for r in seal['payloads']}
paths=sorted(p for p in AREA.rglob('*') if p.is_file())
assert {str(p.relative_to(AREA)) for p in paths}==set(expected)|{'FROZEN.json'}
rows=[]
for path in paths:
    assert not path.is_symlink()
    data=path.read_bytes()
    row=dict(path=str(path.relative_to(AREA)),bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
    if row['path']!='FROZEN.json':assert row==expected[row['path']]
    rows.append(row)
archive=DEST/'evidence.tar.gz'
with tarfile.open(archive,'w:gz',compresslevel=6) as target:
    for path in paths:target.add(path,arcname=str(path.relative_to(AREA)),recursive=False)
manifest=dict(archive=archive.name,archive_bytes=archive.stat().st_size,
    archive_sha256=hashlib.sha256(archive.read_bytes()).hexdigest(),source_commit=seal['source_head'],
    docs_commit=seal['docs_head'],payloads=rows)
(DEST/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
shutil.copyfile(ROOT/'lean/restart-evidence/20261030-normalization-control/verify.py',DEST/'verify.py')
shutil.copyfile(__file__,DEST/'package.py')
(DEST/'README.md').write_text(f'''# Inherited payload operations and recursive control: restart evidence

Full goal ACTIVE. Source{seal['source_head']}. Documentation{seal['docs_head']}.
All{len(rows)} regular payloads are retained without filtering.
Raw bytes:{sum(r['bytes'] for r in rows)}. Compressed bytes:{manifest['archive_bytes']}.
SHA256:{manifest['archive_sha256']}.

Verify or reconstruct from the repository root:

```sh
python3 lean/restart-evidence/20261030-inherited-control/verify.py lean/restart-evidence/20261030-inherited-control --extract /tmp/mcfta-inherited-control-restored
```

Use a fresh destination. Omit --extract to verify only. The verifier rejects
duplicate, missing, extra, unsafe and non-regular members. It executes no Lean
or Haskell. Keep the source area and reconstructed evidence immutable.
All twelve failed proof drafts and diagnostics remain. Both native checks pass.
The prior protected proof sources remain unchanged. The full goal is active.

---

'''+(ROOT/'lean/notes-current-inherited-control.md').read_text())
print(json.dumps(dict(payloads=len(rows),raw_bytes=sum(r['bytes'] for r in rows),
    archive_bytes=manifest['archive_bytes'],archive_sha256=manifest['archive_sha256'])))
