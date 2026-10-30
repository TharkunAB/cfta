from pathlib import Path
import hashlib,json,shutil,tarfile

ROOT=Path('/home/tritlo/Code/mcfta')
AREA=Path('/tmp/mcfta-native-stored-prefix-control-20261030')
DEST=ROOT/'lean/restart-evidence/20261030-native-stored-prefix-control'
DEST.mkdir(exist_ok=False)
seal=json.loads((AREA/'FROZEN.json').read_text())
assert seal['write_halt'] is True and seal['goal_turn']=='progress'
expected={a['path']:a for a in seal['payloads']}
paths=sorted(p for p in AREA.rglob('*') if p.is_file())
assert {str(p.relative_to(AREA)) for p in paths}==set(expected)|{'FROZEN.json'}
rows=[]
for p in paths:
    assert not p.is_symlink() and not(p.stat().st_mode&0o222)
    b=p.read_bytes();a={'path':str(p.relative_to(AREA)),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
    if a['path']!='FROZEN.json':assert a==expected[a['path']]
    rows.append(a)
archive=DEST/'evidence.tar.gz'
with tarfile.open(archive,'w:gz',compresslevel=6) as target:
    for p in paths:target.add(p,arcname=str(p.relative_to(AREA)),recursive=False)
manifest={'archive':archive.name,'archive_bytes':archive.stat().st_size,'archive_sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),'source_commit':seal['source_head'],'docs_commit':seal['docs_head'],'payloads':rows}
(DEST/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
shutil.copyfile(ROOT/'lean/restart-evidence/20261030-neutral-recording-control/verify.py',DEST/'verify.py')
shutil.copyfile(__file__,DEST/'package.py')
(DEST/'README.md').write_text(f'''# Native prefix and actual returned control: restart evidence

Source `{seal['source_head']}`. Documentation `{seal['docs_head']}`.
The full objective remains incomplete. Work continues.
All {len(rows)} regular payloads remain without filtering.
Raw bytes: {sum(a['bytes'] for a in rows)}. Compressed bytes: {manifest['archive_bytes']}.
SHA256: `{manifest['archive_sha256']}`.

Verify or reconstruct from the repository root:

```sh
python3 lean/restart-evidence/20261030-native-stored-prefix-control/verify.py lean/restart-evidence/20261030-native-stored-prefix-control --extract /tmp/mcfta-native-stored-prefix-control-restored-20261030
```

Use a fresh destination. Omit --extract to verify only.
The verifier rejects duplicate, missing, extra, unsafe and non-regular members.
It executes no Lean or Haskell. Extraction creates writable ordinary files.
Remove their write bits before ownership checks. Give each metadata verifier
a separate writable output directory. Current-source verification expects
the matching source and documentation checkout.

All final compiler checks pass. Twelve commands retain nine passes and
three repaired failed probes. All twenty-seven input snapshots remain.
Five laws preserve conditional native certificates at arbitrary observed
checked prefixes and actual terminal returned states. Yielded concludes True.
Three laws derive stable actual successful narrowing results, physical Normal,
retained rows and same-key replay. Changed prepare results derive their own
filter branch. Empty can still select rejection. Action execution is separate.
The independent review read all 457 installed source lines and 190 new output
lines. All eight reports use standard axioms. All prior public output, full
old root documents, uncompiled originals, repairs and failed logs remain.
All owner payloads and historical dependency manifests remain.
No sufficient original depth, global reset bound, unrestricted raw execution
or Haskell correspondence is proved. No Haskell source changed or native ran.

---

'''+(ROOT/'lean/notes-current-native-prefix-and-returned-control.md').read_text())
print(json.dumps({'payloads':len(rows),'raw_bytes':sum(a['bytes'] for a in rows),'archive_bytes':manifest['archive_bytes'],'archive_sha256':manifest['archive_sha256']}))
