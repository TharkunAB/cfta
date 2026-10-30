from pathlib import Path
import hashlib,json,shutil,tarfile

ROOT=Path('/home/tritlo/Code/mcfta')
AREA=Path('/tmp/mcfta-native-memo-stored-control-20261030')
DEST=ROOT/'lean/restart-evidence/20261030-native-memo-stored-control'
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
(DEST/'README.md').write_text(f'''# Native conditional cache preservation: restart evidence

Source `{seal['source_head']}`. Documentation `{seal['docs_head']}`.
The full objective remains incomplete. Work continues.
All {len(rows)} regular payloads remain without filtering.
Raw bytes: {sum(a['bytes'] for a in rows)}. Compressed bytes: {manifest['archive_bytes']}.
SHA256: `{manifest['archive_sha256']}`.

Verify or reconstruct from the repository root:

```sh
python3 lean/restart-evidence/20261030-native-memo-stored-control/verify.py lean/restart-evidence/20261030-native-memo-stored-control --extract /tmp/mcfta-native-memo-stored-control-restored-20261030
```

Use a fresh destination. Omit --extract to verify only.
The verifier rejects duplicate, missing, extra, unsafe and non-regular members.
It executes no Lean or Haskell. Extraction creates writable ordinary files.
Remove their write bits before ownership checks. Give each metadata verifier
a separate writable output directory. Current-source verification expects
the matching source and documentation checkout.

All seven compiler commands pass. All twelve input snapshots remain.
Six conditional native cache preservation laws are checked. They consume
completed checked traces or existing receipts. They do not prove future
completion, arbitrary unfinished prefixes, sufficient original recursive
depth or Haskell correspondence. All previous worker and recording laws remain.
The independent public review read the complete source and new public tail.
All source-only incidents, failed metadata verifier versions, original drafts,
full public output and prior document bodies remain. No compiler check failed.
The next preparation review is retained in full as UNCOMPILED future work.
No Haskell source changed and no native command ran.

---

'''+(ROOT/'lean/notes-current-native-memo-stored-control.md').read_text())
print(json.dumps({'payloads':len(rows),'raw_bytes':sum(a['bytes'] for a in rows),'archive_bytes':manifest['archive_bytes'],'archive_sha256':manifest['archive_sha256']}))
