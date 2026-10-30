from pathlib import Path
import hashlib,json,shutil,tarfile

ROOT=Path('/home/tritlo/Code/mcfta')
AREA=Path('/tmp/mcfta-slot-and-native-dispatch-control-20261031')
DEST=ROOT/'lean/restart-evidence/20261031-slot-dispatch-fold-control'
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
(DEST/'README.md').write_text(f'''# Dispatch, changed slots and fold certificates: restart evidence

Dispatch source `{seal['dispatch_source_head']}`.
Slot source `{seal['slot_source_head']}`.
Fold source `{seal['source_head']}`. Documentation `{seal['docs_head']}`.
The full original-input objective remains incomplete. Work continues.
All {len(rows)} regular payloads remain without filtering.
Raw bytes: {sum(a['bytes'] for a in rows)}. Compressed bytes: {manifest['archive_bytes']}.
SHA256: `{manifest['archive_sha256']}`.

Verify or reconstruct from the repository root:

```sh
python3 lean/restart-evidence/20261031-slot-dispatch-fold-control/verify.py lean/restart-evidence/20261031-slot-dispatch-fold-control --extract /tmp/mcfta-slot-and-native-dispatch-restored-20261031
```

Use a fresh destination. Omit --extract to verify only.
The verifier rejects duplicate, missing, extra, unsafe and non-regular members.
It executes no Lean or Haskell. Extraction creates writable ordinary files.
Remove their write bits before ownership checks. Give each metadata verifier
its own writable output directory. Current-source verification expects the
matching source and documentation checkout.

All final compiler checks pass. Nineteen commands retain fifteen passes and
four repaired failed probes. All 52 input snapshots remain.
Native Stored is preserved through every actual dispatch and Fold.run outcome.
All current context, slot and original-reservation gates remain explicit.
No future Ranges, output certificate or postcondition supplier is added.
The false check derives Frame. The changed-slot action derives returned Normal,
exact readback, the same allocated root and final PendingRealized.
Its actual read/check/lookup/prepare/newEncoded/change/success equations remain
inputs. It ends before adaptation/index/Right recording. It does not extract
those equations from a final runPrefix result or prove a global history bound.
Independent review reads all 413 source lines and 137 new public lines.
All four axiom reports use standard axioms. All prior public output and full
old root documents remain exact prefixes or suffixes respectively.
Complete owners, reused providers, original drafts, repairs and failed logs remain.
Complete Terminal152L and adapter63L owners remain UNCOMPILED future work.
Sufficient original depth, ordered global coverage, public adapters and Haskell
correspondence remain open. No Haskell source changed or native command ran.

---

'''+(ROOT/'lean/notes-current-slot-and-native-dispatch.md').read_text())
print(json.dumps({'payloads':len(rows),'raw_bytes':sum(a['bytes'] for a in rows),'archive_bytes':manifest['archive_bytes'],'archive_sha256':manifest['archive_sha256']}))
