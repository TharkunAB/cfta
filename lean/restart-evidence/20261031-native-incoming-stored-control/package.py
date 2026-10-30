from pathlib import Path
import hashlib,json,shutil,tarfile

ROOT=Path('/home/tritlo/Code/mcfta')
AREA=Path('/tmp/mcfta-native-incoming-stored-control-20261030')
DEST=ROOT/'lean/restart-evidence/20261031-native-incoming-stored-control'
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
(DEST/'README.md').write_text(f'''# Actual incoming native certificates: restart evidence

Incoming source `{seal['incoming_source_head']}`.
Cache-adapter source `{seal['source_head']}`. Documentation `{seal['docs_head']}`.
The full original-input objective remains incomplete. Work continues.
All {len(rows)} regular payloads remain without filtering.
Raw bytes: {sum(a['bytes'] for a in rows)}. Compressed bytes: {manifest['archive_bytes']}.
SHA256: `{manifest['archive_sha256']}`.

Verify or reconstruct from the repository root:

```sh
python3 lean/restart-evidence/20261031-native-incoming-stored-control/verify.py lean/restart-evidence/20261031-native-incoming-stored-control --extract /tmp/mcfta-native-incoming-stored-control-restored-20261031
```

Use a fresh destination. Omit --extract to verify only.
The verifier rejects duplicate, missing, extra, unsafe and non-regular members.
It executes no Lean or Haskell. Extraction creates writable ordinary files.
Remove their write bits before ownership checks. Give each metadata verifier
its own writable output directory. Current-source verification expects the
matching source and documentation checkout.

All final compiler checks pass. Fifteen commands retain twelve passes and
three repaired failed incoming probes. All 31 input snapshots remain.
Two laws preserve conditional native Stored through actual IncomingNode.run
and the actual cache adapter for every supplied fuel and both checkEmpty modes.
Current Ready/Realized/Available/closed/Fits/Room/entry Stored gates remain.
No future Trace, WordRanges, output certificate or completion supplier is added.
The cache adapter adds no index-validity premise.
Independent review reads all 146 source lines and 63 new public lines.
Both new axiom reports use standard axioms. All prior public output and all
full old root documents remain exact prefixes or suffixes respectively.
Complete owners, original drafts, repairs, failed logs and provenance remain.
Unproved exact Dispatch/Fold targets remain in the cache-adapter owner bundle.
Sufficient original depth, actual whole-worker history transport, public
adapters and Haskell correspondence remain open.
No Haskell source changed. No native command ran.

---

'''+(ROOT/'lean/notes-current-native-incoming-stored.md').read_text())
print(json.dumps({'payloads':len(rows),'raw_bytes':sum(a['bytes'] for a in rows),'archive_bytes':manifest['archive_bytes'],'archive_sha256':manifest['archive_sha256']}))
