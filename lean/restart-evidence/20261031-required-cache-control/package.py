from pathlib import Path
import hashlib,json,shutil,tarfile
ROOT=Path('/home/tritlo/Code/mcfta');AREA=Path('/tmp/mcfta-required-cache-control-20261031');DEST=ROOT/'lean/restart-evidence/20261031-required-cache-control';DEST.mkdir(exist_ok=False);seal=json.loads((AREA/'FROZEN.json').read_text());assert seal['write_halt'] is True and seal['goal_turn']=='progress';expected={a['path']:a for a in seal['payloads']};paths=sorted(p for p in AREA.rglob('*') if p.is_file());assert {str(p.relative_to(AREA)) for p in paths}==set(expected)|{'FROZEN.json'};rows=[]
for p in paths:
 assert not p.is_symlink() and not p.stat().st_mode&0o222;b=p.read_bytes();row={'path':str(p.relative_to(AREA)),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
 if row['path']!='FROZEN.json':assert row==expected[row['path']]
 rows.append(row)
archive=DEST/'evidence.tar.gz'
with tarfile.open(archive,'w:gz',compresslevel=6) as target:
 for p in paths:target.add(p,arcname=str(p.relative_to(AREA)),recursive=False)
manifest={'archive':archive.name,'archive_bytes':archive.stat().st_size,'archive_sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),'source_commit':seal['source_head'],'docs_commit':seal['docs_head'],'payloads':rows};(DEST/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');shutil.copyfile(ROOT/'lean/restart-evidence/20261030-neutral-recording-control/verify.py',DEST/'verify.py');shutil.copyfile(__file__,DEST/'package.py')
readme=f"""# Terminal cache and required-reader effects: restart evidence

Source `{seal['source_head']}`. Documentation `{seal['docs_head']}`.
The full original-input objective remains open. Work continues.
All {len(rows)} regular payloads remain without filtering.
Raw bytes: {sum(a['bytes'] for a in rows)}. Compressed bytes: {manifest['archive_bytes']}.
SHA256: `{manifest['archive_sha256']}`.

Verify or reconstruct from the repository root:

```sh
python3 lean/restart-evidence/20261031-required-cache-control/verify.py lean/restart-evidence/20261031-required-cache-control --extract /tmp/mcfta-required-cache-restored-20261031
```

Use a fresh destination. Omit --extract to verify only.
The verifier rejects duplicate, missing, extra, unsafe and non-regular members.
It executes no Lean or Haskell. Make restored files read-only before owner checks.
Give each metadata verifier a separate writable output directory.
Use the matching source and documentation checkout.
Run verify-current.py, verify-owned.py, verify-documents.py,
verify-peer-replay.py and verify-prior-evidence.py from the restored area.

Five installed modules pass default, strict, full Audit and public checks.
They cover actual successful terminal and incoming raw rows and Some caches,
the literal staged ordinary incoming child producer, and secondary required-reader effects.
Known concerns encoded pending Some handles under explicit current admissions.
The actual CURRENT failed-check path uses CurrentRows and ProjectionWorker.forest.
SharedTarget/ClassFold is a separate legacy route. Its corrected complete review remains.
Fixed-original-D full worker Post/admissions/resources BOTHworkers remain open.
The SAME captured sibling cache needs preservation at the ACTUAL after-hook Caller/query pair.
Prepared raw failure heaps do not imply an exposed outer Caller.
All {seal['owners']} complete owner bundles and all private provider closures remain.
Any future current-rows candidate remains source-only and UNCOMPILED here.
The immutable 34-owner peer-input snapshot is historical and remains exact.
Later source-only providers and the current peer do not alter that snapshot.
The complete prior R19 archive remains in Git with all 29 complete owners.
prior-evidence.json pins all five archive files and its 2638 regular payloads.
No Haskell source changed and no Haskell/native product program ran.
No new Haskell defect or fix was established. Record later Haskell fixes in FINDINGS.

---

"""
(DEST/'README.md').write_text(readme+(ROOT/'lean/notes-current-terminal-cache-and-required-effects.md').read_text());print(json.dumps({'payloads':len(rows),'raw_bytes':sum(a['bytes'] for a in rows),'archive_bytes':manifest['archive_bytes'],'archive_sha256':manifest['archive_sha256']}))
