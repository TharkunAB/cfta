from pathlib import Path
import hashlib,json,shutil,tarfile
ROOT=Path('/home/tritlo/Code/mcfta');AREA=Path('/tmp/mcfta-native-binding-and-constraint-control-20261031');DEST=ROOT/'lean/restart-evidence/20261031-native-binding-and-constraint-control';DEST.mkdir(exist_ok=False);seal=json.loads((AREA/'FROZEN.json').read_text());assert seal['write_halt'] is True and seal['goal_turn']=='progress';expected={a['path']:a for a in seal['payloads']};paths=sorted(p for p in AREA.rglob('*') if p.is_file());assert {str(p.relative_to(AREA)) for p in paths}==set(expected)|{'FROZEN.json'};rows=[]
for p in paths:
 assert not p.is_symlink() and not p.stat().st_mode&0o222;b=p.read_bytes();row={'path':str(p.relative_to(AREA)),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
 if row['path']!='FROZEN.json':assert row==expected[row['path']]
 rows.append(row)
archive=DEST/'evidence.tar.gz'
with tarfile.open(archive,'w:gz',compresslevel=6) as target:
 for p in paths:target.add(p,arcname=str(p.relative_to(AREA)),recursive=False)
manifest={'archive':archive.name,'archive_bytes':archive.stat().st_size,'archive_sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),'source_commit':seal['source_head'],'docs_commit':seal['docs_head'],'payloads':rows};(DEST/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');shutil.copyfile(ROOT/'lean/restart-evidence/20261030-neutral-recording-control/verify.py',DEST/'verify.py');shutil.copyfile(__file__,DEST/'package.py');(DEST/'README.md').write_text(f'''# Native bindings and constraint startup: restart evidence

Source `{seal['source_head']}`. Documentation `{seal['docs_head']}`.
The full original-input objective remains open. Work continues.
All {len(rows)} regular payloads remain without filtering.
Raw bytes: {sum(a['bytes'] for a in rows)}. Compressed bytes: {manifest['archive_bytes']}.
SHA256: `{manifest['archive_sha256']}`.

Verify or reconstruct from the repository root:

```sh
python3 lean/restart-evidence/20261031-native-binding-and-constraint-control/verify.py lean/restart-evidence/20261031-native-binding-and-constraint-control --extract /tmp/mcfta-native-binding-and-constraint-restored-20261031
```

Use a fresh destination. Omit --extract to verify only.
The verifier rejects duplicate, missing, extra, unsafe and non-regular members.
It executes no Lean or Haskell. Make restored files read-only before owner checks.
Give each metadata verifier a separate writable output directory.
Use the matching source and documentation checkout.
Run verify-current.py, verify-owned.py, verify-documents.py,
verify-peer-replay.py and verify-prior-evidence.py from the restored area.

Seven new modules derive the full current Nat constraint numeric filter and
actual computed startup. They classify actual ordinary native query results,
None/child slot creation, strict canonical child grades and actual Some/Some
representative-slot writes with checkEmpty=false. An auxiliary signed codec
preserves all index/path identities and bounded lookup. These are local laws.
No caller supplies a minimum table, equality view or future native receipt.
Original warm Stored, physical availability and resource gates remain explicit.

Audit default/strict passes 4785 jobs and 83418 theorem dependency checks.
Public passes 1295 checks and 155 definition prints. All 19 new reports are
standard-only. The old 4997063 public bytes remain an exact prefix.
Root read all 699 final source lines and the 433-line/31009-byte public tail.
Independent source/public/doc review is CLEAR. All 26 compiler attempts remain:
18 passes and eight repaired failures, with all 168 input snapshots.
Every dispatch had effective 4 GiB memory/high, zero swap and a five-minute cap.
All 579 old protected sources and 835 native inputs remain exact.
Audit alone adds imports to its old body.

All 15 current full owner bundles remain, including four source-only future
drafts: whole incoming Known/Stored, arbitrary emptiness checking, None-fill and
canonical interned edge origin. These four drafts are UNCOMPILED.
All complete private providers referenced by current owners remain.
The complete prior R16 archive and its 24 owner bundles remain in Git.
prior-evidence.json pins all five of its archive files. It is not silently
replaced by the smaller current owner set.

Whole cache/terminal/alias/renewal transport, sufficient ORIGINAL depth/progress
for both workers, original Map/domain/order and signed normalization adapters,
generic Mu/Union/opaque sources, accepted public membership/coverage/configured
order/stops/intended prefix/resources and full Haskell correspondence remain
open. A root height cap is not a whole-worker resource bound.
No Haskell source changed and no Haskell/native product program ran.
No new Haskell defect or fix was established. Record later Haskell fixes in FINDINGS.

---

'''+(ROOT/'lean/notes-current-native-bindings-and-constraint-startup.md').read_text());print(json.dumps({'payloads':len(rows),'raw_bytes':sum(a['bytes'] for a in rows),'archive_bytes':manifest['archive_bytes'],'archive_sha256':manifest['archive_sha256']}))
