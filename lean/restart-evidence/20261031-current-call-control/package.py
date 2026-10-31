from pathlib import Path
import hashlib,json,shutil,tarfile
ROOT=Path('/home/tritlo/Code/mcfta');AREA=Path('/tmp/mcfta-current-call-control-20261031');DEST=ROOT/'lean/restart-evidence/20261031-current-call-control';DEST.mkdir(exist_ok=False);seal=json.loads((AREA/'FROZEN.json').read_text());assert seal['write_halt'] is True and seal['goal_turn']=='progress';expected={a['path']:a for a in seal['payloads']};paths=sorted(p for p in AREA.rglob('*') if p.is_file());assert {str(p.relative_to(AREA)) for p in paths}==set(expected)|{'FROZEN.json'};rows=[]
for p in paths:
 assert not p.is_symlink() and not p.stat().st_mode&0o222;b=p.read_bytes();row={'path':str(p.relative_to(AREA)),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
 if row['path']!='FROZEN.json':assert row==expected[row['path']]
 rows.append(row)
archive=DEST/'evidence.tar.gz'
with tarfile.open(archive,'w:gz',compresslevel=6) as target:
 for p in paths:target.add(p,arcname=str(p.relative_to(AREA)),recursive=False)
manifest={'archive':archive.name,'archive_bytes':archive.stat().st_size,'archive_sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),'source_commit':seal['source_head'],'docs_commit':seal['docs_head'],'payloads':rows};(DEST/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');shutil.copyfile(ROOT/'lean/restart-evidence/20261030-neutral-recording-control/verify.py',DEST/'verify.py');shutil.copyfile(__file__,DEST/'package.py')
readme=f"""# Actual current-call effects and conservative memo soundness: restart evidence

Source `{seal['source_head']}`. Documentation `{seal['docs_head']}`.
The original-input system objective remains open. The goal remains ACTIVE.
All {len(rows)} regular payloads remain without filtering.
Raw bytes: {sum(a['bytes'] for a in rows)}. Compressed bytes: {manifest['archive_bytes']}.
SHA256: `{manifest['archive_sha256']}`.

Verify or reconstruct from the repository root:

```sh
python3 lean/restart-evidence/20261031-current-call-control/verify.py lean/restart-evidence/20261031-current-call-control --extract /tmp/mcfta-current-call-restored-20261031
```

Use a fresh destination. Omit --extract to verify only.
The verifier rejects duplicate, missing, extra, unsafe and non-regular members.
It executes no Lean or Haskell. Make restored files read-only before owner checks.
Give each metadata verifier a separate writable output directory.
Use the matching source and documentation checkout.
Run verify-current.py, verify-owned.py, verify-documents.py,
verify-peer-replay.py and verify-prior-evidence.py from the restored area.

Five new modules contain 684 lines and eleven public theorems.
They cover actual rows/call heap effects on all outcomes, old pending-handle
preservation on every incoming outcome, inventory and old memo retention,
and conservative soundness of every actual returned fourth memo.
True excludes every satisfying term. False supplies no nonempty witness.
Full reached Context/Post and full physical readiness remain open.
The largest gap remains fixed-original-D recursive induction for BOTH workers.
The SAME captured sibling cache must hold at the ACTUAL after-hook Caller/query.
Prepared endpoint None supplies no hidden outer Caller certificate.
All {seal['owners']} owner bundles and all retained provider closures remain.
The historical 40-owner, 26-file peer input remains exact and immutable.
Any later sound-source or future-source supplement remains a separate snapshot.
The complete previous R20 archive remains in Git with all 36 complete owners.
prior-evidence.json pins all five archive files and its 4473 regular payloads.
Production evidence has 18 commands: 16 passes, 2 failed drafts, and 90 input snapshots.
The separate frozen isolated probe preserves 13 commands and 103 snapshots.
All actual Lean commands use verified serial 4 GiB memory.max/high, zero swap, and a timeout of five minutes.
Audit passes 4806 jobs and 83739 theorem dependencies. Public checks: 1332 declarations, 159 definitions, and 11 standard axiom reports.
The full 5,120,002-byte readback retains both previous exact prefixes.
All 602 prior protected sources and 835 native inputs remain exact.
Only Audit's five added imports change an old Lean file.
No Haskell source changed. No Haskell or native product program ran.
No new Haskell defect or fix was established. Keep later Haskell fixes in FINDINGS.

---

"""
(DEST/'README.md').write_text(readme+(ROOT/'lean/notes-current-call-effects-and-retained-memos.md').read_text());print(json.dumps({'payloads':len(rows),'raw_bytes':sum(a['bytes'] for a in rows),'archive_bytes':manifest['archive_bytes'],'archive_sha256':manifest['archive_sha256']}))
