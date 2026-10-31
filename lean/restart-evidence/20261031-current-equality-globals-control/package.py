from pathlib import Path
import hashlib,json,shutil,tarfile
ROOT=Path('/home/tritlo/Code/mcfta');AREA=Path('/tmp/mcfta-current-equality-globals-control-20261031');DEST=ROOT/'lean/restart-evidence/20261031-current-equality-globals-control';DEST.mkdir(exist_ok=False);seal=json.loads((AREA/'FROZEN.json').read_text());assert seal['write_halt'] is True and seal['goal_turn']=='progress';expected={a['path']:a for a in seal['payloads']};paths=sorted(p for p in AREA.rglob('*') if p.is_file());assert {str(p.relative_to(AREA)) for p in paths}==set(expected)|{'FROZEN.json'};rows=[]
for p in paths:
 assert not p.is_symlink() and not p.stat().st_mode&0o222;b=p.read_bytes();row={'path':str(p.relative_to(AREA)),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
 if row['path']!='FROZEN.json':assert row==expected[row['path']]
 rows.append(row)
archive=DEST/'evidence.tar.gz'
with tarfile.open(archive,'w:gz',compresslevel=6) as target:
 for p in paths:target.add(p,arcname=str(p.relative_to(AREA)),recursive=False)
manifest={'archive':archive.name,'archive_bytes':archive.stat().st_size,'archive_sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),'source_commit':seal['source_head'],'docs_commit':seal['docs_head'],'payloads':rows};(DEST/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');shutil.copyfile(ROOT/'lean/restart-evidence/20261030-neutral-recording-control/verify.py',DEST/'verify.py');shutil.copyfile(__file__,DEST/'package.py')
readme=f"""# Actual row equality and global memo preservation: restart evidence

Source `{seal['source_head']}`. Documentation `{seal['docs_head']}`.
The full original-input objective remains open. Goal ACTIVE.
All {len(rows)} regular payloads remain without filtering.
Raw bytes: {sum(a['bytes'] for a in rows)}. Compressed bytes: {manifest['archive_bytes']}.
SHA256: `{manifest['archive_sha256']}`.

Verify or reconstruct from the repository root:

```sh
python3 lean/restart-evidence/20261031-current-equality-globals-control/verify.py lean/restart-evidence/20261031-current-equality-globals-control --extract /tmp/mcfta-current-equality-globals-restored-20261031
```

Use a fresh destination. Omit --extract to verify only.
The verifier rejects duplicate, missing, extra, unsafe and non-regular members.
It executes no Lean or Haskell. Make restored files read-only before owner checks.
Give each metadata verifier a separate writable output directory.
Use the matching source and documentation checkout.
Run verify-current.py, verify-owned.py, verify-documents.py,
verify-peer-replay.py and verify-prior-evidence.py from the restored area.

Three new modules have 304 lines and five public theorems.
Actual exposures produce full Effects/Ready and resident field loads on every outcome.
Actual rows preserve cache Valid/Grows and Fields on the INITIAL heap.
The same complete global memos remain Valid at every literal actual call endpoint.
The prior conservative returned-fourth and old pending-cache laws remain checked.
True excludes every satisfying term. False supplies no nonempty witness.
Full actual projection/requirements/tuple/rows/call readiness remains open.
Completed projection traces do not certify arbitrary failed prefixes.
Result-table Sound and MuProbe Clean also remain open.
The largest gap remains fixed-original-D actual induction for BOTH workers.
Restore the SAME captured sibling cache at the ACTUAL post-hook Caller/query pair.
Prepared endpoint None supplies no hidden outer Caller certificate.
All {seal['owners']} complete owner bundles and all retained provider closures remain.
The immutable historical47-owner public-review input remains exact.
Later future warm/probe candidates must stay separate from checked3/304.
Separate future bundles retain the original 198/63-line candidates and checked 206/64-line revisions.
Their five isolated strict commands retain two passes, three failures, and all 25 snapshots.
Those candidates are not installed in this three-module production checkpoint.
The complete previous R21 archive remains in Git with all 43 complete owners.
prior-evidence.json pins its five archive files and 10480 regular payloads.
Nine production commands pass and retain 32 input snapshots.
Separate probes retain the tuple failure/repair and first unchanged globals pass.
All actual Lean commands use verified serial 4 GiB memory.max/high, zero swap,
and a timeout of five minutes.
Audit passes 4809 jobs and 83773 dependencies. Public: 1337 checks, 159 definitions, and five standard reports.
The prior 5120002-byte readback remains an exact prefix of 5125851 bytes.
All 607 prior protected sources and 835 native inputs remain exact.
Only Audit's three added imports change an old Lean file.
No Haskell source changed. No Haskell or native product program ran.
No new Haskell defect or fix was established. Keep later Haskell fixes in FINDINGS.

---

"""
(DEST/'README.md').write_text(readme+(ROOT/'lean/notes-current-row-equality-and-global-memos.md').read_text());print(json.dumps({'payloads':len(rows),'raw_bytes':sum(a['bytes'] for a in rows),'archive_bytes':manifest['archive_bytes'],'archive_sha256':manifest['archive_sha256']}))
