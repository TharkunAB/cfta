from pathlib import Path
import hashlib,json,shutil,tarfile

ROOT=Path('/home/tritlo/Code/mcfta')
AREA=Path('/tmp/mcfta-sized-source-filter-admission-control-20261031')
DEST=ROOT/'lean/restart-evidence/20261031-sized-source-filter-admission-control'
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
(DEST/'README.md').write_text(f"""# Concrete filter and product startup: restart evidence

Source `{seal['source_head']}`. Documentation `{seal['docs_head']}`.
The complete original-input objective remains open. Work continues.
All {len(rows)} regular payloads remain without filtering.
Raw bytes: {sum(a['bytes'] for a in rows)}. Compressed bytes: {manifest['archive_bytes']}.
SHA256: `{manifest['archive_sha256']}`.

Verify or reconstruct from the repository root:

```sh
python3 lean/restart-evidence/20261031-sized-source-filter-admission-control/verify.py lean/restart-evidence/20261031-sized-source-filter-admission-control --extract /tmp/mcfta-sized-source-filter-admission-restored-20261031
```

Use a fresh destination. Omit --extract to verify only.
The verifier rejects duplicate, missing, extra, unsafe and non-regular members.
It executes no Lean or Haskell. Make restored files read-only before owner checks.
Give each metadata verifier a separate writable output directory.
Current checks require the matching source and documentation checkout.
Run verify-current.py, verify-owned.py, verify-documents.py and
verify-peer-replay.py from the restored area with separate result folders.

Two checked modules model the signed-view numeric equality filter, preserve
exact ordered Integer/Nat filtered splits and derive the actual same-root
bounded product startup Packet, initial Fits and physical guard Heap.
Original cache validity, cached original-row equality payloads and empty pending
metadata are gates. Minima/filter remain model inputs. Initial Fits at a supplied
width does not produce sufficient global capacity or worker depth.

Audit default/strict passes 4771 jobs/83226 theorem dependency checks.
Public passes 1251 checks/135 definition prints; all six new reports are
standard-only. The complete old 4952782 public bytes are an exact prefix.
Root and independent review cover final 250 source lines and the complete
128-line public tail. All 11 compiler attempts/24 snapshots remain: nine passes,
two failed attempts before proof repair. All dispatched jobs had verified
4 GiB memory/high, zero swap and five-minute time caps.
All 570 prior protected sources and 835 native inputs remain exact.

Actual full-constraint equality projection, minimumSizes convergence and Map
adapters, literal reachable/trim/SCC/memo/native semantic import, sufficient
original worker depth/global progress and intended accepted public prefixes
remain open. Keep both workers and all original API/Haskell obligations.
Source-only next drafts remain UNCOMPILED. No Haskell source changed or
Haskell/native program ran. No new executable Haskell defect/fix was established.

---

"""+(ROOT/'lean/notes-current-sized-source-filter-and-initial.md').read_text())
print(json.dumps({'payloads':len(rows),'raw_bytes':sum(a['bytes'] for a in rows),'archive_bytes':manifest['archive_bytes'],'archive_sha256':manifest['archive_sha256']}))
