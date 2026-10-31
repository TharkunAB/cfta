from pathlib import Path
import hashlib,json,shutil,tarfile

ROOT=Path('/home/tritlo/Code/mcfta')
AREA=Path('/tmp/mcfta-literal-minimum-control-20261031')
DEST=ROOT/'lean/restart-evidence/20261031-literal-minimum-control'
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
(DEST/'README.md').write_text(f"""# Signed minimum pass and convergence: restart evidence

Source `{seal['source_head']}`. Documentation `{seal['docs_head']}`.
The complete original-input objective remains open. Work continues.
All {len(rows)} regular payloads remain without filtering.
Raw bytes: {sum(a['bytes'] for a in rows)}. Compressed bytes: {manifest['archive_bytes']}.
SHA256: `{manifest['archive_sha256']}`.

Verify or reconstruct from the repository root:

```sh
python3 lean/restart-evidence/20261031-literal-minimum-control/verify.py lean/restart-evidence/20261031-literal-minimum-control --extract /tmp/mcfta-literal-minimum-restored-20261031
```

Use a fresh destination. Omit --extract to verify only.
The verifier rejects duplicate, missing, extra, unsafe and non-regular members.
It executes no Lean or Haskell. Make restored files read-only before owner checks.
Give each metadata verifier a separate writable output directory.
Current checks require the matching source and documentation checkout.
Run verify-current.py, verify-owned.py, verify-documents.py and
verify-peer-replay.py from the restored area with separate result folders.

Two checked modules model the actual ordered signed minimum pass and a total
positive pass fixed-point computation from internally empty initialization.
All rows at one key read the same suffix-updated table before one min insertion.
The finite-key comparison and natural lexicographic decrease are derived inside
the producer. No future result, count or invariant is supplied as an input.
The original Input.complete covers every value of Q. The source Map key-domain,
container and scan-order adapter and guard-erased structural minimum semantics
remain open. No constrained-language attained minimum is claimed.

Audit default/strict passes 4773 jobs/83303 theorem dependency checks.
Public passes 1258 checks/148 definition prints; all seven new reports use only
propext and Quot.sound. The complete old 4961279 public bytes are an exact prefix.
Root and independent review cover final 417 source lines and the complete
125-line public tail. All 10 compiler attempts/23 snapshots remain: nine passes,
one failed attempt before proof repair. All dispatched jobs had verified
4 GiB memory/high, zero swap and five-minute time caps.
All 572 prior protected sources and 835 native inputs remain exact.

Actual source Map correspondence and computed Int/Nat embedding, literal source
reachable/trim/SCC/memo/native semantic import, sufficient original worker depth,
accepted membership/configured order and intended public prefixes remain open.
Keep both workers, source contradictions and all original API/Haskell obligations.
The finite constraint/SCS path carrier is not a work/depth or forecast bound.
Source-only next drafts remain UNCOMPILED. No Haskell source changed and no
Haskell/native program ran. No new Haskell defect or fix was established.

---

"""+(ROOT/'lean/notes-current-literal-minimum-pass.md').read_text())
print(json.dumps({'payloads':len(rows),'raw_bytes':sum(a['bytes'] for a in rows),'archive_bytes':manifest['archive_bytes'],'archive_sha256':manifest['archive_sha256']}))
