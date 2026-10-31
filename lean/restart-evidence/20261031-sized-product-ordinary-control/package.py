from pathlib import Path
import hashlib,json,shutil,tarfile

ROOT=Path('/home/tritlo/Code/mcfta')
AREA=Path('/tmp/mcfta-sized-product-ordinary-control-20261031')
DEST=ROOT/'lean/restart-evidence/20261031-sized-product-ordinary-control'
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
(DEST/'README.md').write_text(f"""# Size-product native construction: restart evidence

Source `{seal['source_head']}`. Documentation `{seal['docs_head']}`.
The complete original-input objective remains open. Work continues.
All {len(rows)} regular payloads remain without filtering.
Raw bytes: {sum(a['bytes'] for a in rows)}. Compressed bytes: {manifest['archive_bytes']}.
SHA256: `{manifest['archive_sha256']}`.

Verify or reconstruct from the repository root:

```sh
python3 lean/restart-evidence/20261031-sized-product-ordinary-control/verify.py lean/restart-evidence/20261031-sized-product-ordinary-control --extract /tmp/mcfta-sized-product-ordinary-restored-20261031
```

Use a fresh destination. Omit --extract to verify only.
The verifier rejects duplicate, missing, extra, unsafe and non-regular members.
It executes no Lean or Haskell. Make restored files read-only before owner checks.
Give each metadata verifier a separate writable output directory.
Current checks require the matching source and documentation checkout.
Run verify-current.py, verify-owned.py, verify-documents.py and
verify-peer-replay.py from the restored area, with separate result folders.

Four checked modules derive original size-product rank decrease, ordered
Integer/Nat split equality under an embedded table, actual ordinary constructor
completion and height at most bound.toNat+1 for the bounded product.
The original minimum table and filter are still inputs. The construction unfolds
ranked rows. Literal SCC/memo import and final native row-list order stay open.

All 26 compiler attempts and 82 snapshots remain: 15 passes and 11 repaired failures.
The separate before-dispatch bus failure remains. All dispatched checks used
verified 4 GiB memory/high, zero swap and five-minute time caps. Full Audit 4769/83193 and
public 1245/129 pass. All 14 new axiom reports use only standard axioms.
The old 4938741 public bytes remain an exact prefix. Root and independent review
cover final 678 source lines and the complete 196-line new public tail.
Large failed diagnostics retain all raw bytes, exact-line dictionaries and
replay/reconstruction checks. This is not a raw full-line peer-read claim.
All 566 old protected sources and 835 native inputs remain exact.

Actual source minimum/filter/exploration/SCC/memo/native correspondence,
sufficient original worker depth, global progress and intended accepted public
prefix membership/coverage/order remain open. Keep both workers and the complete
Prefix/table/count/checkpoint/adapter/Haskell obligations. Keep generic recursive,
union and opaque-field inputs in scope. Source-only next drafts remain UNCOMPILED.
No Haskell source changed, no Haskell/native program ran, and no new executable
Haskell defect or fix was established.

---

"""+(ROOT/'lean/notes-current-sized-product-ordinary.md').read_text())
print(json.dumps({'payloads':len(rows),'raw_bytes':sum(a['bytes'] for a in rows),'archive_bytes':manifest['archive_bytes'],'archive_sha256':manifest['archive_sha256']}))
