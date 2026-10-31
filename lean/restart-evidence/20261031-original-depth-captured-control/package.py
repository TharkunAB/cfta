from pathlib import Path
import hashlib,json,shutil,tarfile

ROOT=Path('/home/tritlo/Code/mcfta')
AREA=Path('/tmp/mcfta-original-depth-and-captured-control-20261031')
DEST=ROOT/'lean/restart-evidence/20261031-original-depth-captured-control'
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
(DEST/'README.md').write_text(f"""# Original size-rank inventory and captured edges: restart evidence

Captured-edge source `{seal['source_head']}`. Documentation `{seal['docs_head']}`.
The complete original-input objective remains incomplete. Work continues.
All {len(rows)} regular payloads remain without filtering.
Raw bytes: {sum(a['bytes'] for a in rows)}. Compressed bytes: {manifest['archive_bytes']}.
SHA256: `{manifest['archive_sha256']}`.

Verify or reconstruct from the repository root:

```sh
python3 lean/restart-evidence/20261031-original-depth-captured-control/verify.py lean/restart-evidence/20261031-original-depth-captured-control --extract /tmp/mcfta-original-depth-captured-restored-20261031
```

Use a fresh destination. Omit --extract to verify only.
The verifier rejects duplicate, missing, extra, unsafe and non-regular members.
It executes no Lean or Haskell. Make restored files read-only before owner
checks. Give each metadata verifier a separate writable output directory.
Current checks require the matching source and documentation checkout.

Eight compiler commands completed: six passed, two failed before repair.
All 13 snapshots remain. CapturedEdge derives parent admission from its actual
pending slot and preserves conditional native Stored at exposed callers.
None and unhandled give True and establish no hidden-state property.
Root and peer read all 108 source lines and 63 public lines.
Audit4765/83090 and public1231/118 pass. New axioms are standard.
All earlier public output and root documents remain complete exact prefixes
or suffixes. All current original-input and resource gates remain explicit.

The finite carrier bounds constraint/SCS and projected equality paths.
Numeric forecast magnitudes can depend on supplied recursive depth.
It does not bound term depth, recursion, or whole work traces.
The size-reference contracts are distinct from cross-depth operational output
inclusion. The actual positive-size product is the next construction route.
Complete source inventories, independent reviews, private providers and
metadata/correction records remain without filtering.

A complete157L numeric product-rank V2 is retained UNCOMPILED.
The proposed46L native construction header is UNIMPLEMENTED and UNELABORATED.
Actual Integer/minimum/filter/reachable/SCC/native transport, global progress,
intended ordered public prefix production and Haskell correspondence remain
open. The full goal also retains generic Mu/Union/opaque-field sources.
No Haskell source changed, no Haskell/native program ran, and no new executable
issue or fix was established. The custom-cost candidate is an existing
source-review progress limit, not a current executed nontermination result.

---

"""+(ROOT/'lean/notes-current-original-depth-and-captured.md').read_text())
print(json.dumps({'payloads':len(rows),'raw_bytes':sum(a['bytes'] for a in rows),'archive_bytes':manifest['archive_bytes'],'archive_sha256':manifest['archive_sha256']}))
