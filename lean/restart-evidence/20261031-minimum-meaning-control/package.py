from pathlib import Path
import hashlib,json,shutil,tarfile

ROOT=Path('/home/tritlo/Code/mcfta')
AREA=Path('/tmp/mcfta-minimum-meaning-control-20261031')
DEST=ROOT/'lean/restart-evidence/20261031-minimum-meaning-control'
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
(DEST/'README.md').write_text(f"""# Structural minima and known handles: restart evidence

Source `{seal['source_head']}`. Documentation `{seal['docs_head']}`.
The complete original-input objective remains open. Work continues.
All {len(rows)} regular payloads remain without filtering.
Raw bytes: {sum(a['bytes'] for a in rows)}. Compressed bytes: {manifest['archive_bytes']}.
SHA256: `{manifest['archive_sha256']}`.

Verify or reconstruct from the repository root:

```sh
python3 lean/restart-evidence/20261031-minimum-meaning-control/verify.py lean/restart-evidence/20261031-minimum-meaning-control --extract /tmp/mcfta-minimum-meaning-restored-20261031
```

Use a fresh destination. Omit --extract to verify only.
The verifier rejects duplicate, missing, extra, unsafe and non-regular members.
It executes no Lean or Haskell. Make restored files read-only before owner checks.
Give each metadata verifier a separate writable output directory.
Current checks require the matching source and documentation checkout.
Run verify-current.py, verify-owned.py, verify-documents.py and
verify-peer-replay.py from the restored area with separate result folders.

Five new modules and one append-only extension prove actual finite-pass
reachability, exact minimum node counts for the EXISTING finite guard-erased
language, computed Int/Nat embedding and actual bounded startup, and preservation
of known ordinary handles/height through callback frames and actual native effects.
The query factory derives its actual completed receipt from current resource gates.
It preserves the SAME old cache; it does not classify newly returned handles.
No future result, iteration count, trace, range or global invariant is supplied.
All original cache/row/pending/filter/width/bound gates remain explicit.

Audit default/strict passes 4778 jobs/83357 theorem dependency checks.
Public passes 1276 checks/151 definition prints; all 18 new reports are standard-only.
The complete old 4969828 public bytes are an exact prefix.
Root covers final 844 source lines and the complete 363-line/27235B public tail.
All 26 compiler attempts/120 snapshots remain: 23 passes and 3 repaired failures.
All dispatched jobs had effective 4 GiB memory/high, zero swap and five-minute caps.
Of 574 prior protected sources, 573 retain exact bytes; the remaining convergence
source retains its complete original 196-line body as an exact byte prefix.
Its append adds no changes to old declarations, headers or proofs.
All 835 native inputs remain exact.

Original Map/domain/order and full signed equality-filter source adapters remain
open. New child/assigned/query handle domain+height, arbitrary configured-fuel raw
query endpoints, sufficient original nested-call depth, accepted membership,
configured order, intended public prefix and Haskell/native correspondence remain
open. Retain both workers, terminal/alias work, source contradictions and captured
sibling restoration. No attained constrained-language minimum is claimed.
Source-only next drafts remain UNCOMPILED. No Haskell source changed and no
Haskell/native product ran. No new Haskell defect or fix was established.

---

"""+(ROOT/'lean/notes-current-minimum-meaning-and-known-nodes.md').read_text())
print(json.dumps({'payloads':len(rows),'raw_bytes':sum(a['bytes'] for a in rows),'archive_bytes':manifest['archive_bytes'],'archive_sha256':manifest['archive_sha256']}))
