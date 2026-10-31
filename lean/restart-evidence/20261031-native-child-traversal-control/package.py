from pathlib import Path
import hashlib,json,shutil,tarfile

ROOT=Path('/home/tritlo/Code/mcfta')
AREA=Path('/tmp/mcfta-native-child-traversal-control-20261031')
DEST=ROOT/'lean/restart-evidence/20261031-native-child-traversal-control'
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
(DEST/'README.md').write_text(f"""# Recursive traversal and continuation receipt count: restart evidence

Traversal source `{seal['traversal_source_head']}`.
Selected-edge source `{seal['selected_source_head']}`.
Count source `{seal['source_head']}`. Documentation `{seal['docs_head']}`.
The complete original-input objective remains incomplete. Work continues.
All {len(rows)} regular payloads remain without filtering.
Raw bytes: {sum(a['bytes'] for a in rows)}. Compressed bytes: {manifest['archive_bytes']}.
SHA256: `{manifest['archive_sha256']}`.

Verify or reconstruct from the repository root:

```sh
python3 lean/restart-evidence/20261031-native-child-traversal-control/verify.py lean/restart-evidence/20261031-native-child-traversal-control --extract /tmp/mcfta-native-child-traversal-restored-20261031
```

Use a fresh destination. Omit --extract to verify only.
The verifier rejects duplicate, missing, extra, unsafe and non-regular members.
It executes no Lean or Haskell. Make restored files read-only before owner
checks. Give each metadata verifier a separate writable output directory.
Current checks require the matching source and documentation checkout.

All fifteen compiler commands pass. All 42 input snapshots remain.
Actual ChildTraversal derives successor admission and retains native Stored
for complete and stopped callers. SelectedEdge derives its own-cache admission
and certifies exposed callers. Unhandled gives True, with no hidden-state fact.
Actual continuation complete receipts equal the supplied edge-list length;
stopped processed receipts are fewer. The stopping receipt is separate.
No future invariant, history or output-certificate supplier is added.
All current input and numeric reservation gates remain explicit.
Independent review reads all 328 source lines and 163 public lines.
All three new axiom reports use standard axioms. Full prior public output and
old root documents remain exact prefixes or suffixes respectively.
Complete owners/providers/drafts/provenance and metadata recoveries remain.
CapturedEdge108L remains UNCOMPILED future evidence, with the same hidden-state
limit. Sufficient ORIGINAL depth/resources, whole ordered coverage, public
adapters and Haskell correspondence remain open. No Haskell source changed,
no native command ran, and no new executable defect or fix was established.

---

"""+(ROOT/'lean/notes-current-native-child-traversal.md').read_text())
print(json.dumps({'payloads':len(rows),'raw_bytes':sum(a['bytes'] for a in rows),'archive_bytes':manifest['archive_bytes'],'archive_sha256':manifest['archive_sha256']}))
