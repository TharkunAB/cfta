"""Archive every sealed checkpoint file without changing the source area."""
from pathlib import Path
import hashlib
import json
import shutil
import tarfile

source = Path('/tmp/mcfta-prepared-history-semantics-20261028')
repo = Path('/home/tritlo/Code/mcfta')
destination = repo/'lean/restart-evidence/20261028-prepared-history-semantics'
destination.mkdir(parents=True, exist_ok=False)
seal = json.loads((source/'FROZEN.json').read_text())
assert seal['write_halt'] is True
expected = {r['path']: r for r in seal['payloads']}
assert len(expected) == len(seal['payloads'])
paths = sorted(p for p in source.rglob('*') if p.is_file())
assert {str(p.relative_to(source)) for p in paths} == set(expected)|{'FROZEN.json'}
records = []
for path in paths:
    assert not path.is_symlink()
    raw = path.read_bytes()
    record = {'path': str(path.relative_to(source)), 'bytes': len(raw),
              'sha256': hashlib.sha256(raw).hexdigest()}
    if record['path'] != 'FROZEN.json':
        assert record == expected[record['path']]
    records.append(record)
archive = destination/'evidence.tar.gz'
with tarfile.open(archive, 'w:gz', compresslevel=6) as tar:
    for path in paths:
        tar.add(path, arcname=str(path.relative_to(source)), recursive=False)
manifest = {'archive': archive.name, 'archive_bytes': archive.stat().st_size,
            'archive_sha256': hashlib.sha256(archive.read_bytes()).hexdigest(),
            'source_commit': seal['source_head'], 'docs_commit': seal['docs_head'],
            'payloads': records}
(destination/'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')
verifier = repo/'lean/restart-evidence/20261028-prepared-semantic-history-reboot/verify.py'
raw = verifier.read_text().replace('saved reboot evidence snapshot', 'complete sealed proof evidence snapshot')
(destination/'verify.py').write_text(raw)
readme = f'''# Prepared history semantic gates: complete checkpoint evidence

Source commit: `{seal['source_head']}`.
Documentation commit: `{seal['docs_head']}`.
Branch: `formalize`. The whole formalization goal remains open and active.

This archive contains every file in the sealed proof area. It includes all
failed drafts and full diagnostics, final strict-check inputs and reports,
complete public readback, exact old-prefix evidence, all 49 whole public block
reviews, the resolved documentation finding, preserved old document bodies,
source hashes, resource measurements, Git receipts and exact board readback.
The root `FROZEN.json` and three final owner seals identify the immutable inputs.
No file filter or cleanup was applied. The original temporary area is immutable.

The archive has {len(records):,} regular payload files and
{sum(r['bytes'] for r in records):,} uncompressed payload bytes.
`evidence.tar.gz` has {manifest['archive_bytes']:,} bytes and SHA-256
`{manifest['archive_sha256']}`.
`manifest.json` records every payload path, byte count and SHA-256 value.

From the repository root, verify and reconstruct the evidence with one command:

```sh
python3 lean/restart-evidence/20261028-prepared-history-semantics/verify.py lean/restart-evidence/20261028-prepared-history-semantics --extract /tmp/mcfta-prepared-history-semantics-restored
```

Use a fresh destination. Omit `--extract` to verify without reconstruction.
The verifier checks the complete compressed archive and all payload identities.
It rejects duplicate, missing, extra, unsafe and non-regular archive members.
It uses only Python's standard library. It does not invoke Lean or Haskell.
Keep the restored evidence immutable. Use a separate fresh area for later work.

All 30 new modules and Audit pass exact-source strict checks with Lean 4.34.1,
warningAsError and linter.all. The full Audit build passes with 4,463 jobs and
81,374 checked theorem dependencies. Public readback has 622 theorem signatures
with axiom checks and 58 definitions. The old 2,610,680-byte prefix is exact.
The only listed axioms are propext, Classical.choice and Quot.sound.
All 49 new public blocks received whole-block source review.

The checkpoint preserves all 4,432 old non-Audit Lean files, 281 stronger proof
sources, and 817 current Haskell/Cabal files. It preserves all ten older document
bodies exactly. No new Haskell defect or fix was established.
Ten compiler/build failures and one precompiler launch failure remain in the
evidence. All final compiler checks pass. A separate final-review metadata
attempt failed because 28 inherited stronger-source records omit optional byte
counts. The repaired checker retains those original records and checks every
recorded SHA-256, plus byte counts where present. That failed checker is retained.

Current claims and limits are in
`../../notes-current-prepared-history-semantics.md`. The finite producer preserves
canonical trie representation and actual resource histories. Local opaque
semantics, all-tag marker isolation, same-output discharged child retention,
full native Posts and selected preparation arity are checked. Backward arity
still assumes a reached arity certificate. Global stable opaque history evidence,
forward whole-driver arity, whole-history backward semantics, the public
rendering/discharge connection, accepted-output coverage, sufficient recursive
depth, full public APIs and physical Haskell correspondence remain open.

The archived `root-progress-final.json` supersedes earlier progress reports.
Archived Git state was captured before this archive's publication commit.
Use the final branch tip and Git remote readback for publication state.
The earlier reboot archive remains unchanged.
'''
(destination/'README.md').write_text(readme)
shutil.copy2(Path(__file__), destination/'package.py')
print(json.dumps({k: v for k, v in manifest.items() if k != 'payloads'}|
                 {'payloads': len(records), 'raw_bytes': sum(r['bytes'] for r in records)}))
